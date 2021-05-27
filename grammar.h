/**
 * grammar.h
 *
 *  Created on: Jul 15, 2015
 *      Author: asaparov
 */

#ifndef GRAMMAR_H_
#define GRAMMAR_H_

#include <math.h>
#include <limits>
#include <core/array.h>
#include <core/map.h>
#include <core/io.h>
#include <core/utility.h>
#include <math/features.h>

#define NEW_TERMINAL (UINT_MAX - 3)

using namespace core;

/* forward declarations */

template<typename Semantics> struct syntax_node;


template<typename T>
struct weighted {
	T object;
	double log_probability;

	static inline void swap(weighted<T>& first, weighted<T>& second) {
		core::swap(first.object, second.object);
		core::swap(first.log_probability, second.log_probability);
	}

	static inline void move(const weighted<T>& src, weighted<T>& dst) {
		core::move(src.object, dst.object);
		dst.log_probability = src.log_probability;
	}

	static inline void free(weighted<T>& form) {
		core::free(form.object);
	}
};

template<typename T>
inline bool operator < (
		const weighted<T>& first,
		const weighted<T>& second)
{
	/* we want to sort in descending order */
	return first.log_probability > second.log_probability;
}

template<typename Semantics>
struct transformation {
	typedef typename Semantics::function function;

	function* functions;
	unsigned int function_count;

	static inline unsigned int hash(const transformation<Semantics>& t) {
		unsigned int hash_value = default_hash(t.function_count);
		for (unsigned int i = 0; i < t.function_count; i++)
			hash_value ^= hasher<function>::hash(t.functions[i]);
		return hash_value;
	}

	static inline void free(transformation<Semantics>& t) {
		core::free(t.functions);
	}
};

template<typename Semantics>
inline bool init(transformation<Semantics>& t, const transformation<Semantics>& src) {
	typedef typename Semantics::function function;
	t.function_count = src.function_count;
	t.functions = (function*) malloc(max((size_t) 1, sizeof(function) * src.function_count));
	if (t.functions == nullptr) {
		fprintf(stderr, "init ERROR: Insufficient memory for `transformation.functions`.\n");
		return false;
	}
	for (unsigned int i = 0; i < src.function_count; i++)
		t.functions[i] = src.functions[i];
	return true;
}

template<typename Semantics>
inline bool operator != (
	const transformation<Semantics>& first,
	const transformation<Semantics>& second)
{
	if (first.function_count != second.function_count) return true;
	for (unsigned int i = 0; i < first.function_count; i++)
		if (first.functions[i] != second.functions[i]) return true;
	return false;
}

template<typename Semantics>
inline bool operator < (
	const transformation<Semantics>& first,
	const transformation<Semantics>& second)
{
	if (first.function_count < second.function_count) return true;
	else if (first.function_count > second.function_count) return false;
	for (unsigned int i = 0; i < first.function_count; i++) {
		if (first.functions[i] < second.functions[i]) return true;
		else if (second.functions[i] < first.functions[i]) return false;
	}
	return false;
}

template<typename Semantics, typename Stream>
inline bool read(transformation<Semantics>& t, Stream& in) {
	typedef typename Semantics::function function;
	if (!read(t.function_count, in)) return false;
	t.functions = (function*) malloc(max((size_t) 1, sizeof(function) * t.function_count));
	if (t.functions == nullptr) return false;
	if (!Semantics::read(t.functions, in, t.function_count)) {
		free(t.functions);
		return false;
	}
	return true;
}

template<typename Semantics, typename Stream>
inline bool write(const transformation<Semantics>& t, Stream& out) {
	return write(t.function_count, out)
		&& Semantics::write(t.functions, out, t.function_count);
}

template<typename Semantics, typename Stream>
inline bool print(const transformation<Semantics>& t, Stream& out) {
	if (t.function_count == 0) return true;
	if (!Semantics::print(t.functions[0], out)) return false;
	for (unsigned int i = 1; i < t.function_count; i++) {
		if (!print(',', out) || !Semantics::print(t.functions[i], out)) return false;
	}
	return true;
}

template<typename Semantics>
inline bool apply(
	const transformation<Semantics>& t,
	const Semantics& src, Semantics& out)
{
	if (!apply(t.functions[0], src, out)) return false;
	Semantics& temp = *((Semantics*) alloca(sizeof(Semantics)));
	for (unsigned int i = 1; i < t.function_count; i++) {
		swap(out, temp);
		if (!apply(t.functions[i], temp, out)) {
			free(temp);
			return false;
		}
		free(temp);
	}
	return true;
}

template<typename Semantics>
inline bool invert(
	Semantics*& inverse, unsigned int& inverse_count,
	const transformation<Semantics>& t,
	const Semantics& first, const Semantics& second)
{
	/* apply the function forward first */
	Semantics* outputs = (Semantics*) malloc(max((size_t) 1, sizeof(Semantics) * t.function_count));
	if (outputs == nullptr) {
		fprintf(stderr, "invert ERROR: Out of memory.\n");
		return false;
	}
	outputs[0] = first;
	for (unsigned int i = 1; i < t.function_count; i++) {
		if (!apply(t.functions[i - 1], outputs[i - 1], outputs[i])) {
			for (unsigned int k = 0; k < i; k++) free(outputs[k]);
			free(outputs); return false;
		}
	}

	unsigned int count;
	array<Semantics>& old_inverse = *((array<Semantics>*) alloca(sizeof(array<Semantics>)));
	if (!invert(old_inverse.data, count, t.functions[t.function_count - 1], outputs[t.function_count - 1], second)) {
		for (unsigned int k = 0; k < t.function_count; k++) free(outputs[k]);
		free(outputs); return false;
	}
	old_inverse.length = count;
	old_inverse.capacity = count;
	for (unsigned int i = t.function_count - 1; i > 0; i--)
	{
		array<Semantics> new_inverse(1 << (core::log2(old_inverse.length) + 1));
		for (unsigned int j = 0; j < old_inverse.length; j++) {
			Semantics* next_inverse; unsigned int next_inverse_count;
			if (!invert(next_inverse, next_inverse_count, t.functions[i - 1], outputs[i - 1], old_inverse[j])) {
				continue;
			} else if (!new_inverse.ensure_capacity(new_inverse.length + next_inverse_count)) {
				for (unsigned int k = 0; k < new_inverse.length; k++) free(new_inverse[k]);
				for (unsigned int k = 0; k < old_inverse.length; k++) free(old_inverse[k]);
				for (unsigned int k = 0; k < t.function_count; k++) free(outputs[k]);
				for (unsigned int k = 0; k < next_inverse_count; k++) free(next_inverse[k]);
				free(outputs); free(old_inverse); free(next_inverse); return false;
			}
			for (unsigned int k = 0; k < next_inverse_count; k++) {
				new_inverse[new_inverse.length++] = next_inverse[k];
				free(next_inverse[k]);
			}
			free(next_inverse);
		}

		for (unsigned int k = 0; k < old_inverse.length; k++) free(old_inverse[k]);
		swap(old_inverse, new_inverse);
	}

	for (unsigned int k = 0; k < t.function_count; k++) free(outputs[k]);
	free(outputs);
	if (old_inverse.length == 0) {
		free(old_inverse);
		return false;
	}

	resize(old_inverse.data, old_inverse.length);
	inverse = old_inverse.data;
	inverse_count = old_inverse.length;
	return true;
}

enum class rule_type : uint_fast8_t {
	EMPTY = 0,
	NONTERMINAL,
	TERMINAL
};

template<typename Stream>
inline bool read(rule_type& type, Stream& in) {
	uint8_t v;
	if (!read(v, in)) return false;
	type = (rule_type) v;
	return true;
}

template<typename Stream>
inline bool write(const rule_type& type, Stream& out) {
	return write((uint8_t) type, out);
}

template<typename Semantics>
struct nonterminal_rule {
	unsigned int* nonterminals;
	transformation<Semantics>* transformations;
	unsigned int length;

	static inline void move(const nonterminal_rule<Semantics>& src, nonterminal_rule<Semantics>& dst) {
		dst.nonterminals = src.nonterminals;
		dst.transformations = src.transformations;
		dst.length = src.length;
	}

	static inline unsigned int hash(const nonterminal_rule<Semantics>& rule) {
		unsigned int hash = default_hash(rule.nonterminals, rule.length);
		for (unsigned int i = 0; i < rule.length; i++)
			hash ^= hasher<transformation<Semantics>>::hash(rule.transformations[i]);
		return hash;
	}

	static inline void free(nonterminal_rule<Semantics>& rule) {
		core::free(rule.nonterminals);
		for (unsigned int i = 0; i < rule.length; i++)
			core::free(rule.transformations[i]);
		core::free(rule.transformations);
	}
};

template<typename Semantics>
inline bool init(nonterminal_rule<Semantics>& rule, const nonterminal_rule<Semantics>& src) {
	rule.length = src.length;
	rule.nonterminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * src.length));
	if (rule.nonterminals == nullptr) {
		fprintf(stderr, "init ERROR: Insufficient memory for `nonterminal_rule.nonterminals`.\n");
		return false;
	}

	for (unsigned int i = 0; i < src.length; i++)
		rule.nonterminals[i] = src.nonterminals[i];
	rule.transformations = (transformation<Semantics>*) malloc(
			max((size_t) 1, sizeof(transformation<Semantics>) * src.length));
	if (rule.transformations == nullptr) {
		fprintf(stderr, "init ERROR: Insufficient memory for `nonterminal_rule.transformations`.\n");
		core::free(rule.nonterminals); return false;
	}
	for (unsigned int i = 0; i < src.length; i++) {
		if (!init(rule.transformations[i], src.transformations[i])) {
			fprintf(stderr, "init ERROR: Insufficient memory for `nonterminal_rule.transformations[%u]`.\n", i);
			for (unsigned int j = 0; j < i; j++) core::free(rule.transformations[j]);
			core::free(rule.transformations); core::free(rule.nonterminals);
			return false;
		}
	}
	return true;
}

template<typename Semantics>
inline bool operator == (const nonterminal_rule<Semantics>& first, const nonterminal_rule<Semantics>& second) {
	if (first.nonterminals == nullptr || first.length != second.length)
		return false;

	/* compare nonterminal list */
	for (unsigned int i = 0; i < first.length; i++)
		if (first.nonterminals[i] != second.nonterminals[i]) return false;

	/* compare transformation functions */
	for (unsigned int i = 0; i < first.length; i++)
		if (first.transformations[i] != second.transformations[i]) return false;
	return true;
}

template<typename Semantics>
inline bool operator < (const nonterminal_rule<Semantics>& first, const nonterminal_rule<Semantics>& second) {
	if (first.length < second.length) return true;
	else if (first.length > second.length) return false;

	/* compare the nonterminal list */
	for (unsigned int i = 0; i < first.length; i++) {
		if (first.nonterminals[i] < second.nonterminals[i]) return true;
		else if (first.nonterminals[i] > second.nonterminals[i]) return false;
	}

	/* compare the transformation functions */
	for (unsigned int i = 0; i < first.length; i++) {
		if (first.transformations[i] < second.transformations[i]) return true;
		else if (second.transformations[i] < first.transformations[i]) return false;
	}
	return false;
}

template<typename Semantics, typename Stream, typename Printer>
inline bool print(const nonterminal_rule<Semantics>& r, Stream& out, Printer& printer) {
	if (!print('(', out)) return false;
	for (unsigned int i = 0; i < r.length; i++) {
		if (i > 0 && !print(' ', out)) return false;
		if (!print(r.nonterminals[i], out, printer) || !print(':', out) || !print(r.transformations[i], out))
			return false;
	}
	return print(')', out);
}

template<typename Semantics, typename Stream>
inline bool read(nonterminal_rule<Semantics>& r, Stream& in, hash_map<string, unsigned int>& token_map) {
	if (!read(r.length, in))
		return false;
	r.nonterminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * r.length));
	if (r.nonterminals == nullptr) {
		fprintf(stderr, "read ERROR: Insufficient memory for `nonterminal_rule.nonterminals`.\n");
		return false;
	} if (!read(r.nonterminals, in, r.length)) {
		core::free(r.nonterminals);
		return false;
	}

	r.transformations = (transformation<Semantics>*) malloc(
			max((size_t) 1, sizeof(transformation<Semantics>) * r.length));
	if (r.transformations == nullptr) {
		fprintf(stderr, "read ERROR: Insufficient memory for `nonterminal_rule.transformations`.\n");
		core::free(r.nonterminals); return false;
	} if (!read(r.transformations, in, r.length)) {
		core::free(r.nonterminals); core::free(r.transformations);
		return false;
	}
	return true;
}

template<typename Semantics, typename Stream>
inline bool write(const nonterminal_rule<Semantics>& r, Stream& out, const string** token_map) {
	return write(r.length, out)
		&& write(r.nonterminals, out, r.length)
		&& write(r.transformations, out, r.length);
}

struct terminal_rule {
	unsigned int* terminals;
	unsigned int length;
	unsigned int* inflected;
	unsigned int inflected_length;

	static inline unsigned int hash(const terminal_rule& rule) {
		unsigned int hash = default_hash(rule.terminals, rule.length);
		if (rule.inflected != nullptr)
			hash ^= default_hash(rule.inflected, rule.inflected_length);
		return hash;
	}

	static inline void move(const terminal_rule& src, terminal_rule& dst) {
		dst.terminals = src.terminals;
		dst.length = src.length;
		dst.inflected = src.inflected;
		dst.inflected_length = src.inflected_length;
	}

	static inline void free(terminal_rule& rule) {
		core::free(rule.terminals);
		if (rule.inflected != nullptr)
			core::free(rule.inflected);
	}
};

inline bool init(terminal_rule& rule, const terminal_rule& src) {
	rule.length = src.length;
	rule.inflected_length = src.inflected_length;
	rule.terminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * src.length));
	if (rule.terminals == nullptr) {
		fprintf(stderr, "init ERROR: Insufficient memory for `terminal_rule.terminals`.\n");
		return false;
	}

	for (unsigned int i = 0; i < src.length; i++)
		rule.terminals[i] = src.terminals[i];
	if (src.inflected == nullptr) {
		rule.inflected = nullptr;
	} else {
		rule.inflected = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * src.inflected_length));
		if (rule.inflected == nullptr) {
			fprintf(stderr, "init ERROR: Insufficient memory for `terminal_rule.inflected`.\n");
			free(rule.terminals); return false;
		}
		for (unsigned int i = 0; i < src.inflected_length; i++)
			rule.inflected[i] = src.inflected[i];
	}
	return true;
}

inline bool init(terminal_rule& rule, const sequence& terminal) {
	rule.length = terminal.length;
	rule.terminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * terminal.length));
	if (rule.terminals == NULL) {
		fprintf(stderr, "init ERROR: Insufficient memory for `terminal_rule.terminals`.\n");
		return false;
	}
	for (unsigned int i = 0; i < terminal.length; i++)
		rule.terminals[i] = terminal.tokens[i];
	rule.inflected = nullptr;
	rule.inflected_length = 0;
	return true;
}

inline bool operator == (const terminal_rule& first, const terminal_rule& second) {
	if (first.terminals == nullptr
	 || first.length != second.length
	 || first.inflected_length != second.inflected_length)
		return false;

	/* compare terminal list */
	for (unsigned int i = 0; i < first.length; i++)
		if (first.terminals[i] != second.terminals[i]) return false;

	/* compare inflected terminal list */
	if (first.inflected == nullptr) {
		if (second.inflected != nullptr) return false;
	} else {
		if (second.inflected == nullptr) return false;
		for (unsigned int i = 0; i < first.inflected_length; i++)
			if (first.inflected[i] != second.inflected[i]) return false;
	}
	return true;
}

inline bool operator < (const terminal_rule& first, const terminal_rule& second) {
	if (first.length < second.length) return true;
	else if (first.length > second.length) return false;
	else if (first.inflected_length < second.inflected_length) return true;
	else if (first.inflected_length > second.inflected_length) return false;

	/* first compare the terminals */
	for (unsigned int i = 0; i < first.length; i++) {
		if (first.terminals[i] < second.terminals[i]) return true;
		else if (first.terminals[i] > second.terminals[i]) return false;
	}

	/* compare inflected terminal list */
	if (first.inflected == nullptr) {
		if (second.inflected != nullptr) return true;
	} else {
		if (second.inflected == nullptr) return false;
		for (unsigned int i = 0; i < first.inflected_length; i++) {
			if (first.inflected[i] < second.inflected[i]) return true;
			else if (first.inflected[i] > second.inflected[i]) return false;
		}
	}
	return false;
}

template<typename Stream, typename Printer>
inline bool print(const terminal_rule& rule, Stream& out, Printer& printer) {

	if (!print('"', out) || !print(sequence(rule.terminals, rule.length), out, printer) || !print('"', out))
		return false;
	if (rule.inflected == nullptr) return true;
	return print("/\"", out) && print(sequence(rule.inflected, rule.inflected_length), out, printer) && print('"', out);
}

template<typename Stream>
inline bool read(terminal_rule& r, Stream& in, hash_map<string, unsigned int>& token_map) {

	if (!read(r.length, in))
		return false;
	r.terminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * r.length));
	if (r.terminals == nullptr) {
		fprintf(stderr, "read ERROR: Insufficient memory for `terminal_rule.terminals`.\n");
		return false;
	} if (!read(r.terminals, in, r.length)) {
		core::free(r.terminals);
		return false;
	}

	if (!read(r.inflected_length, in))
		return false;
	if (r.inflected_length == 0) {
		r.inflected = nullptr;
		return true;
	}

	r.inflected = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * r.inflected_length));
	if (r.inflected == nullptr) {
		fprintf(stderr, "read ERROR: Insufficient memory for `terminal_rule.inflected`.\n");
		return false;
	} if (!read(r.inflected, in, r.length)) {
		core::free(r.terminals); core::free(r.inflected);
		return false;
	}
	return true;
}

template<typename Stream>
inline bool write(const terminal_rule& r, Stream& out, const string** token_map) {
	if (!write(r.length, out) || !write(r.terminals, out, r.length) || !write(r.inflected_length, out))
		return false;
	if (r.inflected == nullptr)
		return true;
	else return write(r.inflected, out, r.inflected_length);
}

/* Represents a production rule in the semantic grammar. */
template<typename Semantics>
struct rule {
	rule_type type;
	union {
		nonterminal_rule<Semantics> nt;
		terminal_rule t;
	};

	rule(const rule<Semantics>& src) : type(src.type) {
		if (!initialize(src))
			exit(EXIT_FAILURE);
	}

	rule(const sequence& terminal) : type(rule_type::TERMINAL) {
		if (!initialize(terminal))
			exit(EXIT_FAILURE);
	}

	rule(const syntax_node<Semantics>* const* terminals, unsigned int terminal_count) : type(rule_type::TERMINAL)
	{
#if !defined(NDEBUG)
		if (terminal_count == 0)
			fprintf(stderr, "rule WARNING: `length` is zero.\n");
#endif

		t.length = 0;
		unsigned int total_length = 0;
		for (unsigned int i = 0; i < terminal_count; i++) {
#if !defined(NDEBUG)
			/* check if the children are terminal tokens */
			if (!terminals[i]->right.is_terminal())
				fprintf(stderr, "rule WARNING: This constructor should only be used with sequences of terminals.\n");
#endif
			total_length += terminals[i]->right.t.length;
		}

		t.terminals = (unsigned int*) malloc(sizeof(unsigned int) * total_length);
		if (t.terminals == nullptr) exit(EXIT_FAILURE);
		for (unsigned int i = 0; i < terminal_count; i++)
			for (unsigned int j = 0; j < terminals[i]->right.t.length; j++)
				t.terminals[t.length++] = terminals[i]->right.t.terminals[j];
		t.inflected = nullptr;
		t.inflected_length = 0;
	}

	~rule() { free(); }

	inline void operator = (const rule<Semantics>& src) {
		type = src.type;
		if (!initialize(src))
			exit(EXIT_FAILURE);
	}

	inline bool is_terminal() const {
		return type == rule_type::TERMINAL;
	}

	inline const sequence get_terminal() const {
		return sequence(t.terminals, t.length);
	}

	static inline unsigned int hash(const rule<Semantics>& rule) {
		/* TODO: precompute these and store them in a table for faster access */
		unsigned int type_hash = default_hash<rule_type, 4027360733>(rule.type);
		switch (rule.type) {
		case rule_type::TERMINAL:
			return type_hash ^ terminal_rule::hash(rule.t);
		case rule_type::NONTERMINAL:
			return type_hash ^ nonterminal_rule<Semantics>::hash(rule.nt);
		case rule_type::EMPTY: break;
		}
		fprintf(stderr, "rule.hash ERROR: Unrecognized rule_type.\n");
		exit(EXIT_FAILURE);
	}

	static inline void move(const rule<Semantics>& src, rule<Semantics>& dst) {
		dst.type = src.type;
		switch (src.type) {
		case rule_type::TERMINAL:
			core::move(src.t, dst.t); return;
		case rule_type::NONTERMINAL:
			core::move(src.nt, dst.nt); return;
		case rule_type::EMPTY: break;
		}
		fprintf(stderr, "rule.move ERROR: Unrecognized rule_type.\n");
		exit(EXIT_FAILURE);
	}

	static inline bool copy(const rule<Semantics>& src, rule<Semantics>& dst) {
		return init(dst, src);
	}

	static inline void swap(rule<Semantics>& first, rule<Semantics>& second) {
		char* first_data = (char*) &first;
		char* second_data = (char*) &second;
		for (unsigned int i = 0; i < sizeof(rule<Semantics>); i++)
			core::swap(first_data[i], second_data[i]);
	}

	static inline bool is_empty(const rule<Semantics>& rule) {
		return rule.type == rule_type::EMPTY;
	}

	static inline void set_empty(rule<Semantics>& rule) {
		rule.type = rule_type::EMPTY;
	}

	static inline void set_empty(rule<Semantics>* rules, unsigned int count) {
		memset(static_cast<void*>(rules), 0, sizeof(rule<Semantics>) * count);
	}

	static inline void free(rule<Semantics>& r) {
		r.free();
	}

private:
	bool initialize(const rule<Semantics>& src) {
		switch (src.type) {
		case rule_type::TERMINAL:
			return init(t, src.t);
		case rule_type::NONTERMINAL:
			return init(nt, src.nt);
		case rule_type::EMPTY: break;
		}
		fprintf(stderr, "rule.move ERROR: Unrecognized rule_type.\n");
		return false;
	}

	bool initialize(const sequence& terminal) {
		return init(t, terminal);
	}

	inline void free() {
		switch (type) {
		case rule_type::TERMINAL:
			core::free(t); return;
		case rule_type::NONTERMINAL:
			core::free(nt); return;
		case rule_type::EMPTY: break;
		}
		fprintf(stderr, "rule.free ERROR: Unrecognized rule_type.\n");
		exit(EXIT_FAILURE);
	}

	template<typename A> friend bool init(rule<A>&, const rule<A>&);
	template<typename A> friend bool init(rule<A>&, const sequence&);
};

template<typename Semantics>
inline bool init(rule<Semantics>& r, const rule<Semantics>& src) {
	r.type = src.type;
	return r.initialize(src);
}

template<typename Semantics>
inline bool init(rule<Semantics>& r, const sequence& terminal) {
	r.type = rule_type::TERMINAL;
	return r.initialize(terminal);
}

template<typename Semantics>
inline bool operator == (const rule<Semantics>& first, const rule<Semantics>& second) {
	if (first.type != second.type) return false;
	switch (first.type) {
	case rule_type::TERMINAL:
		return first.t == second.t;
	case rule_type::NONTERMINAL:
		return first.nt == second.nt;
	case rule_type::EMPTY: break;
	}
	fprintf(stderr, "operator == ERROR: Unrecognized rule_type.\n");
	exit(EXIT_FAILURE);
}

template<typename Semantics>
inline bool operator != (const rule<Semantics>& first, const rule<Semantics>& second) {
	return !(first == second);
}

template<typename Semantics>
inline bool operator < (const rule<Semantics>& first, const rule<Semantics>& second) {
	if (first.type < second.type) return true;
	else if (first.type > second.type) return false;
	switch (first.type) {
	case rule_type::TERMINAL:
		return first.t < second.t;
	case rule_type::NONTERMINAL:
		return first.nt < second.nt;
	case rule_type::EMPTY: break;
	}
	fprintf(stderr, "operator < ERROR: Unrecognized rule_type.\n");
	exit(EXIT_FAILURE);
}

template<typename Semantics, typename Stream, typename AtomPrinter, typename NonterminalPrinter>
inline bool print(const rule<Semantics>& r, Stream& out, pair<AtomPrinter&, NonterminalPrinter&> printers) {
	switch (r.type) {
	case rule_type::TERMINAL:
		return print(r.t, out, printers.key);
	case rule_type::NONTERMINAL:
		return print(r.nt, out, printers.value);
	case rule_type::EMPTY: break;
	}
	fprintf(stderr, "print ERROR: Unrecognized rule_type.\n");
	return false;
}

template<typename Semantics, typename Stream>
bool read(rule<Semantics>& r, Stream& stream, hash_map<string, unsigned int>& token_map)
{
	if (!read(r.type, stream)) return false;
	switch (r.type) {
	case rule_type::TERMINAL:
		return read(r.t, stream, token_map);
	case rule_type::NONTERMINAL:
		return read(r.nt, stream, token_map);
	case rule_type::EMPTY: break;
	}
	fprintf(stderr, "read ERROR: Unrecognized rule_type.\n");
	return false;
}

template<typename Semantics, typename Stream>
bool write(const rule<Semantics>& r, Stream& stream, const string** token_map)
{
	if (!write(r.type, stream)) return false;
	switch (r.type) {
	case rule_type::TERMINAL:
		return write(r.t, stream, token_map);
	case rule_type::NONTERMINAL:
		return write(r.nt, stream, token_map);
	case rule_type::EMPTY: break;
	}
	fprintf(stderr, "write ERROR: Unrecognized rule_type.\n");
	return false;
}

/* forward declarations */

template<bool DiscardImpossible, bool PruneAmbiguousLogicalForms,
		typename RuleDistribution, typename Semantics, typename StringMapType>
weighted<Semantics>* log_conditional(RuleDistribution&,
		const rule<Semantics>&, const Semantics&, const StringMapType& token_map, unsigned int&);

template<bool PruneUnobservedTerminals, typename RuleDistribution, typename Semantics, typename StringMapType>
weighted<sequence>* get_terminals(RuleDistribution&,
		const Semantics&, StringMapType&, unsigned int&);


/* TODO: i think it would be better if we didn't make a
   distinction between preterminals and "internal"
   nonterminals, and instead allow the user to make this
   distinction in the rule distribution if they so desire;
   it might make the parser cleaner */
template<typename Semantics, typename RuleDistribution>
struct nonterminal {
	typedef Semantics semantics_type;
	typedef RuleDistribution rule_distribution_type;

	string name;
	unsigned int id;
	RuleDistribution rule_distribution;

	inline RuleDistribution& get_rule_distribution() {
		return rule_distribution;
	}

	inline void on_resize() {
		rule_distribution.on_resize();
	}

	inline void clear() {
		rule_distribution.clear();
	}

	static inline void free(nonterminal<Semantics, RuleDistribution>& N) {
		core::free(N.name);
		core::free(N.rule_distribution);
	}
};

template<typename Semantics, typename RuleDistribution>
bool init(nonterminal<Semantics, RuleDistribution>& N,
		const string& name, unsigned int id)
{
	N.id = id;
	return init(N.name, name);
}

template<typename Semantics, typename RuleDistribution>
bool init(nonterminal<Semantics, RuleDistribution>& N,
	const nonterminal<Semantics, RuleDistribution>& src)
{
	N.id = src.id;
	if (!init(N.rule_distribution, src.rule_distribution)) {
		return false;
	} else if (!init(N.name, src.name)) {
		free(N.rule_distribution);
		return false;
	}
	return true;
}

template<typename Semantics, typename RuleDistribution>
inline bool copy(
	const nonterminal<Semantics, RuleDistribution>& src, 
	nonterminal<Semantics, RuleDistribution>& dst)
{
	dst.id = src.id;
	if (!copy(src.rule_distribution, dst.rule_distribution)) {
		return false;
	} else if (!copy(src.name, dst.name)) {
		free(dst.rule_distribution);
		return false;
	}
	return true;
}

template<typename Semantics, typename RuleDistribution,
	typename Stream, typename... Scribes,
	typename std::enable_if<is_readable<Stream>::value>::type* = nullptr>
bool read(nonterminal<Semantics, RuleDistribution>& N,
	Stream& stream, Scribes&&... scribes)
{
	if (!read(N.id, stream)
	 || !read(N.rule_distribution, stream, std::forward<Scribes>(scribes)...)) {
		return false;
	} else if (!read(N.name, stream)) {
		free(N.rule_distribution);
		return false;
	}
	return true;
}

template<typename Semantics, typename RuleDistribution,
	typename Stream, typename... Scribes,
	typename std::enable_if<is_writeable<Stream>::value>::type* = nullptr>
bool write(
	const nonterminal<Semantics, RuleDistribution>& N,
	Stream& stream, Scribes&&... scribes)
{
	return write(N.id, stream) && write(N.rule_distribution, stream, std::forward<Scribes>(scribes)...) && write(N.name, stream);
}

template<typename Semantics, typename Distribution>
inline void sample(nonterminal<Semantics, Distribution>& N) {
	sample(N.rule_distribution);
}

template<typename Semantics, typename RuleDistribution>
struct grammar
{
	array<nonterminal<Semantics, RuleDistribution>> nonterminals;
	hash_map<string, unsigned int> nonterminal_names;

	grammar() : nonterminals(16), nonterminal_names(16) { }

	~grammar() { free(); }

	inline void on_resize() {
		for (auto& nonterminal : nonterminals)
			nonterminal.on_resize();
	}

	inline void clear() {
		for (auto& nonterminal : nonterminals)
			nonterminal.clear();
	}

	bool compute_nonterminal_names() {
		bool contains; unsigned int index;
		if (!nonterminal_names.check_size(nonterminals.length))
			return false;
		for (const auto& N : nonterminals) {
			unsigned int& id = nonterminal_names.get(N.name, contains, index);
			if (contains) {
				fprintf(stderr, "grammar.compute_nonterminal_names ERROR: Nonterminal names must be unique.\n");
				return false;
			} else {
				if (!init(nonterminal_names.table.keys[index], N.name))
					return false;
				nonterminal_names.table.size++;
				id = N.id;
			}
		}
		return true;
	}

	static inline void free(grammar<Semantics, RuleDistribution>& G) {
		G.free();
		core::free(G.nonterminals);
		core::free(G.nonterminal_names);
	}

private:
	inline void free() {
		for (unsigned int i = 0; i < nonterminals.length; i++)
			core::free(nonterminals[i]);
		for (auto entry : nonterminal_names)
			core::free(entry.key);
	}
};

template<typename Semantics, typename RuleDistribution>
bool copy(const grammar<Semantics, RuleDistribution>& src, grammar<Semantics, RuleDistribution>& dst) {
	if (!array_init(dst.nonterminals, src.nonterminals.length)) {
		return false;
	} else if (!hash_map_init(dst.nonterminal_names, src.nonterminal_names.table.capacity)) {
		free(dst.nonterminals);
		return false;
	}
	for (unsigned int i = 0; i < src.nonterminals.length; i++) {
		if (!copy(src.nonterminals[i], dst.nonterminals[i])) {
			free(dst);
			return false;
		}
		dst.nonterminals.length++;
	}
	return dst.compute_nonterminal_names();
}

template<typename Semantics, typename RuleDistribution,
	typename Stream, typename... Scribes,
	typename std::enable_if<is_readable<Stream>::value>::type* = nullptr>
bool read(
	grammar<Semantics, RuleDistribution>& G,
	Stream& stream, Scribes&&... scribes)
{
	return hash_map_init(G.nonterminal_names, 64)
		&& read(G.nonterminals, stream, std::forward<Scribes>(scribes)...)
		&& G.compute_nonterminal_names();
}

template<typename Semantics, typename RuleDistribution,
	typename Stream, typename... Scribes,
	typename std::enable_if<is_writeable<Stream>::value>::type* = nullptr>
bool write(
	const grammar<Semantics, RuleDistribution>& G,
	Stream& stream, Scribes&&... scribes)
{
	return write(G.nonterminals, stream, std::forward<Scribes>(scribes)...);
}

template<typename Semantics, typename RuleDistribution>
inline void sample_grammar(grammar<Semantics, RuleDistribution>& G) {
	for (auto& nonterminal : G.nonterminals)
		sample(nonterminal);
}

template<typename Semantics>
struct syntax_node {
	/* if right_terminal.tokens != NULL, this is a
	   terminal node; otherwise, it's a nonterminal */
	rule<Semantics> right;
	syntax_node<Semantics>** children;

	unsigned int reference_count;

	syntax_node(const sequence& terminal) : right(terminal), children(NULL), reference_count(1) { }

	syntax_node(const syntax_node<Semantics>* const* terminals, unsigned int length) :
		right(terminals, length), children(NULL), reference_count(1)
	{ }

	syntax_node(const syntax_node<Semantics>& src) :
		right(src.right), reference_count(1)
	{
		if (!initialize(src))
			exit(EXIT_FAILURE);
	}

	syntax_node(const rule<Semantics>& r) : right(r), reference_count(1) {
		if (r.is_terminal()) {
			children = nullptr;
		} else {
			children = (syntax_node<Semantics>**) calloc(r.nt.length, sizeof(syntax_node<Semantics>*));
			if (children == NULL) {
				fprintf(stderr, "syntax_node ERROR: Insufficient memory for child node array.\n");
				exit(EXIT_FAILURE);
			}
		}
	}

	~syntax_node() { free(); }

	inline void operator = (const syntax_node<Semantics>& src) {
		right = src.right;
		if (!initialize(src))
			exit(EXIT_FAILURE);
		reference_count = 1;
	}

	inline bool is_terminal() const {
		return right.is_terminal();
	}

	inline bool is_valid(hash_map<const syntax_node<Semantics>*, unsigned int>& reference_counts) const {
		if (!reference_counts.check_size())
			return false;
		bool contains; unsigned int index;
		unsigned int& count = reference_counts.get(this, contains, index);
		if (!contains) {
			reference_counts.table.keys[index] = this;
			reference_counts.values[index] = 1;
			reference_counts.table.size++;
		} else count++;

		if (reference_count == 0) return false;
		if (is_terminal()) return true;
		for (unsigned int i = 0; i < right.length; i++) {
			if (children[i] != NULL && !children[i]->is_valid(reference_counts))
				return false;
		}
		return true;
	}

	inline bool check_reference_counts(
		const hash_map<const syntax_node<Semantics>*, unsigned int>& reference_counts,
		const hash_set<const syntax_node<Semantics>*>& invalid_children) const
	{
		bool contains;
		unsigned int expected = reference_counts.get(this, contains);
		if (!contains) return false;

		if (expected != reference_count) {
			fprintf(stderr, "syntax_node.check_reference_counts ERROR:"
				" Reference counter is invalid. Expected %u but counter "
				"is currently %u.\n", expected, reference_count);
			return false;
		}

		if (is_terminal()) return true;
		for (unsigned int i = 0; i < right.length; i++) {
			if (children[i] == NULL) continue;
			if (invalid_children.contains(children[i])
			 || !children[i]->check_reference_counts(reference_counts, invalid_children))
				return false;
		}
		return true;
	}

	static inline void move(const syntax_node<Semantics>& src, syntax_node<Semantics>& dst) {
		core::move(src.right, dst.right);
		core::move(src.children, dst.children);
		dst.reference_count = src.reference_count;
	}

	static inline void swap(syntax_node<Semantics>& first, syntax_node<Semantics>& second) {
		core::swap(first.right, second.right);
		core::swap(first.children, second.children);
		core::swap(first.reference_count, second.reference_count);
	}

	static inline bool is_empty(const syntax_node<Semantics>& key) {
		return key.reference_count == 0;
	}

	static inline unsigned int hash(const syntax_node<Semantics>& key) {
		unsigned int hash_value = rule<Semantics>::hash(key.right);
		if (key.is_terminal()) return hash_value;
		for (unsigned int i = 0; i < key.right.length; i++) {
			if (key.children[i] != NULL)
				hash_value ^= hash(*key.children[i]);
		}
		return hash_value;
	}

	static inline void free(syntax_node<Semantics>& node) {
		node.free();
		if (node.reference_count == 0)
			core::free(node.right);
	}

private:
	inline bool initialize(const syntax_node<Semantics>& src) {
		if (src.children == NULL) {
			children = NULL;
			return true;
		}
#if !defined(NDEBUG)
		if (src.right.is_terminal())
			fprintf(stderr, "syntax_node.initialize WARNING: `src.right` is a terminal rule.\n");
#endif
		children = (syntax_node<Semantics>**) malloc(sizeof(syntax_node<Semantics>*) * src.right.nt.length);
		if (children == NULL) {
			fprintf(stderr, "syntax_node.initialize ERROR: Out of memory.\n");
			core::free(right);
			return false;
		}
		for (unsigned int i = 0; i < src.right.nt.length; i++) {
			children[i] = src.children[i];
			if (children[i] != NULL)
				children[i]->reference_count++;
		}
		return true;
	}

	inline void free() {
		reference_count--;
		if (reference_count == 0) {
			if (children != NULL) {
				for (unsigned int i = 0; i < right.nt.length; i++) {
					if (children[i] != NULL) {
						core::free(*children[i]);
						if (children[i]->reference_count == 0)
							core::free(children[i]);
					}
				}
				core::free(children);
			}
		}
	}

	template<typename A> friend bool init(syntax_node<A>&, const rule<A>&);
	template<typename A> friend bool init(syntax_node<A>&, const syntax_node<A>&);
};

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node, const rule<Semantics>& rule)
{
	if (!init(node.right, rule))
		return false;
	if (rule.is_terminal()) {
		node.children = nullptr;
	} else {
		node.children = (syntax_node<Semantics>**) calloc(rule.nt.length, sizeof(syntax_node<Semantics>*));
		if (node.children == NULL) {
			fprintf(stderr, "init ERROR: Insufficient memory for child node array in syntax_node.\n");
			free(node.right); return false;
		}
	}
	node.reference_count = 1;
	return true;
}

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node, const sequence& terminal) {
	node.children = NULL;
	node.reference_count = 1;
	return init(node.right, terminal);
}

/* NOTE: this function assumes the given tokens are terminal symbols */
template<typename Semantics>
inline bool init(syntax_node<Semantics>& node,
		const syntax_node<Semantics>* const* terminals,
		unsigned int length)
{
	if (!init(node.right, length))
		return false;
	node.children = NULL;
	node.reference_count = 1;
	return node.initialize(terminals, length);
}

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node,
		const syntax_node<Semantics>& src)
{
	node.reference_count = 1;
	if (!init(node.right, src.right))
		return false;
	else if (!node.initialize(src)) {
		free(node.right);
		return false;
	}
	return true;
}

template<typename Semantics>
inline bool operator == (const syntax_node<Semantics>& first, const syntax_node<Semantics>& second) {
	if (first.right != second.right)
		return false;
	if (!first.right.is_terminal()) {
		for (unsigned int i = 0; i < first.right.length; i++)
			if (*first.children[i] != *second.children[i])
				return false;
	}
	return true;
}

template<typename Semantics>
inline bool operator != (const syntax_node<Semantics>& first, const syntax_node<Semantics>& second) {
	return !(first == second);
}

template<typename Stream>
inline bool print_indent(unsigned int indent, Stream& out) {
	for (unsigned int i = 0; i < indent; i++)
		if (!print("  ", out)) return false;
	return true;
}

template<typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
bool print(const syntax_node<Semantics>& node, Stream& out, unsigned int indent,
	NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	bool success = true;
	if (node.is_terminal()) {
		success &= print(' ', out);
		success &= print('\'', out);
		success &= print(node.right.t.terminals[0], out, terminal_printer);
		for (unsigned int i = 1; i < node.right.t.length; i++) {
			success &= print(' ', out);
			success &= print(node.right.t.terminals[i], out, terminal_printer);
		}
		success &= print('\'', out);
	} else {
		for (unsigned int i = 0; i < node.right.nt.length; i++) {
			success &= print('\n', out) && print_indent(indent + 1, out);
			success &= print('(', out) && print(node.right.nt.nonterminals[i], out, nonterminal_printer);
			success &= print(':', out) && print(node.right.nt.transformations[i], out);
			if (node.children[i] == NULL) {
				success &= print(" <null>", out);
			} else {
				success &= print(*node.children[i], out, indent + 1, nonterminal_printer, terminal_printer);
			}
			success &= print(')', out);
		}
	}
	return success;
}

template<typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
bool print(const syntax_node<Semantics>& node, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer,
		unsigned int root_nonterminal = 1)
{
	return print('(', out) && print(root_nonterminal, out, nonterminal_printer) && print(' ', out)
		&& print(node, out, 0, nonterminal_printer, terminal_printer) && print(')', out);
}

template<typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
bool print(const syntax_node<Semantics>& node, Stream& out, unsigned int indent,
	NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer,
	const Semantics& logical_form)
{
	bool success = true;
	if (node.is_terminal()) {
		success &= print(' ', out);
		success &= print('\'', out);
		success &= print(node.right.t.terminals[0], out, terminal_printer);
		for (unsigned int i = 1; i < node.right.t.length; i++) {
			success &= print(' ', out);
			success &= print(node.right.t.terminals[i], out, terminal_printer);
		}
		success &= print('\'', out);
	} else {
		for (unsigned int i = 0; i < node.right.nt.length; i++) {
			Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
			if (!apply(node.right.nt.transformations[i], logical_form, transformed))
				return false;
			success &= print('\n', out) && print_indent(indent + 1, out);
			success &= print('(', out) && print(node.right.nt.nonterminals[i], out, nonterminal_printer);
			success &= print(':', out) && print(node.right.nt.transformations[i], out);
			success &= print(" {", out) && print(transformed, out, terminal_printer) && print('}', out);
			if (node.children[i] == NULL) {
				success &= print(" <null>", out);
			} else {
				success &= print(*node.children[i], out, indent + 1, nonterminal_printer, terminal_printer, transformed);
			}
			success &= print(')', out);
			free(transformed);
		}
	}
	return success;
}

template<typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
bool print(const syntax_node<Semantics>& node, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer,
		const Semantics& logical_form, unsigned int root_nonterminal = 1)
{
	return print('(', out) && print(root_nonterminal, out, nonterminal_printer) && print(" {", out)
		&& print(logical_form, out, terminal_printer) && print("} ", out)
		&& print(node, out, 0, nonterminal_printer, terminal_printer, logical_form) && print(')', out);
}

template<typename Semantics, typename Stream, typename RuleReader>
bool read(syntax_node<Semantics>& node, Stream& stream, RuleReader& reader) {
	if (!read(node.right, stream, reader)) return false;
	if (node.right.is_terminal()) {
		node.children = NULL;
	} else {
		node.children = (syntax_node<Semantics>**) calloc(node.right.nt.length, sizeof(syntax_node<Semantics>*));
		if (node.children == NULL) {
			free(node.right);
			return false;
		}
		for (unsigned int i = 0; i < node.right.nt.length; i++) {
			node.children[i] = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
			if (node.children[i] == NULL
			 || !read(*node.children[i], stream, reader))
			{
				if (node.children[i] != NULL)
					free(node.children[i]);
				for (unsigned int j = 0; j < i; j++) {
					free(*node.children[j]); free(node.children[j]);
				}
				free(node.children);
				free(node.right);
				return false;
			}
		}
	}
	node.reference_count = 1;
	return true;
}

template<typename Semantics, typename Stream, typename RuleWriter>
bool write(const syntax_node<Semantics>& node, Stream& stream, RuleWriter& writer) {
	if (!write(node.right, stream, writer)) return false;
	if (!node.right.is_terminal()) {
		for (unsigned int i = 0; i < node.right.nt.length; i++)
			if (!write(*node.children[i], stream, writer)) return false;
	}
	return true;
}

template<typename Semantics, typename Distribution>
inline bool yield(const rule<Semantics>& terminal,
		const Distribution& rule_distribution, const Semantics& logical_form,
		unsigned int*& sentence, unsigned int& length, unsigned int& capacity)
{
	unsigned int* leaf;
	unsigned int leaf_length;
	if (terminal.t.inflected != nullptr) {
		leaf = terminal.t.inflected;
		leaf_length = terminal.t.inflected_length;
	} else {
		leaf = terminal.t.terminals;
		leaf_length = terminal.t.length;
	}

	if (!ensure_capacity(sentence, capacity, length + leaf_length))
		return false;
	memcpy(sentence + length, leaf, sizeof(unsigned int) * leaf_length);
	length += leaf_length;
	return true;
}

template<typename Semantics, typename Distribution, typename Printer, typename... OutputType>
bool yield(const grammar<Semantics, Distribution>& G,
		const syntax_node<Semantics>& node,
		unsigned int nonterminal, const Semantics& logical_form,
		Printer& printer, OutputType&&... output)
{
	if (node.is_terminal()) {
		return yield(node.right,
				G.nonterminals[nonterminal - 1].rule_distribution,
				logical_form, std::forward<OutputType>(output)...);
	}

	for (unsigned int i = 0; i < node.right.nt.length; i++) {
		Semantics transformed;
		if (!apply(node.right.nt.transformations[i], logical_form, transformed)) {
			print("yield ERROR: Unable to apply semantic transformation '", stderr);
			print(node.right.nt.transformations[i], stderr); print("' to logical form:\n", stderr);
			print(logical_form, stderr, printer); print('\n', stderr); return false;
		}
		if (!yield(G, *node.children[i], node.right.nt.nonterminals[i], transformed, printer, std::forward<OutputType>(output)...))
			return false;
	}
	return true;
}

template<typename Semantics, typename Distribution, typename Printer>
bool yield(const grammar<Semantics, Distribution>& G,
		const syntax_node<Semantics>& node,
		const Semantics& logical_form, sequence& sentence,
		Printer& printer, unsigned int nonterminal = 1)
{
	unsigned int capacity = 16; sentence.length = 0;
	sentence.tokens = (unsigned int*) malloc(sizeof(unsigned int) * 16);
	if (sentence.tokens == NULL || !yield(G, node, nonterminal, logical_form, printer, sentence.tokens, sentence.length, capacity)) {
		fprintf(stderr, "yield ERROR: Unable to compute yield of derivation.\n");
		return false;
	}
	return true;
}

template<typename Semantics, typename Distribution>
inline bool yield(const grammar<Semantics, Distribution>& G,
		const syntax_node<Semantics>& node, const Semantics& logical_form,
		sequence& sentence, unsigned int nonterminal = 1)
{
	default_scribe printer;
	return yield(G, node, logical_form, sentence, printer, nonterminal);
}

template<typename Semantics, typename Distribution, typename StringMapType>
bool log_probability(double& score,
	grammar<Semantics, Distribution>& G,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	const StringMapType& token_map,
	unsigned int nonterminal_id)
{
	const rule<Semantics>& r = syntax.right;
	double rule_score = log_probability(G.nonterminals[nonterminal_id - 1].rule_distribution, r, logical_form, token_map);
	score += rule_score;

	if (r.is_terminal()) return true;
	for (unsigned int i = 0; i < r.nt.length; i++) {
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (syntax.children[i] == NULL) continue;
		if (!apply(r.nt.transformations[i], logical_form, transformed)) {
			return false;
		} else if (!log_probability(score, G, *syntax.children[i], transformed, token_map, r.nt.nonterminals[i])) {
			free(transformed);
			return false;
		}
		free(transformed);
	}
	return true;
}

/* Computes the log probability of a given parse using the given grammar. */
template<typename Semantics, typename Distribution, typename StringMapType>
double log_probability(
	grammar<Semantics, Distribution>& G,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	const StringMapType& token_map,
	unsigned int nonterminal_id = 1)
{
	double score = 0.0;
	if (!log_probability(score, G, syntax, logical_form, token_map, nonterminal_id))
		return -std::numeric_limits<double>::infinity();
	return score;
}

/* Computes the log joint probability of the grammar and given derivations */
template<typename Semantics, typename Distribution, typename StringMapType>
double log_probability(
	grammar<Semantics, Distribution>& G,
	const syntax_node<Semantics>* const* syntax,
	const Semantics* logical_forms,
	unsigned int sentence_count,
	const StringMapType& token_map)
{
	double score = 0.0;
	for (unsigned int i = 0; i < G.nonterminals.length; i++)
		score += log_probability(G.nonterminals[i].rule_distribution);
	for (unsigned int i = 0; i < sentence_count; i++)
		score += log_probability(G, *syntax[i], logical_forms[i], token_map);
	return score;
}

/* Computes the log joint probability of the grammar and given derivations */
template<typename Semantics, typename Distribution, typename StringMapType>
double log_probability(
	grammar<Semantics, Distribution>& G,
	const syntax_node<Semantics>* const* syntax,
	const Semantics* const* logical_forms,
	unsigned int sentence_count,
	const StringMapType& token_map)
{
	double score = 0.0;
	for (unsigned int i = 0; i < G.nonterminals.length; i++)
		score += log_probability(G.nonterminals[i].rule_distribution);
	for (unsigned int i = 0; i < sentence_count; i++)
		score += log_probability(G, *syntax[i], *logical_forms[i], token_map);
	return score;
}

template<typename Semantics, typename Distribution, typename Printer>
bool add_tree(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G,
	Printer& printer)
{
	nonterminal<Semantics, Distribution>& N = G.nonterminals[nonterminal_id - 1];

	N.clear();
	if (!add(N.rule_distribution, syntax.right, logical_form))
		return false;

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.nt.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.nt.transformations[i], logical_form, transformed)) {
			print("add_tree ERROR: Unable to apply semantic transformation function '", stderr);
			print(syntax.right.nt.transformations[i], stderr); print("' to the logical form:\n", stderr);
			print(logical_form, stderr, printer); print('\n', stderr); return false;
		} if (!add_tree(syntax.right.nt.nonterminals[i], *syntax.children[i], transformed, G, printer))
			return false;
	}
	return true;
}

template<typename Semantics, typename Distribution>
inline bool add_tree(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G)
{
	default_scribe printer;
	return add_tree(nonterminal_id, syntax, logical_form, G, printer);
}

template<typename Semantics, typename Distribution>
bool remove_tree(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G)
{
	nonterminal<Semantics, Distribution>& N = G.nonterminals[nonterminal_id - 1];

	if (!remove(N.rule_distribution, syntax.right, logical_form))
		return false;
	N.clear();

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.transformations[i], logical_form, transformed)
		 || !remove_tree(syntax.right.nonterminals[i], *syntax.children[i], transformed, G))
			return false;
	}
	return true;
}

template<typename Semantics, typename Distribution, typename StringMapType>
bool add_tree(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G,
	const StringMapType& token_map,
	double& score)
{
	nonterminal<Semantics, Distribution>& N = G.nonterminals[nonterminal_id - 1];

	N.clear();
	score += log_probability(G.nonterminals[nonterminal_id - 1].rule_distribution, syntax.right, logical_form, token_map);
	N.clear();
	if (!add(N.rule_distribution, syntax.right, logical_form))
		return false;

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.nt.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.nt.transformations[i], logical_form, transformed)
		 || !add_tree(syntax.right.nt.nonterminals[i], *syntax.children[i], transformed, G, token_map, score))
			return false;
	}
	return true;
}

template<typename Semantics, typename Distribution, typename StringMapType>
bool remove_tree(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G,
	const StringMapType& token_map,
	double& score)
{
	nonterminal<Semantics, Distribution>& N = G.nonterminals[nonterminal_id - 1];

	if (!remove(N.rule_distribution, syntax.right, logical_form))
		return false;
	N.clear();
	score += log_probability(G.nonterminals[nonterminal_id - 1].rule_distribution, syntax.right, logical_form, token_map);
	N.clear();

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.nt.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.nt.transformations[i], logical_form, transformed)
		 || !remove_tree(syntax.right.nt.nonterminals[i], *syntax.children[i], transformed, G, token_map, score))
			return false;
	}
	return true;
}

template<typename Semantics, typename RuleDistribution>
inline int sample(
		const grammar<Semantics, RuleDistribution>& G,
		syntax_node<Semantics>*& syntax,
		const Semantics& logical_form,
		unsigned int nonterminal_id = 1)
{
	syntax = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
	syntax->reference_count = 1;
	if (syntax == NULL) {
		fprintf(stderr, "sample ERROR: Insufficient memory for syntax_node.\n");
		return -1;
	}

	/* first sample a production rule */
	const nonterminal<Semantics, RuleDistribution>& N = G.nonterminals[nonterminal_id - 1];
	if (!sample(N.rule_distribution, syntax->right, logical_form)) {
		free(syntax); syntax = NULL;
		return 1;
	}

	if (syntax->right.is_terminal()) {
		syntax->children = NULL;
	} else {
		syntax->children = (syntax_node<Semantics>**) calloc(
				syntax->right.nt.length, sizeof(syntax_node<Semantics>*));
		if (syntax->children == NULL) {
			fprintf(stderr, "sample ERROR: Insufficient memory for child nodes.\n");
			free(*syntax); free(syntax);
			syntax = NULL;
			return -1;
		}
		for (unsigned int i = 0; i < syntax->right.nt.length; i++) {
			Semantics transformed;
			if (!apply(syntax->right.nt.transformations[i], logical_form, transformed)) {
				free(*syntax); free(syntax);
				syntax = NULL;
				return 1;
			}

			int status = sample(G, syntax->children[i], transformed, syntax->right.nt.nonterminals[i]);
			if (status != 0) {
				free(*syntax); free(syntax);
				syntax = NULL;
				return status;
			}
		}
	}
	return 0;
}

template<typename Semantics>
struct rooted_syntax_node {
	unsigned int root;
	syntax_node<Semantics>* tree;

	rooted_syntax_node() : tree(nullptr) { }

	~rooted_syntax_node() {
		if (tree != nullptr) {
			core::free(*tree);
			if (tree->reference_count == 0)
				core::free(tree);
		}
	}

	inline void operator = (const rooted_syntax_node<Semantics>& src) {
		root = src.root;
		tree = src.tree;
		tree->reference_count++;
	}

	static inline bool is_empty(const rooted_syntax_node<Semantics>& node) {
		return node.tree == nullptr;
	}

	static inline void set_empty(rooted_syntax_node<Semantics>& node) {
		node.tree = nullptr;
	}

	static inline unsigned int hash(const rooted_syntax_node<Semantics>& node) {
		return default_hash(node.root) ^ syntax_node<Semantics>::hash(*node.tree);
	}

	static inline void free(rooted_syntax_node<Semantics>& node) {
		core::free(*node.tree);
		if (node.tree->reference_count == 0)
			core::free(node.tree);
	}
};

template<typename Semantics>
inline bool operator == (const rooted_syntax_node<Semantics>& first, const rooted_syntax_node<Semantics>& second)
{
	return first.root == second.root
		&& *first.tree == *second.tree;
}

struct null_semantics {
	enum feature {
		FEATURE_NULL
	};

	enum function_type {
		FUNCTION_EMPTY = 0,
		FUNCTION_IDENTITY = 1
	};

	struct function {
		function_type type;

		constexpr function(const function_type& type) : type(type) { }

		static inline unsigned int hash(const function& f) {
			return default_hash(f.type);
		}

		static inline bool is_empty(const function& f) {
			return f.type == FUNCTION_EMPTY;
		}

		static inline void set_empty(function& f) {
			f.type = FUNCTION_EMPTY;
		}
	};

	template<typename Stream>
	static inline bool print(const function& f, Stream& out) {
		switch (f.type) {
		case null_semantics::FUNCTION_IDENTITY:
			return core::print("identity", out);
		default:
			fprintf(stderr, "print ERROR: Unrecognized null_semantics::function type.\n");
			return false;
		}
	}

	static inline function default_function() {
		return FUNCTION_EMPTY;
	}

	static constexpr bool initialize_any(const null_semantics& logical_form) { return true; };

	static inline void move(const null_semantics& src, null_semantics& dst) { }
	static inline void swap(null_semantics& src, null_semantics& dst) { }
	static inline void free(const null_semantics& logical_form) { }
};

constexpr inline bool initialize_any(const null_semantics& lf) { return true; }

constexpr bool operator == (const null_semantics& first, const null_semantics& second) {
	return true;
}

constexpr bool operator != (const null_semantics& first, const null_semantics& second) {
	return false;
}

constexpr bool operator == (const null_semantics::function& first, const null_semantics::function& second) {
	return first.type == second.type;
}

constexpr bool operator != (const null_semantics::function& first, const null_semantics::function& second) {
	return first.type != second.type;
}

template<typename Stream, typename Printer>
constexpr bool print(const null_semantics& logical_form, Stream& out, Printer& printer) {
	return true;
}

constexpr bool is_ambiguous(const null_semantics& logical_form) { return false; }

constexpr bool apply(null_semantics::function function, const null_semantics& src, null_semantics& dst) {
	return true;
}

inline bool invert(
	null_semantics*& inverse,
	unsigned int& inverse_count,
	const null_semantics::function& function,
	const null_semantics& first_arg,
	const null_semantics& second_arg)
{
	inverse = (null_semantics*) malloc(sizeof(null_semantics));
	if (inverse == nullptr) return false;
	inverse[0] = null_semantics();
	inverse_count = 1;
	return true;
}

constexpr unsigned int get_feature(
	null_semantics::feature feature,
	const null_semantics& src,
	unsigned int*& excluded,
	unsigned int& excluded_count)
{
	return 1;
}

constexpr bool set_feature(
	null_semantics::feature feature,
	null_semantics& logical_form,
	unsigned int feature_value)
{
	return true;
}

constexpr bool exclude_features(
	null_semantics::feature feature,
	null_semantics& logical_form,
	const unsigned int* excluded,
	unsigned int excluded_count)
{
	return true;
}

inline void is_separable(
		const transformation<null_semantics>* const functions,
		unsigned int rule_length, bool* separable)
{
	for (unsigned int i = 0; i < rule_length; i++)
		separable[i] = false;
}

struct dummy_morphology_parser { };

template<bool First, typename EmitRootFunction, typename PartOfSpeechType>
inline bool morphology_parse(
		const dummy_morphology_parser& morph, const sequence& words, PartOfSpeechType pos,
		const null_semantics& logical_form, EmitRootFunction emit_root)
{
	return emit_root(words, logical_form);
}

template<typename PartOfSpeechType>
constexpr bool morphology_is_valid(
		const dummy_morphology_parser& morph,
		const sequence& terminal, PartOfSpeechType pos,
		const null_semantics& logical_form)
{
	return true;
}

template<bool IsFirst, typename Semantics,
	typename Distribution, typename Morphology,
	typename NonterminalPrinter, typename TerminalPrinter,
	typename StringMapType>
bool is_parseable(
		const syntax_node<Semantics>& syntax,
		const Semantics& logical_form,
		grammar<Semantics, Distribution>& G,
		const Morphology& morphology_parser,
		Semantics& logical_form_set,
		pair<TerminalPrinter&, NonterminalPrinter&>& printers,
		const StringMapType& token_map, double& prior,
		unsigned int nonterminal = 1)
{
#if defined(USE_NONTERMINAL_PREITERATOR)
	if (!is_parseable(G.nonterminals[nonterminal - 1].rule_distribution,
			syntax, logical_form, logical_form_set, printers, token_map))
		return false;

	double new_prior = log_probability<false>(logical_form_set);
	if (new_prior > prior || new_prior == -std::numeric_limits<double>::infinity()) {
		print("is_parseable ERROR: The prior is not monotonic after checking "
				"parseability with the rule distribution to obtain logical form set ", stderr);
		print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
		print(syntax.right, stderr, printers); print('\n', stderr);
		return false;
	}
	prior = new_prior;
#endif

	if (!syntax.right.is_terminal()) {
		for (unsigned int i = 0; i < syntax.right.nt.length; i++) {
			Semantics& child_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
			Semantics& child_logical_form_set = *((Semantics*) alloca(sizeof(Semantics)));
			if (!apply(syntax.right.nt.transformations[i], logical_form_set, child_logical_form_set)) {
				print("is_parseable ERROR: Unable to apply semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' to logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				return false;
			} else if (!apply(syntax.right.nt.transformations[i], logical_form, child_logical_form)) {
				print("is_parseable ERROR: Unable to apply semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' to ground truth logical form ", stderr);
				print(logical_form, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				free(child_logical_form_set);
				return false;
			}

			double child_prior = log_probability<false>(child_logical_form_set);

			if (child_prior == -std::numeric_limits<double>::infinity()) {
				print("is_parseable ERROR: The prior is -inf after applying semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' to logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" to obtain logical form set ", stderr);
				print(child_logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				free(child_logical_form); free(child_logical_form_set);
				return false;
			} else if (i == 0 && !is_parseable<IsFirst>(*syntax.children[i], child_logical_form, G, morphology_parser, child_logical_form_set, printers, token_map, child_prior, syntax.right.nt.nonterminals[i])) {
				free(child_logical_form_set);
				free(child_logical_form);
				return false;
			} else if (i != 0 && !is_parseable<false>(*syntax.children[i], child_logical_form, G, morphology_parser, child_logical_form_set, printers, token_map, child_prior, syntax.right.nt.nonterminals[i])) {
				free(child_logical_form_set);
				free(child_logical_form);
				return false;
			}

			/* invert the child logical form set */
			Semantics* inverse = nullptr; unsigned int inverse_count;
			if (!invert(inverse, inverse_count, syntax.right.nt.transformations[i], logical_form_set, child_logical_form_set) || inverse_count == 0) {
				print("is_parseable ERROR: Unable to invert semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				print("Tried to invert ", stderr); print(child_logical_form_set, stderr, printers.key);
				print(" and intersect with ", stderr); print(logical_form_set, stderr, printers.key); print(".\n", stderr);
				free(child_logical_form_set); free(child_logical_form);
				if (inverse != nullptr) {
					for (unsigned int j = 0; j < inverse_count; j++)
						free(inverse[j]);
					free(inverse);
				}
				return false;
			}
			free(child_logical_form_set);
			free(logical_form_set);
			/* find `j` such that `logical_form` is a subset of `inverse[j]` */
			unsigned int j;
			for (j = 0; j < inverse_count; j++)
				if (is_subset(logical_form, inverse[j])) break;
			if (j == inverse_count) {
				print("is_parseable ERROR: The true inverse is not an element of any `inverse[j]` after inverting semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("'.\n", stderr);
				print("  True inverse: ", stderr); print(logical_form, stderr, printers.key); print('\n', stderr);
				for (j = 0; j < inverse_count; j++) {
					print("  inverse[", stderr); print(j, stderr); print("]:   ", stderr); print(inverse[j], stderr, printers.key); print('\n', stderr);
					free(inverse[j]);
				}
				free(inverse);
				initialize_any(logical_form_set);
				free(child_logical_form);
				return false;
			}
			logical_form_set = inverse[j];
			for (unsigned int k = 0; k < inverse_count; k++)
				free(inverse[k]);
			free(inverse);

			/* invert the child logical form (this isn't strictly needed for parsing, but it is for things like sampling, and is a good correctness check anyway) */
			inverse = nullptr;
			if (!invert(inverse, inverse_count, syntax.right.nt.transformations[i], logical_form, child_logical_form) || inverse_count == 0) {
				print("is_parseable ERROR: Unable to invert semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				print("Tried to invert ground truth logical form ", stderr); print(child_logical_form, stderr, printers.key);
				print(" and intersect with ", stderr); print(logical_form, stderr, printers.key); print(".\n", stderr);
				if (inverse != nullptr) {
					for (unsigned int j = 0; j < inverse_count; j++)
						free(inverse[j]);
					free(inverse);
				}
				free(child_logical_form);
				return false;
			}
			free(child_logical_form);
			for (unsigned int k = 0; k < inverse_count; k++)
				free(inverse[k]);
			free(inverse);

			double new_prior = log_probability<false>(logical_form_set);
			if (new_prior > prior || new_prior > child_prior || new_prior == -std::numeric_limits<double>::infinity()) {
				print("is_parseable ERROR: The prior is not monotonic after inverting semantic transformation function '", stderr);
				print(syntax.right.nt.transformations[i], stderr); print("' to obtain logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				return false;
			}
			prior = new_prior;
		}
	} else {
		bool found_correct_morphology = false;
		auto emit_root = [&](const sequence& root, const Semantics& new_logical_form_set)
			{
				if (found_correct_morphology) return true;

				bool root_matches = (root.length == syntax.right.t.length);
				for (unsigned int i = 0; root_matches && i < root.length; i++)
					if (root[i] != syntax.right.t.terminals[i]) root_matches = false;

				if (root_matches && is_subset(logical_form, new_logical_form_set)) {
					Semantics temp = new_logical_form_set;
					swap(logical_form_set, temp);
					found_correct_morphology = true;
				}
				return true;
			};

		sequence sentence_tokens(nullptr, 0);
		if (syntax.right.t.inflected == nullptr) {
			sentence_tokens.tokens = syntax.right.t.terminals;
			sentence_tokens.length = syntax.right.t.length;
		} else {
			sentence_tokens.tokens = syntax.right.t.inflected;
			sentence_tokens.length = syntax.right.t.inflected_length;
		}

		if (!morphology_parse<IsFirst>(morphology_parser, sentence_tokens, G.nonterminals[nonterminal - 1].rule_distribution.get_part_of_speech(), logical_form_set, emit_root)) {
			print("is_parseable ERROR: Morphological parsing failed with logical form set ", stderr);
			print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			return false;
		} else if (!found_correct_morphology) {
			print("is_parseable ERROR: Unable to find correct morphological parse with logical form set ", stderr);
			print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			return false;
		}
	}

#if !defined(USE_NONTERMINAL_PREITERATOR)
	if (!is_parseable(G.nonterminals[nonterminal - 1].rule_distribution,
			syntax, logical_form, logical_form_set, printers, token_map))
		return false;

	double new_prior = log_probability<false>(logical_form_set);
	if (new_prior > prior || new_prior == -std::numeric_limits<double>::infinity()) {
		print("is_parseable ERROR: The prior is not monotonic after checking "
				"parseability with the rule distribution to obtain logical form set ", stderr);
		print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
		print(syntax.right, stderr, printers); print('\n', stderr);
		return false;
	}
	prior = new_prior;
#endif
	return true;
}

template<typename Semantics, typename Distribution, typename Morphology,
	typename NonterminalPrinter, typename TerminalPrinter, typename StringMapType>
bool is_parseable(
		syntax_node<Semantics>& syntax,
		const Semantics& logical_form,
		grammar<Semantics, Distribution>& G,
		const Morphology& morphology_parser,
		Semantics& logical_form_set,
		NonterminalPrinter& nonterminal_printer,
		TerminalPrinter& terminal_printer,
		const StringMapType& token_map,
		unsigned int nonterminal = 1,
		bool test_equivalence = true)
{
	double prior = log_probability<false>(logical_form_set);
	if (prior == -std::numeric_limits<double>::infinity()) {
		fprintf(stderr, "is_parseable ERROR: The prior of the root logical form set is -inf: ");
		print(logical_form_set, stderr, terminal_printer); print('\n', stderr);
		return false;
	}

	double true_prior = log_probability<true>(logical_form);
	if (true_prior == -std::numeric_limits<double>::infinity()) {
		fprintf(stderr, "is_parseable ERROR: The prior of the ground truth logical form is -inf: ");
		print(logical_form, stderr, terminal_printer); print('\n', stderr);
		return false;
	}

	auto printers = pair<TerminalPrinter&, NonterminalPrinter&>(terminal_printer, nonterminal_printer);
	if (!is_parseable<true, Semantics, Distribution, Morphology, TerminalPrinter, NonterminalPrinter, StringMapType>(
			syntax, logical_form, G, morphology_parser, logical_form_set, printers, token_map, prior, nonterminal))
		return false;
	if ((test_equivalence && !equivalent(logical_form, logical_form_set))
	 || (!test_equivalence && !is_subset(logical_form, logical_form_set))) {
		if (test_equivalence)
			print("is_parseable ERROR: The parsed logical form is not equivalent to the reference logical form.\n", stderr);
		else print("is_parseable ERROR: The reference logical form is not a subset of the parsed logical form set.\n", stderr);
		print("  Reference logical form: ", stderr); print(logical_form, stderr, terminal_printer); print('\n', stderr);
		print("  Parsed logical form:    ", stderr); print(logical_form_set, stderr, terminal_printer); print('\n', stderr);
		return false;
	}
	return true;
}


#endif /* GRAMMAR_H_ */
