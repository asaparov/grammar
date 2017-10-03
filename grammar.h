/**
 * grammar.h
 *
 *  Created on: Jul 15, 2015
 *      Author: asaparov
 */

#ifndef GRAMMAR_H_
#define GRAMMAR_H_

#include <math.h>
#include <limits.h>
#include <core/array.h>
#include <core/map.h>
#include <core/io.h>
#include <core/utility.h>
#include <math/features.h>

#define ALL_EXCEPT UINT_MAX
#define NEW_TERMINAL (UINT_MAX - 3)

using namespace core;

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

/* Represents a production rule in the semantic grammar. */
template<typename Semantics>
struct rule {
	typedef typename Semantics::function function;

	unsigned int* nonterminals;
	function* functions;
	unsigned int length;

	/* constructs an empty rule */
	rule(unsigned int length) : length(length) {
		if (!initialize())
			exit(EXIT_FAILURE);
	}

	rule(const rule<Semantics>& src) : length(src.length) {
		if (!initialize(src, src.length))
			exit(EXIT_FAILURE);
	}

	rule(const rule<Semantics>& src, unsigned int new_length) : length(new_length) {
		if (!initialize(src, new_length))
			exit(EXIT_FAILURE);
	}

	rule(const sequence& terminal) : length(terminal.length) {
		if (!initialize(terminal))
			exit(EXIT_FAILURE);
	}

	~rule() { free(); }

	inline void operator = (const rule<Semantics>& src) {
		length = src.length;
		if (!initialize(src, src.length))
			exit(EXIT_FAILURE);
	}

	inline bool is_terminal() const {
		return functions[0] == Semantics::terminal_function();
	}

	inline const sequence get_terminal() const {
		return sequence(nonterminals, length);
	}

	static inline unsigned int hash(const rule<Semantics>& rule) {
		unsigned int hash = default_hash(rule.nonterminals, rule.length);
		if (rule.is_terminal()) return hash;
		for (unsigned int i = 0; i < rule.length; i++)
			hash ^= hasher<function>::hash(rule.functions[i]);
		return hash;
	}

	static inline void move(const rule<Semantics>& src, rule<Semantics>& dst) {
		dst.nonterminals = src.nonterminals;
		dst.functions = src.functions;
		dst.length = src.length;
	}

	static inline bool copy(const rule<Semantics>& src, rule<Semantics>& dst) {
		return init(dst, src, src.length);
	}

	static inline void swap(rule<Semantics>& first, rule<Semantics>& second) {
		core::swap(first.nonterminals, second.nonterminals);
		core::swap(first.functions, second.functions);
		core::swap(first.length, second.length);
	}

	static inline bool is_empty(const rule<Semantics>& rule) {
		return rule.nonterminals == NULL;
	}

	static inline void set_empty(rule<Semantics>& rule) {
		rule.nonterminals = NULL;
	}

	static inline void set_empty(rule<Semantics>* rules, unsigned int count) {
		memset(rules, 0, sizeof(rule<Semantics>) * count);
	}

	static inline void free(rule<Semantics>& r) {
		r.free();
	}

private:
	/* NOTE: this function assumes 'length' was initialized */
	bool initialize() {
		nonterminals = (unsigned int*) malloc(max((size_t) 1, sizeof(unsigned int) * length));
		if (nonterminals == NULL) {
			fprintf(stderr, "rule.initialize ERROR: Out of memory.\n");
			return false;
		}
		functions = (function*) malloc(max((size_t) 1, sizeof(function) * length));
		if (functions == NULL) {
			core::free(nonterminals);
			fprintf(stderr, "rule.initilize ERROR: Out of memory.\n");
			return false;
		}
		return true;
	}

	bool initialize(const rule<Semantics>& src, unsigned int new_length) {
		if (!initialize()) return false;
		if (src.length == 0) return true;
		memcpy(nonterminals, src.nonterminals, sizeof(unsigned int) * src.length);
		if (src.is_terminal()) {
			functions[0] = Semantics::terminal_function();
		} else {
			memcpy(functions, src.functions, sizeof(function) * src.length);
		}
		return true;
	}

	bool initialize(const sequence& terminal) {
		if (!initialize()) return false;
		functions[0] = Semantics::terminal_function();
		memcpy(nonterminals, terminal.tokens, sizeof(unsigned int) * length);
		return true;
	}

	inline void free() {
		core::free(nonterminals);
		core::free(functions);
	}

	template<typename A> friend bool init(rule<A>&, unsigned int);
	template<typename A> friend bool init(rule<A>&, const rule<A>&, unsigned int);
	template<typename A> friend bool init(rule<A>&, const sequence&);
	template<typename A, typename B> friend bool read(rule<A>&, B&, hash_map<string, unsigned int>&);
};

template<typename Semantics>
inline bool init(rule<Semantics>& rule, unsigned int length) {
	rule.length = length;
	return rule.initialize();
}

template<typename Semantics>
inline bool init(rule<Semantics>& dst, const rule<Semantics>& src, unsigned int new_length) {
	dst.length = new_length;
	return dst.initialize(src, new_length);
}

template<typename Semantics>
inline bool init(rule<Semantics>& dst, const rule<Semantics>& src) {
	return init(dst, src, src.length);
}

template<typename Semantics>
inline bool init(rule<Semantics>& rule, const sequence& terminal) {
	rule.length = terminal.length;
	return rule.initialize(terminal);
}

template<typename Semantics>
inline bool operator == (const rule<Semantics>& first, const rule<Semantics>& second) {
	if (first.length != second.length || first.nonterminals == NULL)
		return false;

	/* compare nonterminal list */
	for (unsigned int i = 0; i < first.length; i++)
		if (first.nonterminals[i] != second.nonterminals[i]) return false;

	if (first.is_terminal()) {
		if (!second.is_terminal()) return false;
		else return true;
	} else if (second.is_terminal()) return false;

	/* compare function list */
	for (unsigned int i = 0; i < first.length; i++)
		if (first.functions[i] != second.functions[i]) return false;
	return true;
}

template<typename Semantics>
inline bool operator != (const rule<Semantics>& first, const rule<Semantics>& second) {
	return !(first == second);
}

template<typename Semantics>
inline bool operator < (const rule<Semantics>& first, const rule<Semantics>& second) {
	if (first.length < second.length) return true;
	else if (first.length > second.length) return false;

	if (first.is_terminal()) {
		if (!second.is_terminal()) return true;
	} else {
		if (second.is_terminal()) return false;
	}

	/* first compare the nonterminals */
	for (unsigned int i = 0; i < first.length; i++) {
		if (first.nonterminals[i] < second.nonterminals[i]) return true;
		else if (first.nonterminals[i] > second.nonterminals[i]) return false;
	}

	if (!first.is_terminal()) {
		/* compare the transformation functions */
		for (unsigned int i = 0; i < first.length; i++) {
			if (first.functions[i] < second.functions[i]) return true;
			else if (second.functions[i] < first.functions[i]) return false;
		}
	}

	return false;
}

template<typename Semantics, typename Stream, typename AtomPrinter, typename NonterminalPrinter>
inline bool print(const rule<Semantics>& r, Stream& out, pair<AtomPrinter&, NonterminalPrinter&> printers) {
	if (r.is_terminal())
		return print('"', out) && print(sequence(r.nonterminals, r.length), out, printers.key) && print('"', out);
	if (!print('(', out)) return false;
	for (unsigned int i = 0; i < r.length; i++) {
		if (i > 0 && !print(' ', out)) return false;
		if (!print(r.nonterminals[i], out, printers.value) || !print(':', out) || !print(r.functions[i], out))
			return false;
	}
	return print(')', out);
}

template<typename Semantics, typename Stream>
bool read(rule<Semantics>& r, Stream& stream, hash_map<string, unsigned int>& token_map)
{
	if (!read(r.length, stream)
	 || !r.initialize())
		return false;
	if (!read(r.functions[0], stream)) {
		r.free();
		return false;
	}
	if (r.functions[0] == Semantics::terminal_function()) {
		for (unsigned int i = 0; i < r.length; i++) {
			if (!read(r.nonterminals[i], stream, token_map)) {
				r.free();
				return false;
			}
		}
	} else {
		if (!read(r.functions + 1, stream, r.length - 1)
		 || !read(r.nonterminals, stream, r.length)) {
			r.free();
			return false;
		}
	}
	return true;
}

template<typename Semantics, typename Stream>
bool write(const rule<Semantics>& r, Stream& stream, const string** token_map)
{
	if (!write(r.length, stream)) return false;
	if (r.functions[0] == Semantics::terminal_function()) {
		if (!write(r.functions, stream, 1)) return false;
		for (unsigned int i = 0; i < r.length; i++) {
			if (!write(r.nonterminals[i], stream, token_map))
				return false;
		}
		return true;
	} else {
		return write(r.functions, stream, r.length)
			&& write(r.nonterminals, stream, r.length);
	}
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
		right(length), children(NULL), reference_count(1)
	{
		if (!initialize(terminals, length))
			exit(EXIT_FAILURE);
	}

	syntax_node(const syntax_node<Semantics>& src) :
		right(src.right), reference_count(1)
	{
		if (!initialize(src, src.right.length))
			exit(EXIT_FAILURE);
	}

	syntax_node(const syntax_node<Semantics>& src, unsigned int new_length) :
		right(src.right, new_length), reference_count(1)
	{
		if (!initialize(src, new_length))
			exit(EXIT_FAILURE);
	}

	syntax_node(const rule<Semantics>& r) : right(r), reference_count(1) {
		children = (syntax_node<Semantics>**) calloc(r.length, sizeof(syntax_node<Semantics>*));
		if (children == NULL) {
			fprintf(stderr, "syntax_node ERROR: Insufficient memory for child node array.\n");
			exit(EXIT_FAILURE);
		}
	}

	~syntax_node() { free(); }

	inline void operator = (const syntax_node<Semantics>& src) {
		right = src.right;
		if (!initialize(src, src.right.length))
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
	inline bool initialize(const syntax_node<Semantics>& src, unsigned int new_length) {
		if (src.children == NULL) {
			children = NULL;
			return true;
		}
		children = (syntax_node<Semantics>**) malloc(sizeof(syntax_node<Semantics>*) * new_length);
		if (children == NULL) {
			fprintf(stderr, "syntax_node.initialize ERROR: Out of memory.\n");
			core::free(right);
			return false;
		}
		for (unsigned int i = 0; i < src.right.length; i++) {
			children[i] = src.children[i];
			if (children[i] != NULL)
				children[i]->reference_count++;
		}
		return true;
	}

	inline bool initialize(const syntax_node<Semantics>* const* terminals, unsigned int length)
	{
#if !defined(NDEBUG)
		if (length == 0)
			fprintf(stderr, "init WARNING: In initializing syntax_node, length is zero.\n");
#endif
		/* check if the children are terminal tokens */
		right.functions[0] = Semantics::terminal_function();
		for (unsigned int i = 0; i < length; i++)
			right.nonterminals[i] = terminals[i]->right.nonterminals[0];
		return true;
	}

	inline void free() {
		reference_count--;
		if (reference_count == 0) {
			if (children != NULL) {
				for (unsigned int i = 0; i < right.length; i++) {
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

	template<typename A>
	friend bool init(syntax_node<A>&, const syntax_node<A>&, unsigned int);

	template<typename A>
	friend bool init(syntax_node<A>&, const syntax_node<A>* const*, unsigned int);
};

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node, unsigned int rule_length)
{
	node.children = (syntax_node<Semantics>**) calloc(max(1u, rule_length), sizeof(syntax_node<Semantics>*));
	if (node.children == NULL) {
		fprintf(stderr, "init ERROR: Insufficient memory for child node array in syntax_node.\n");
		return false;
	} else if (!init(node.right, rule_length)) {
		fprintf(stderr, "init ERROR: Insufficient memory for rule in syntax_node.\n");
		free(node.children); return false;
	}
	node.reference_count = 1;
	return true;
}

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node, const rule<Semantics>& rule)
{
	node.right = rule;
	node.children = (syntax_node<Semantics>**) calloc(rule.length, sizeof(syntax_node<Semantics>*));
	if (node.children == NULL) {
		fprintf(stderr, "init ERROR: Insufficient memory for child node array in syntax_node.\n");
		return false;
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
		const syntax_node<Semantics>& src,
		unsigned int new_length)
{
	node.reference_count = 1;
	if (!init(node.right, src.right, new_length))
		return false;
	else if (!node.initialize(src, new_length)) {
		free(node.right);
		return false;
	}
	return true;
}

template<typename Semantics>
inline bool init(syntax_node<Semantics>& node,
		const syntax_node<Semantics>& src)
{
	return init(node, src, src.right.length);
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
		success &= print(node.right.nonterminals[0], out, terminal_printer);
		for (unsigned int i = 1; i < node.right.length; i++) {
			success &= print(' ', out);
			success &= print(node.right.nonterminals[i], out, terminal_printer);
		}
		success &= print('\'', out);
	} else {
		for (unsigned int i = 0; i < node.right.length; i++) {
			success &= print('\n', out) && print_indent(indent + 1, out);
			success &= print('(', out) && print(node.right.nonterminals[i], out, nonterminal_printer);
			success &= print(':', out) && print(node.right.functions[i], out);
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

template<typename Semantics, typename Stream, typename RuleReader>
bool read(syntax_node<Semantics>& node, Stream& stream, RuleReader& reader) {
	if (!read(node.right, stream, reader)) return false;
	if (node.right.is_terminal()) {
		node.children = NULL;
	} else {
		node.children = (syntax_node<Semantics>**) calloc(node.right.length, sizeof(syntax_node<Semantics>*));
		if (node.children == NULL) {
			free(node.right);
			return false;
		}
		for (unsigned int i = 0; i < node.right.length; i++) {
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
		for (unsigned int i = 0; i < node.right.length; i++)
			if (!write(*node.children[i], stream, writer)) return false;
	}
	return true;
}

template<typename Semantics, typename Distribution>
inline bool yield(const rule<Semantics>& terminal,
		const Distribution& rule_distribution, const Semantics& logical_form,
		unsigned int*& sentence, unsigned int& length, unsigned int& capacity)
{
	if (!ensure_capacity(sentence, capacity, length + terminal.length))
		return false;
	memcpy(sentence + length, terminal.nonterminals, sizeof(unsigned int) * terminal.length);
	length += terminal.length;
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

	for (unsigned int i = 0; i < node.right.length; i++) {
		Semantics transformed;
		if (!apply(node.right.functions[i], logical_form, transformed)) {
			print("yield ERROR: Unable to apply semantic transformation '", stderr);
			print(node.right.functions[i], stderr); print("' to logical form:\n", stderr);
			print(logical_form, stderr, printer); print('\n', stderr); return false;
		}
		if (!yield(G, *node.children[i], node.right.nonterminals[i], transformed, printer, std::forward<OutputType>(output)...))
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
inline double log_probability(
	grammar<Semantics, Distribution>& G,
	const rule<Semantics>& observation,
	const Semantics& logical_form,
	const StringMapType& token_map,
	unsigned int nonterminal_id)
{
	unsigned int length;
	weighted<Semantics>* posterior = log_conditional<false, false>(
			G.nonterminals[nonterminal_id - 1].rule_distribution,
			observation, logical_form, token_map, length);
	if (length == 0)
		return -std::numeric_limits<double>::infinity();
	double weight = posterior[0].log_probability;
	for (unsigned int i = 0; i < length; i++)
		free(posterior[i]);
	free(posterior);
	return weight;
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
	double rule_score = log_probability(G, r, logical_form, token_map, nonterminal_id);
extern bool debug2;
if (debug2) {
print(G.nonterminals[nonterminal_id - 1].name, stderr); fprintf(stderr, "\t%lf\n", rule_score);
}
	score += rule_score;

	if (r.is_terminal()) return true;
	for (unsigned int i = 0; i < r.length; i++) {
		Semantics transformed;
		if (syntax.children[i] == NULL) continue;
		if (!apply(r.functions[i], logical_form, transformed))
			return false;
		else if (!log_probability(score, G, *syntax.children[i], transformed, token_map, r.nonterminals[i]))
			return false;
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
	for (unsigned int i = 0; i < syntax.right.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.functions[i], logical_form, transformed)) {
			print("add_tree ERROR: Unable to apply semantic transformation function '", stderr);
			print(syntax.right.functions[i], stderr); print("' to the logical form:\n", stderr);
			print(logical_form, stderr, printer); print('\n', stderr); return false;
		} if (!add_tree(syntax.right.nonterminals[i], *syntax.children[i], transformed, G, printer))
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
		if (!apply(syntax.right.functions[i], logical_form, transformed)
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
	score += log_probability(G, syntax.right, logical_form, token_map, nonterminal_id);
	N.clear();
	if (!add(N.rule_distribution, syntax.right, logical_form))
		return false;

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.functions[i], logical_form, transformed)
		 || !add_tree(syntax.right.nonterminals[i], *syntax.children[i], transformed, G, token_map, score))
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
	score += log_probability(G, syntax.right, logical_form, token_map, nonterminal_id);
	N.clear();

	if (syntax.is_terminal()) return true;
	for (unsigned int i = 0; i < syntax.right.length; i++) {
		if (syntax.children[i] == NULL) continue;

		Semantics transformed;
		if (!apply(syntax.right.functions[i], logical_form, transformed)
		 || !remove_tree(syntax.right.nonterminals[i], *syntax.children[i], transformed, G, token_map, score))
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
				syntax->right.length, sizeof(syntax_node<Semantics>*));
		if (syntax->children == NULL) {
			fprintf(stderr, "sample ERROR: Insufficient memory for child nodes.\n");
			free(*syntax); free(syntax);
			syntax = NULL;
			return -1;
		}
		for (unsigned int i = 0; i < syntax->right.length; i++) {
			Semantics transformed;
			if (!apply(syntax->right.functions[i], logical_form, transformed)) {
				free(*syntax); free(syntax);
				syntax = NULL;
				return 1;
			}

			int status = sample(G, syntax->children[i], transformed, syntax->right.nonterminals[i]);
			if (status != 0) {
				free(*syntax); free(syntax);
				syntax = NULL;
				return status;
			}
		}
	}
	return 0;
}

template<typename Semantics, typename Distribution,
	typename NonterminalPrinter, typename TerminalPrinter>
bool is_parseable(
		const syntax_node<Semantics>& syntax,
		const Semantics& logical_form,
		grammar<Semantics, Distribution>& G,
		Semantics& logical_form_set,
		pair<TerminalPrinter&, NonterminalPrinter&>& printers,
		const string** token_map, double& prior,
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

	/* TODO: make the error messages more informative */
	if (!syntax.right.is_terminal()) {
		for (unsigned int i = 0; i < syntax.right.length; i++) {
			Semantics child_logical_form, child_logical_form_set;
			if (!apply(syntax.right.functions[i], logical_form_set, child_logical_form_set)) {
				print("is_parseable ERROR: Unable to apply semantic transformation function '", stderr);
				print(syntax.right.functions[i], stderr); print("' to logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				return false;
			} else if (!apply(syntax.right.functions[i], logical_form, child_logical_form)) {
				print("is_parseable ERROR: Unable to apply semantic transformation function '", stderr);
				print(syntax.right.functions[i], stderr); print("' to ground truth logical form ", stderr);
				print(logical_form, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				free(child_logical_form_set);
				return false;
			}

			double child_prior = log_probability<false>(child_logical_form_set);
			if (child_prior == -std::numeric_limits<double>::infinity()) {
				print("is_parseable ERROR: The prior is -inf after applying semantic transformation function '", stderr);
				print(syntax.right.functions[i], stderr); print("' to logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" to obtain logical form set ", stderr);
				print(child_logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				return false;
			} else if (!is_parseable(*syntax.children[i], child_logical_form, G, child_logical_form_set, printers, token_map, child_prior, syntax.right.nonterminals[i])) {
				free(child_logical_form_set);
				free(child_logical_form);
				return false;
			}
			free(child_logical_form);

			/* invert the child logical form set */
			/* TODO: make this work with more general invert iterators */
			typename Semantics::invert_iterator inverter;
			if (!invert(inverter, syntax.right.functions[i], logical_form_set, child_logical_form_set)) {
				print("is_parseable ERROR: Unable to invert semantic transformation function '", stderr);
				print(syntax.right.functions[i], stderr); print("' at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				print("Tried to invert ", stderr); print(child_logical_form_set, stderr, printers.key);
				print(" and intersect with ", stderr); print(logical_form_set, stderr, printers.key); print(".\n", stderr);
				free(child_logical_form_set);
				return false;
			}
			free(child_logical_form_set);
			free(logical_form_set);
			logical_form_set = *inverter.inverse;
			free(inverter);

			double new_prior = log_probability<false>(logical_form_set);
			if (new_prior > prior || new_prior > child_prior || new_prior == -std::numeric_limits<double>::infinity()) {
				print("is_parseable ERROR: The prior is not monotonic after inverting semantic transformation function '", stderr);
				print(syntax.right.functions[i], stderr); print("' to obtain logical form set ", stderr);
				print(logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				return false;
			}
			prior = new_prior;
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

template<typename Semantics, typename Distribution,
	typename NonterminalPrinter, typename TerminalPrinter>
bool is_parseable(
		syntax_node<Semantics>& syntax,
		const Semantics& logical_form,
		grammar<Semantics, Distribution>& G,
		Semantics& logical_form_set,
		NonterminalPrinter& nonterminal_printer,
		TerminalPrinter& terminal_printer,
		const string** token_map,
		unsigned int nonterminal = 1)
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
	if (!is_parseable<Semantics, Distribution, TerminalPrinter, NonterminalPrinter>(
			syntax, logical_form, G, logical_form_set, printers, token_map, prior, nonterminal))
		return false;
	if (!equivalent(logical_form, logical_form_set)) {
		print("is_parseable ERROR: The parsed logical form is not equivalent to the reference logical form.\n", stderr);
		print("  Reference logical form: ", stderr); print(logical_form, stderr, terminal_printer); print('\n', stderr);
		print("  Parsed logical form:    ", stderr); print(logical_form_set, stderr, terminal_printer); print('\n', stderr);
		return false;
	}
	return true;
}

struct null_semantics {
	enum feature {
		FEATURE_NULL
	};

	enum function_type {
		FUNCTION_EMPTY = 0,
		FUNCTION_IDENTITY = 1,
		FUNCTION_TERMINAL = 2
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

	struct invert_iterator {
		constexpr null_semantics get_next() const {
			return null_semantics();
		}

		static constexpr bool is_empty(const invert_iterator& inverter) {
			return true;
		}

		static inline void free(invert_iterator& inverter) { }
	};

	static inline function terminal_function() {
		return FUNCTION_TERMINAL;
	}

	static constexpr bool initialize_any(const null_semantics& logical_form) { return true; };

	static inline void move(const null_semantics& src, null_semantics& dst) { }
	static inline void swap(null_semantics& src, null_semantics& dst) { }
	static inline void free(const null_semantics& logical_form) { }
};

inline void operator ++ (null_semantics::invert_iterator& inverter, int i) { }

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

template<typename Stream>
inline bool print(const null_semantics::function& function, Stream& out) {
	switch (function.type) {
	case null_semantics::FUNCTION_IDENTITY:
		return print(":identity", out);
	default:
		fprintf(stderr, "print ERROR: Unrecognized null_semantics::function type.\n");
		return false;
	}
}

template<typename Stream, typename Printer>
constexpr bool print(const null_semantics& logical_form, Stream& out, Printer& printer) {
	return true;
}

constexpr bool is_ambiguous(const null_semantics& logical_form) { return false; }

constexpr bool apply(null_semantics::function function, const null_semantics& src, null_semantics& dst) {
	return true;
}

constexpr bool invert(
	null_semantics::invert_iterator& inverter,
	null_semantics::function& function,
	const null_semantics& first_arg,
	const null_semantics& second_arg)
{
	return true;
}

constexpr bool next(const null_semantics::invert_iterator& inverter, null_semantics& dst) {
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

constexpr bool is_separable(const null_semantics::function* functions, unsigned int rule_position) {
	return false;
}

template<typename EmitRootFunction, typename PartOfSpeechType>
inline bool morphology_parse(const sequence& words, PartOfSpeechType pos,
		const null_semantics& logical_form, EmitRootFunction emit_root)
{
	return emit_root(words, logical_form);
}


#endif /* GRAMMAR_H_ */
