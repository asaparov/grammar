/**
 * parser.h
 *
 *  Created on: Jul 15, 2015
 *      Author: asaparov
 */

#ifndef PARSER_H_
#define PARSER_H_

#include <math.h>

constexpr bool USE_SLICE_SAMPLING = false; /* enable/disable slice sampling (only affects sampling) */
constexpr bool USE_BEAM_SEARCH = false; /* enable/disable beam search (only affects parsing) */
constexpr bool USE_NONTERMINAL_PREITERATOR = false; /* use nonterminal_iterator states either before or after completing rule_states */

constexpr unsigned int BEAM_WIDTH = 10000;
constexpr unsigned int PRINT_PROBABILITY_PRECISION = 20;

/* Beta prior parameters for the slice variable */
constexpr double SLICE_ALPHA = 10.0;
constexpr double SLICE_BETA = 1.0;
const double slice_normalization = lgamma(SLICE_ALPHA + SLICE_BETA) - lgamma(SLICE_ALPHA) - lgamma(SLICE_BETA);

#include "grammar.h"

#include <core/map.h>
#include <math/distributions.h>
#include <math/log.h>
#include <mutex>
#include <set>


/* TODO: the following is for debugging; delete it */
string_map_scribe* debug_terminal_printer;
string_map_scribe* debug_nonterminal_printer;
bool debug_flag = false;
bool detect_duplicate_logical_forms = false;

thread_local double minimum_priority = 0.0;


thread_local const char* parser_prefix = "";

using namespace core;

template<typename Semantics>
struct tokenized_sentence
{
	template<typename LabelSemantics, class Enable = void> struct node_label;

	template<typename LabelSemantics>
	struct node_label<LabelSemantics, typename std::enable_if<!std::is_empty<LabelSemantics>::value>::type> {
		unsigned int nonterminal;
		LabelSemantics logical_form;

		node_label(unsigned int nonterminal, const LabelSemantics& logical_form) :
			nonterminal(nonterminal), logical_form(logical_form) { }

		static inline unsigned int hash(const node_label<LabelSemantics>& key) {
			return default_hash(key.nonterminal) ^ LabelSemantics::hash(key.logical_form);
		}

		static inline bool is_empty(const node_label<LabelSemantics>& key) {
			return key.nonterminal == 0;
		}

		static inline void move(const node_label<LabelSemantics>& src, node_label<LabelSemantics>& dst) {
			dst.nonterminal = src.nonterminal;
			core::move(src.logical_form, dst.logical_form);
		}

		static inline void free(node_label<LabelSemantics>& src) {
			core::free(src.logical_form);
		}

		inline bool operator == (const node_label<Semantics>& other) {
			return nonterminal == other.nonterminal
				&& logical_form == other.logical_form;
		}
	};

	template<typename LabelSemantics>
	struct node_label<LabelSemantics, typename std::enable_if<std::is_empty<LabelSemantics>::value>::type> {
		unsigned int nonterminal;

		node_label(unsigned int nonterminal, const LabelSemantics& logical_form) : nonterminal(nonterminal) { }

		static inline unsigned int hash(const node_label<LabelSemantics>& key) {
			return default_hash(key.nonterminal);
		}

		static inline bool is_empty(const node_label<LabelSemantics>& key) {
			return key.nonterminal == 0;
		}

		static inline void move(const node_label<LabelSemantics>& src, node_label<LabelSemantics>& dst) {
			dst.nonterminal = src.nonterminal;
		}

		static inline void free(node_label<LabelSemantics>& src) { }

		inline bool operator == (const node_label<LabelSemantics>& other) {
			return nonterminal == other.nonterminal;
		}
	};

	unsigned int length;
	syntax_node<Semantics>** tokens;
	unsigned int* end_terminal;

	/* cache for storing probabilities of fixed subtrees */
	hash_map<node_label<Semantics>, double>* cache;

	tokenized_sentence(sequence sentence) : length(0), tokens(NULL), end_terminal(NULL), cache(NULL)
	{
		if (!initialize(sentence))
			exit(EXIT_FAILURE);
	}

	tokenized_sentence(syntax_node<Semantics>** token_array, unsigned int count) :
		length(0), tokens(NULL), end_terminal(NULL), cache(NULL)
	{
		if (!initialize(token_array, count))
			exit(EXIT_FAILURE);
	}

	~tokenized_sentence() { free(); }

	template<typename Distribution, typename StringMapType>
	double subtree_probability(
			grammar<Semantics, Distribution>& G,
			unsigned int nonterminal,
			const Semantics& logical_form,
			const StringMapType& token_map,
			unsigned int index)
	{
		if (!cache[index].check_size())
			exit(EXIT_FAILURE);

		bool contains; unsigned int bucket;
		double& probability = cache[index].get(node_label<Semantics>(nonterminal, logical_form), contains, bucket);
		if (!contains) {
			/* cache doesn't contain this entry, so compute and store it */
			probability = log_probability(G, *tokens[index], logical_form, token_map, nonterminal);
			cache[index].table.keys[bucket] = {nonterminal, logical_form};
			cache[index].table.size++;
		}
		return probability;
	}

	static inline void free(tokenized_sentence<Semantics>& sequence) {
		sequence.free();
	}

private:
	inline bool initialize(sequence sentence) {
		if (!resize(sentence.length)) {
			free(); return false;
		}

		for (unsigned int i = 0; i < sentence.length; i++)
		{
			tokens[length] = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
			if (tokens[length] == NULL) {
				fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for syntax_node.\n");
				free(); return false;
			} else if (!init(*tokens[length], {sentence.tokens + i, 1})) {
				fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for cache.\n");
				core::free(tokens[length]);
				free(); return false;
			} else if (!hash_map_init(cache[length], 32)) {
				fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for cache.\n");
				core::free(*tokens[length]); core::free(tokens[length]);
				free(); return false;
			}
			length++;
		}

		for (unsigned int i = 0; i < length; i++)
			end_terminal[i] = length;
		return true;
	}

	inline bool initialize(syntax_node<Semantics>** token_array, unsigned int count) {
		unsigned int capacity = 1 << (core::log2(count) + 2);
		if (!resize(capacity)) {
			free(); return false;
		}

		for (unsigned int i = 0; i < count; i++)
		{
			if (!ensure_capacity(capacity, length + token_array[i]->right.length)) {
				free(); return false;
			}

			if (token_array[i]->is_terminal()) {
				for (unsigned int j = 0; j < token_array[i]->right.length; j++) {
					tokens[length] = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
					if (tokens[length] == NULL) {
						fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for syntax_node.\n");
						free(); return false;
					} else if (!init(*tokens[length], {token_array[i]->right.nonterminals + j, 1})) {
						fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for cache.\n");
						core::free(tokens[length]);
						free(); return false;
					} else if (!hash_map_init(cache[length], 32)) {
						fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for cache.\n");
						core::free(*tokens[length]); core::free(tokens[length]);
						free(); return false;
					}
					length++;
				}
			} else {
				tokens[length] = token_array[i];
				if (!hash_map_init(cache[length], 32)) {
					fprintf(stderr, "tokenized_sentence ERROR: Insufficient memory for cache.\n");
					free(); return false;
				}
				tokens[length]->reference_count++;
				length++;
			}
		}

		unsigned int next_nonterminal = length;
		for (unsigned int i = length; i > 0; i--) {
			if (!tokens[i - 1]->is_terminal())
				next_nonterminal = i - 1;
			end_terminal[i - 1] = next_nonterminal;
		}
		return true;
	}

	inline void free()
	{
		if (tokens != NULL) {
			for (unsigned int j = 0; j < length; j++) {
				if (tokens[j] != NULL)
					core::free(*tokens[j]);
				if (tokens[j] != NULL && tokens[j]->reference_count == 0)
					core::free(tokens[j]);
			}
			core::free(tokens);
		}
		if (cache != NULL) {
			for (unsigned int j = 0; j < length; j++) {
				for (auto entry : cache[j])
					core::free(entry.key);
				core::free(cache[j]);
			}
			core::free(cache);
		}
		if (end_terminal != NULL)
			core::free(end_terminal);
	}

	inline bool ensure_capacity(unsigned int& capacity, unsigned int new_length) {
		if (new_length > capacity) {
			core::expand_capacity(capacity, new_length);
			return resize(capacity);
		}
		return true;
	}

	inline bool resize(unsigned int new_capacity)
	{
		auto new_tokens = (syntax_node<Semantics>**)
				realloc(tokens, sizeof(syntax_node<Semantics>*) * new_capacity);
		auto new_cache = (hash_map<node_label<Semantics>, double>*)
				realloc(static_cast<void*>(cache), sizeof(hash_map<node_label<Semantics>, double>) * new_capacity);
		auto new_end_terminal = (unsigned int*) realloc(
				end_terminal, sizeof(unsigned int) * new_capacity);
		if (new_tokens == NULL || new_cache == NULL || new_end_terminal == NULL) {
			fprintf(stderr, "tokenized_sentence.ensure_capacity ERROR: Out of memory.\n");
			return false;
		}
		tokens = new_tokens;
		cache = new_cache;
		end_terminal = new_end_terminal;
		return true;
	}

	template<typename A>
	friend bool init(tokenized_sentence<A>&, syntax_node<A>**, unsigned int);
};

template<typename Semantics>
inline bool init(tokenized_sentence<Semantics>& tokens, syntax_node<Semantics>** token_array, unsigned int count)
{
	tokens.length = 0; tokens.tokens = NULL;
	tokens.end_terminal = NULL; tokens.cache = NULL;
	return tokens.initialize(token_array, count);
}

enum parse_mode {
	MODE_SAMPLE,
	MODE_PARSE,
	MODE_COMPUTE_BOUNDS,
	MODE_GENERATE
};

/* forward declarations */

template<parse_mode Mode, typename Semantics> struct cell_value;
template<parse_mode Mode, typename Semantics, typename StringMapType> struct chart;
template<parse_mode Mode, typename Semantics, class Enable = void> struct agenda;

struct span {
	unsigned int start;
	unsigned int end;

	inline unsigned int length() const {
		return end - start;
	}
};

template<typename Stream>
inline bool print(const span& positions, Stream& out) {
	return fprintf(out, "[%u, %u]", positions.start, positions.end) >= 0;
}

inline bool is_negative_inf(double value) {
	return (value == -std::numeric_limits<double>::infinity());
}

template<parse_mode Mode, typename Semantics, class Enable = void>
struct syntax_state;

template<parse_mode Mode, typename Semantics>
struct syntax_state<Mode, Semantics, typename std::enable_if<
	Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type>
{
	/* for sampling, we only record the rule */
	rule<Semantics> r;

	syntax_state(const syntax_node<Semantics>* const* terminal_tokens, unsigned int length) :
		r(terminal_tokens, length) { }

	syntax_state(const syntax_node<Semantics>* nonterminal_token) : r(nonterminal_token->right) {
		/* we don't need information about subtree tokens
		   when sampling or computing log probability bounds */
	}

	syntax_state(const sequence& terminal) : r(terminal) { }

	syntax_state(const rule<Semantics>& r) : r(r) { }

	syntax_state(const syntax_state<Mode, Semantics>& src) : r(src.r) { }

	inline rule<Semantics>& get_rule() {
		return r;
	}

	inline const rule<Semantics>& get_rule() const {
		return r;
	}

	inline const syntax_node<Semantics>& get_tree() const {
		fprintf(stderr, "syntax_state.get_tree ERROR: This function can only be called in PARSE mode.\n");
		exit(EXIT_FAILURE);
	}

	inline bool operator == (const syntax_state<Mode, Semantics>& other) const {
		return r == other.r;
	}

	static inline void free(syntax_state<Mode, Semantics>& state) {
		core::free(state.r);
	}
};

template<parse_mode Mode, typename Semantics>
struct syntax_state<Mode, Semantics, typename std::enable_if<
	Mode == MODE_PARSE || Mode == MODE_GENERATE>::type>
{
	syntax_node<Semantics> tree;

	syntax_state(const syntax_node<Semantics>* const* terminal_tokens, unsigned int length) :
		tree(terminal_tokens, length) { }

	syntax_state(const syntax_node<Semantics>* nonterminal_token) : tree(*nonterminal_token) { }

	syntax_state(const sequence& terminal) : tree(terminal) { }

	syntax_state(const rule<Semantics>& r) : tree(r) { }

	syntax_state(const syntax_state<Mode, Semantics>& src) : tree(src.tree) { }

	inline rule<Semantics>& get_rule() {
		return tree.right;
	}

	inline const rule<Semantics>& get_rule() const {
		return tree.right;
	}

	inline const syntax_node<Semantics>& get_tree() const {
		return tree;
	}

	inline bool operator == (const syntax_state<Mode, Semantics>& other) const {
		return tree == other.tree;
	}

	static inline void free(syntax_state<Mode, Semantics>& state) {
		core::free(state.tree);
	}
};

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline bool init(syntax_state<Mode, Semantics>& state, const rule<Semantics>& r)
{
	state.r = r;
	return true;
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline bool init(
	syntax_state<Mode, Semantics>& state,
	const syntax_state<Mode, Semantics>& src)
{
	state.r = src.r;
	return true;
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline bool init(syntax_state<Mode, Semantics>& state, const rule<Semantics>& r) {
	return init(state.tree, r);
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline bool init(
	syntax_state<Mode, Semantics>& state,
	const syntax_state<Mode, Semantics>& src)
{
	return init(state.tree, src.tree);
}

template<parse_mode Mode, typename Semantics, typename Stream, typename NonterminalPrinter, typename TerminalPrinter,
	typename std::enable_if<Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline bool print(const syntax_state<Mode, Semantics>& syntax, Stream& stream,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	return print(syntax.r, stream, make_pair<TerminalPrinter&, NonterminalPrinter&>(terminal_printer, nonterminal_printer));
}

template<parse_mode Mode, typename Semantics, typename Stream, typename NonterminalPrinter, typename TerminalPrinter,
	typename std::enable_if<Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline bool print(
		const syntax_state<Mode, Semantics>& syntax, Stream& stream, unsigned int indent,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer) {
	return print(syntax, stream, nonterminal_printer, terminal_printer);
}

template<parse_mode Mode, typename Semantics, typename Stream, typename NonterminalPrinter, typename TerminalPrinter,
	typename std::enable_if<Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline bool print(
		const syntax_state<Mode, Semantics>& syntax, Stream& stream, unsigned int indent,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	return print(syntax.tree, stream, indent, nonterminal_printer, terminal_printer);
}

template<parse_mode Mode, typename Semantics, typename Stream, typename NonterminalPrinter, typename TerminalPrinter,
	typename std::enable_if<Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline bool print(const syntax_state<Mode, Semantics>& syntax, Stream& stream,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer) {
	return print(syntax.tree, stream, 0, nonterminal_printer, terminal_printer);
}

template<parse_mode Mode, typename Semantics>
struct rule_state {
	syntax_state<Mode, Semantics> syntax;
	double log_probability;
	cell_value<Mode, Semantics>* cell;
	Semantics logical_form_set; /* TODO: the logical form is unnecessary in syntactic parsing */
	unsigned int rule_position;
	unsigned int nonterminal;

	/* sentence positions */
	unsigned int* positions;

	/* TODO: do we need reference counting? is it actually faster than only
	   freeing unique rule states in the chart? (which involves keeping a hash
	   set of freed rule states) */
	unsigned int reference_count;

	static inline void free(rule_state<Mode, Semantics>& state) {
		state.reference_count--;
		if (state.reference_count == 0) {
			core::free(state.syntax);
			if (Mode != MODE_COMPUTE_BOUNDS)
				core::free(state.logical_form_set);
			if (Mode != MODE_GENERATE)
				core::free(state.positions);
		}
	}
};

template<parse_mode Mode, typename Semantics>
inline bool init(rule_state<Mode, Semantics>& state,
	unsigned int nonterminal, const rule<Semantics>& r, span position)
{
#if !defined(NDEBUG)
	if (r.is_terminal())
		fprintf(stderr, "init WARNING: A terminal rule was specified when initializing rule_state.\n");
#endif
	state.nonterminal = nonterminal;
	if (Mode != MODE_GENERATE) {
		state.positions = (unsigned int*) malloc(sizeof(unsigned int) * (r.nt.length + 1));
		if (state.positions == NULL) {
			fprintf(stderr, "init ERROR: Unable to initialize position array in new rule_state.\n");
			return false;
		}
		state.positions[0] = position.start;
		state.positions[r.nt.length] = position.end;
	}
	if (!init(state.syntax, r)) {
		if (Mode != MODE_GENERATE) free(state.positions);
		return false;
	}

	state.reference_count = 1;
	return true;
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_SAMPLE || Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline bool add_child(
	syntax_state<Mode, Semantics>& state,
	const syntax_state<Mode, Semantics>& child,
	unsigned int rule_position)
{
	return true;
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<
	Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline bool add_child(
	syntax_state<Mode, Semantics>& state,
	const syntax_state<Mode, Semantics>& child,
	unsigned int rule_position)
{
	state.tree.children[rule_position] =
		(syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
	if (state.tree.children[rule_position] == NULL) {
		fprintf(stderr, "add_child ERROR: Out of memory.\n");
		return false;
	}
	*state.tree.children[rule_position] = child.tree;
	return true;
}

template<parse_mode Mode, typename Semantics>
inline bool init(
	rule_state<Mode, Semantics>& state,
	const rule_state<Mode, Semantics>& src,
	const syntax_state<Mode, Semantics>& syntax)
{
	const rule<Semantics>& rule = src.syntax.get_rule();
#if !defined(NDEBUG)
	if (rule.is_terminal())
		fprintf(stderr, "init WARNING: A terminal rule was specified when initializing rule_state.\n");
#endif

	state.nonterminal = src.nonterminal;
	state.log_probability = src.log_probability;
	if (Mode != MODE_GENERATE) {
		state.positions = (unsigned int*) malloc(sizeof(unsigned int) * (rule.nt.length + 1));
		if (state.positions == NULL) {
			fprintf(stderr, "init ERROR: Unable to initialize position array in new rule_state.\n");
			return false;
		}
		for (unsigned int i = 0; i < src.rule_position + 2; i++)
			state.positions[i] = src.positions[i];
		state.positions[rule.nt.length] = src.positions[rule.nt.length];
	}

	if (!init(state.syntax, src.syntax)) {
		if (Mode != MODE_GENERATE) free(state.positions);
		return false;
	} else if (!add_child(state.syntax, syntax, src.rule_position)) {
		if (Mode != MODE_GENERATE) free(state.positions);
		free(state.syntax);
		return false;
	}
	state.reference_count = 1;
	return true;
}

template<typename Stream>
inline bool print_rule_positions(const unsigned int* positions,
		unsigned int rule_position, unsigned int rule_length, Stream& out)
{
	if (!print('[', out)) return false;
	if (rule_length == 0)
		return print(']', out);
	if (!print(positions[0], out)) return false;
	for (unsigned int i = 1; i <= rule_position + 1; i++) {
		if (!print(", ", out) || !print(positions[i], out))
			return false;
	}
	if (rule_position + 1 == rule_length) {
		return print(']', out);
	} else if (rule_position + 1 < rule_length && rule_length > 2)
		if (!print(", ...", out)) return false;
	return print(", ", out) && print(positions[rule_length], out) && print(']', out);
}

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(
		const rule_state<Mode, Semantics>& state, Stream& out, unsigned int indent,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	const rule<Semantics>& r = state.syntax.get_rule();
	return print("nonterminal = ", out) && print(state.nonterminal, out, nonterminal_printer)
		&& print('\n', out) && print_indent(indent, out) && print("syntax: ", out) && print(state.syntax, out, indent, nonterminal_printer, terminal_printer)
		&& (Mode == MODE_COMPUTE_BOUNDS || (print('\n', out) && print_indent(indent, out) && print("logical_form: ", out) && print(state.logical_form_set, out, terminal_printer)))
		&& print('\n', out) && print_indent(indent, out) && print("log_probability: ", out) && print(state.log_probability, out, PRINT_PROBABILITY_PRECISION)
		&& print('\n', out) && print_indent(indent, out) && print("rule_position: ", out) && print(state.rule_position, out)
		&& (Mode == MODE_GENERATE || (print('\n', out) && print_indent(indent, out) && print("positions: ", out) && print_rule_positions(state.positions, state.rule_position, r.nt.length, out)));
}

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const rule_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer) {
	return print(state, out, 0, nonterminal_printer, terminal_printer);
}

template<parse_mode Mode, typename Semantics>
struct nonterminal_state {
	double log_probability;
	syntax_state<Mode, Semantics> syntax;
	Semantics logical_form_set; /* TODO: the logical form is unnecessary in syntactic parsing */
	unsigned int* positions;

#if !defined(NDEBUG)
	unsigned int iteration;
#endif

	static inline void free(nonterminal_state<Mode, Semantics>& state) {
		core::free(state.syntax);
		if (Mode != MODE_COMPUTE_BOUNDS)
			core::free(state.logical_form_set);
		if (Mode != MODE_GENERATE)
			core::free(state.positions);
	}
};

template<parse_mode Mode, typename Semantics>
inline bool init(nonterminal_state<Mode, Semantics>& state,
	const syntax_state<Mode, Semantics>& syntax,
	const unsigned int* positions,
	const Semantics& logical_form_set,
	double priority)
{
	const rule<Semantics>& rule = syntax.get_rule();

	if (Mode != MODE_GENERATE) {
		state.positions = (unsigned int*) malloc(
			sizeof(unsigned int) * (rule.is_terminal() ? 2 : (rule.nt.length + 1)));
		if (state.positions == NULL) return false;
		memcpy(state.positions, positions,
			sizeof(unsigned int) * (rule.is_terminal() ? 2 : (rule.nt.length + 1)));
	}
	state.log_probability = priority;
	if (!init(state.syntax, syntax)) {
		if (Mode != MODE_GENERATE) free(state.positions);
		return false;
	}
	if (Mode != MODE_COMPUTE_BOUNDS)
		state.logical_form_set = logical_form_set;
	return true;
}

/* for computing logsumexp of an array of nonterminal_states */
template<typename Semantics>
inline double log_probability(const nonterminal_state<MODE_SAMPLE, Semantics>& state) {
	return state.log_probability;
}

template<parse_mode Mode, typename Semantics>
struct nonterminal_iterator_state
{
	unsigned int nonterminal;
	syntax_state<Mode, Semantics> syntax;
	cell_value<Mode, Semantics>* cell;
	unsigned int* positions;

	weighted<Semantics>* posterior;
	unsigned int posterior_length;
	unsigned int iterator;

	static inline void free(nonterminal_iterator_state<Mode, Semantics>& state) {
		core::free(state.syntax);
		if (Mode != MODE_GENERATE)
			core::free(state.positions);
		for (unsigned int i = 0; i < state.posterior_length; i++)
			core::free(state.posterior[i]);
		core::free(state.posterior);
	}
};

template<parse_mode Mode, typename Semantics, typename StringMapType>
inline bool init(
	nonterminal_iterator_state<Mode, Semantics>& state,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	unsigned int nonterminal, double inner_probability,
	const syntax_state<Mode, Semantics>& syntax,
	weighted<Semantics>* posterior,
	unsigned int posterior_length,
	cell_value<Mode, Semantics>* cell,
	unsigned int* positions)
{
	const rule<Semantics>& rule = syntax.get_rule();
	state.nonterminal = nonterminal;
	state.cell = cell;
	state.posterior_length = posterior_length;
	state.posterior = posterior;

	unsigned int length = rule.is_terminal() ? 2 : (rule.nt.length + 1);
	if (Mode != MODE_GENERATE) {
		state.positions = (unsigned int*) malloc(sizeof(unsigned int) * length);
		if (state.positions == NULL) {
			fprintf(stderr, "init ERROR: Unable to initialize "
					"position array in new nonterminal_iterator_state.\n");
			return false;
		}
		memcpy(state.positions, positions, sizeof(unsigned int) * length);
	}

	if (!init(state.syntax, syntax)) {
		if (Mode != MODE_GENERATE) free(state.positions);
		return false;
	}
	for (unsigned int i = 0; i < posterior_length; i++) {
		posterior[i].log_probability += inner_probability;
		double old_prior = 0.0;
		if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
			old_prior = min(log_probability<false>(posterior[i].object), cell->prior_probability);
		if (USE_NONTERMINAL_PREITERATOR) {
			double right, prior = old_prior;
			if (!rule.is_terminal() && (Mode == MODE_PARSE || Mode == MODE_GENERATE)) {
				right_probability(rule, posterior[i].object, positions, parse_chart, old_prior, right, prior);
				posterior[i].log_probability += right;
			} else if (Mode != MODE_SAMPLE) {
				posterior[i].log_probability += old_prior;
			}
		} else {
			posterior[i].log_probability += old_prior;
		}
	}
	if (state.posterior_length > 1)
		sort(state.posterior, state.posterior_length, default_sorter());
	while (state.posterior_length > 0) {
		if (!std::isinf(posterior[state.posterior_length - 1].log_probability))
			break;
		free(posterior[state.posterior_length - 1]);
		state.posterior_length--;
	}
	return true;
}

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const nonterminal_iterator_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	const rule<Semantics>& r = state.syntax.get_rule();
	unsigned int length = r.is_terminal() ? 2 : (r.nt.length + 1);
	return print("nonterminal = ", out) && print(state.nonterminal, out, nonterminal_printer)
		&& print("\nnext logical form: ", out) && print(state.posterior[state.iterator].object, out, terminal_printer)
		&& print("\nnext log probability: ", out) && print(state.posterior[state.iterator].log_probability, out, PRINT_PROBABILITY_PRECISION)
		&& print("\nsyntax: ", out) && print(state.syntax, out, nonterminal_printer, terminal_printer)
		&& (Mode == MODE_GENERATE || (print("\npositions: ", out) && print(state.positions, length, out)));
}

template<parse_mode Mode, typename Semantics>
struct invert_iterator_state {
	rule_state<Mode, Semantics>* rule;
	Semantics* inverse; /* TODO: the inverter is unnecessary in syntactic parsing */
	unsigned int inverse_count;
	unsigned int index;
	syntax_state<Mode, Semantics> syntax; /* TODO: during sampling, this field is unnecessary */
	double log_probability;

	static inline void free(invert_iterator_state<Mode, Semantics>& state)
	{
		if (Mode != MODE_COMPUTE_BOUNDS) {
			for (unsigned int i = 0; i < state.inverse_count; i++)
				core::free(state.inverse[i]);
			core::free(state.inverse);
		}
		core::free(state.syntax);
		core::free(*state.rule);
		if (state.rule->reference_count == 0)
			core::free(state.rule);
	}
};

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const invert_iterator_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	return print("\nlog_probability: ", out) && print(state.log_probability, out, PRINT_PROBABILITY_PRECISION)
		&& (Mode == MODE_COMPUTE_BOUNDS || (print("\ninverted logical form: ", out) && print(state.inverse[state.index], out, terminal_printer)))
		&& print("\nsyntax: ", out) && print(state.syntax, out, nonterminal_printer, terminal_printer)
		&& print("\nrule state: ", out) && print(*state.rule, out, 1, nonterminal_printer, terminal_printer);
}

template<parse_mode Mode, typename Semantics>
struct rule_completer_state {
	cell_value<Mode, Semantics>* cell;
	Semantics logical_form_set; /* TODO: the logical form is unnecessary in syntactic parsing */
	syntax_state<Mode, Semantics> syntax; /* TODO: during sampling, this field is unnecessary */
	double log_probability;
	span position;

	const array<rule_state<Mode, Semantics>*>* waiting_states;
	unsigned int iterator;

	static inline void free(rule_completer_state<Mode, Semantics>& state) {
		if (Mode != MODE_COMPUTE_BOUNDS)
			core::free(state.logical_form_set);
		core::free(state.syntax);
	}
};

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const rule_completer_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	return print("\nlog_probability: ", out) && print(state.log_probability, out, PRINT_PROBABILITY_PRECISION)
		&& print("\nlogical_form: ", out) && print(state.logical_form_set, out, terminal_printer)
		&& print("\nsyntax: ", out) && print(state.syntax, out, nonterminal_printer, terminal_printer)
		&& (Mode == MODE_GENERATE || (print("\nposition: ", out) && print(state.position, out)))
		&& print("\nwaiting state: ", out) && print(*state.waiting_states->data[state.iterator], out, 1, nonterminal_printer, terminal_printer);
}

template<typename Semantics>
inline void completer_log_probability(
	rule_completer_state<MODE_SAMPLE, Semantics>& completer,
	const array<nonterminal_state<MODE_SAMPLE, Semantics>>& nonterminals)
{
	completer.log_probability = logsumexp(nonterminals.data, (unsigned int) nonterminals.length);
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline void completer_log_probability(
	rule_completer_state<Mode, Semantics>& completer,
	const array<nonterminal_state<Mode, Semantics>>& nonterminals)
{ }

/* for iterating over terminals in order of descending probability during generation */
template<parse_mode Mode, typename Semantics>
struct terminal_iterator_state
{
	unsigned int nonterminal;
	cell_value<Mode, Semantics>* cell;
	Semantics logical_form;

	weighted<sequence>* terminals;
	unsigned int terminal_count;
	unsigned int iterator;

	static inline void free(terminal_iterator_state<Mode, Semantics>& state) {
		for (unsigned int i = 0; i < state.terminal_count; i++)
			core::free(state.terminals[i]);
		core::free(state.terminals);
		core::free(state.logical_form);
	}
};

template<parse_mode Mode, typename Semantics>
bool init(terminal_iterator_state<Mode, Semantics>& iterator,
		unsigned int nonterminal, cell_value<Mode, Semantics>* cell,
		const Semantics& logical_form, weighted<sequence>* terminals,
		unsigned int terminal_count)
{
	iterator.nonterminal = nonterminal;
	iterator.cell = cell;
	iterator.terminals = terminals;
	iterator.terminal_count = terminal_count;
	iterator.iterator = 0;
	iterator.logical_form = logical_form;
	return true;
}

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const terminal_iterator_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	return print("nonterminal = ", out) && print(state.nonterminal, out, nonterminal_printer)
		&& print("\nlogical form: ", out) && print(state.logical_form, out, terminal_printer)
		&& print("\nnext terminal: ", out) && print(state.terminals[state.iterator].object, out, terminal_printer)
		&& print("\nnext log probability: ", out) && print(state.terminals[state.iterator].log_probability, out, PRINT_PROBABILITY_PRECISION);
}

enum search_phase {
	PHASE_RULE,
	PHASE_TERMINAL_ITERATOR,
	PHASE_NONTERMINAL_ITERATOR,
	PHASE_INVERT_ITERATOR,
	PHASE_RULE_COMPLETER
};

template<parse_mode Mode, typename Semantics>
struct parser_search_state {
	double priority;
	search_phase phase;
	union {
		rule_state<Mode, Semantics>* rule;
		terminal_iterator_state<Mode, Semantics>* terminal_iterator;
		nonterminal_iterator_state<Mode, Semantics>* nonterminal_iterator;
		invert_iterator_state<Mode, Semantics>* invert_iterator;
		rule_completer_state<Mode, Semantics>* rule_completer;
	};

#if !defined(NDEBUG)
	unsigned int iteration;
#endif

	inline double get_priority() const {
		return priority;
	}

	static inline void free(parser_search_state<Mode, Semantics>& state) {
		switch (state.phase) {
		case PHASE_RULE:
			core::free(*state.rule);
			if (state.rule->reference_count == 0)
				core::free(state.rule);
			break;
		case PHASE_TERMINAL_ITERATOR:
			core::free(*state.terminal_iterator); core::free(state.terminal_iterator); break;
		case PHASE_NONTERMINAL_ITERATOR:
			core::free(*state.nonterminal_iterator); core::free(state.nonterminal_iterator); break;
		case PHASE_INVERT_ITERATOR:
			core::free(*state.invert_iterator); core::free(state.invert_iterator); break;
		case PHASE_RULE_COMPLETER:
			break;
		}
	}
};

template<parse_mode Mode, typename Semantics>
inline bool operator < (
	const parser_search_state<Mode, Semantics>& first,
	const parser_search_state<Mode, Semantics>& second)
{
	if (first.get_priority() < second.get_priority()) return true;
	else if (first.get_priority() > second.get_priority()) return false;
	return (first.phase == PHASE_RULE_COMPLETER && second.phase != PHASE_RULE_COMPLETER);
}

template<parse_mode Mode, typename Semantics, typename Stream>
inline bool print_iteration(const parser_search_state<Mode, Semantics>& state, Stream& out)
{
#if !defined(NDEBUG)
	fprintf(stderr, "\n(created on iteration %u)", state.iteration);
#endif
	return true;
}

template<parse_mode Mode, typename Semantics, typename Stream,
	typename NonterminalPrinter, typename TerminalPrinter>
inline bool print(const parser_search_state<Mode, Semantics>& state, Stream& out,
		NonterminalPrinter& nonterminal_printer, TerminalPrinter& terminal_printer)
{
	switch (state.phase) {
	case PHASE_RULE:
		return print("RULE STATE: ", out) && print(*state.rule, out, nonterminal_printer, terminal_printer) && print_iteration(state, out);
	case PHASE_TERMINAL_ITERATOR:
		return print("TERMINAL STATE: ", out) && print(*state.terminal_iterator, out, nonterminal_printer, terminal_printer) && print_iteration(state, out);
	case PHASE_NONTERMINAL_ITERATOR:
		return print("NONTERMINAL STATE: ", out) && print(*state.nonterminal_iterator, out, nonterminal_printer, terminal_printer) && print_iteration(state, out);
	case PHASE_INVERT_ITERATOR:
		return print("INVERT STATE: ", out) && print(*state.invert_iterator, out, nonterminal_printer, terminal_printer) && print_iteration(state, out);
	case PHASE_RULE_COMPLETER:
		return print("RULE COMPLETER STATE: ", out) && print(*state.rule_completer, out, nonterminal_printer, terminal_printer) && print_iteration(state, out);
	}
	fprintf(stderr, "print ERROR: Unrecognized search_phase.\n");
	return false;
}

template<parse_mode Mode, typename Semantics>
struct agenda<Mode, Semantics> {
	std::multiset<parser_search_state<Mode, Semantics>> queue;
	double last_priority;
	unsigned int iteration;

	agenda() : last_priority(std::numeric_limits<double>::infinity()), iteration(0) { }

	~agenda() {
		for (parser_search_state<Mode, Semantics> state : queue)
			free(state);
	}

	inline bool is_empty() const {
		return queue.empty();
	}

	inline unsigned int size() const {
		return queue.size();
	}

	inline void push(
			parser_search_state<Mode, Semantics>& new_state,
			cell_value<Mode, Semantics>& cell)
	{
#if !defined(NDEBUG)
		new_state.iteration = iteration;
#endif
		queue.insert(new_state);
	}

	inline parser_search_state<Mode, Semantics> pop(unsigned int iteration) {
		auto last = queue.cend(); last--;
		parser_search_state<Mode, Semantics> state = *last;
		queue.erase(last);

//#if !defined(NDEBUG)
		if (Mode != MODE_SAMPLE && state.priority > last_priority + 1.0e-12)
			fprintf(stderr, "%sparse WARNING: Search is not monotonic. (iteration %u)\n", parser_prefix, iteration);
		last_priority = state.priority;
//#endif
		return state;
	}

	inline double priority(const cell_value<Mode, Semantics>& cell) {
		return last_priority;
	}

	inline void prune_beam() {
		while (queue.size() > BEAM_WIDTH) {
			auto first = queue.cbegin();
			parser_search_state<Mode, Semantics> state = *first;
			free(state);
			queue.erase(first);
		}
	}
};

template<parse_mode Mode, typename Semantics, bool UseSliceSampling = USE_SLICE_SAMPLING, class Enable = void>
struct cell_variables;

template<typename Semantics>
struct cell_variables<MODE_SAMPLE, Semantics, true> {
	/* variable for slice sampling */
	double slice_variable;
	double slice_beta; /* log of beta density of the slice variable */

	inline double get_slice_variable() const {
		return slice_variable;
	}

	inline void init_slice_variable()
	{
		if (slice_variable != -1.0)
			return;

		init_slice_variable(sample_beta(SLICE_ALPHA, SLICE_BETA));
	}

	inline void init_slice_variable(double beta)
	{
#if !defined(NDEBUG)
		if (isnan(beta)) {
			fprintf(stderr, "cell_variables.init_slice_variable ERROR: Slice parameter is NaN.\n");
			slice_variable = 0.0;
			return;
		}
#endif

		slice_variable = beta;
		slice_beta = slice_normalization
			+ (SLICE_ALPHA - 1.0) * log(beta)
			+ (SLICE_BETA - 1.0) * log(1.0 - beta);
	}

	inline double get_inner_probability() const {
		fprintf(stderr, "cell_variables.get_inner_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_probability(double inner) {
		fprintf(stderr, "cell_variables.set_inner_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_inner_prior_probability() const {
		fprintf(stderr, "cell_variables.get_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_prior_probability(double prior) {
		fprintf(stderr, "cell_variables.set_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_initial_prior_probability() const {
		fprintf(stderr, "cell_variables.get_initial_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline const double get_outer_probability() const {
		fprintf(stderr, "cell_variables.get_outer_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_outer_probability(double outer) {
		fprintf(stderr, "cell_variables.set_outer_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline bool initialize(double inner, double inner_prior, double initial_prior) {
		slice_variable = -1.0;
		return true;
	}

	static inline void free(cell_variables<MODE_SAMPLE, Semantics>& vars) { }
};

template<typename Semantics>
struct cell_variables<MODE_SAMPLE, Semantics, false>
{
	constexpr double get_slice_variable() const { return 0.0; }
	inline void init_slice_variable() { }
	inline void init_slice_variable(double beta) { }

	inline double get_inner_probability() const {
		fprintf(stderr, "cell_variables.get_inner_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_probability(double inner) {
		fprintf(stderr, "cell_variables.set_inner_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_inner_prior_probability() const {
		fprintf(stderr, "cell_variables.get_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_prior_probability(double prior) {
		fprintf(stderr, "cell_variables.set_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_initial_prior_probability() const {
		fprintf(stderr, "cell_variables.get_initial_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline const double get_outer_probability() const {
		fprintf(stderr, "cell_variables.get_outer_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_outer_probability(double outer) {
		fprintf(stderr, "cell_variables.set_outer_probability ERROR:"
			" This function cannot be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	constexpr bool initialize(double inner, double inner_prior, double initial_prior) const { return true; }
	static inline void free(cell_variables<MODE_SAMPLE, Semantics>& vars) { }
};

template<typename Semantics>
struct cell_variables<MODE_PARSE, Semantics>
{
	double inner_probability;
	double inner_prior_probability;
	double outer_probability;
	double initial_prior_probability;

	inline double get_slice_variable() const {
		fprintf(stderr, "cell_variables.get_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void init_slice_variable() const {
		fprintf(stderr, "cell_variables.init_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_inner_probability() const {
		return inner_probability;
	}

	inline void set_inner_probability(double inner) {
		inner_probability = inner;
	}

	inline double get_inner_prior_probability() const {
		return inner_prior_probability;
	}

	inline void set_inner_prior_probability(double prior) {
		inner_prior_probability = prior;
	}

	inline double get_initial_prior_probability() const {
		return initial_prior_probability;
	}

	inline double get_outer_probability() const {
		return outer_probability;
	}

	inline void set_outer_probability(double outer) {
		outer_probability = outer;
	}

	inline bool initialize(double inner, double inner_prior, double initial_prior)
	{
		inner_probability = inner;
		inner_prior_probability = inner_prior;
		initial_prior_probability = initial_prior;
		return true;
	}

	static inline void free(cell_variables<MODE_PARSE, Semantics>& vars) { }
};

template<typename Semantics>
struct cell_variables<MODE_COMPUTE_BOUNDS, Semantics>
{
	double inner_probability;
	double outer_probability;

	inline double get_slice_variable() const {
		fprintf(stderr, "cell_variables.get_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void init_slice_variable() const {
		fprintf(stderr, "cell_variables.init_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_inner_probability() const {
		return inner_probability;
	}

	inline void set_inner_probability(double inner) {
		inner_probability = inner;
	}

	inline double get_inner_prior_probability() const {
		fprintf(stderr, "cell_variables.get_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_prior_probability(double prior) {
		fprintf(stderr, "cell_variables.set_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_initial_prior_probability() const {
		fprintf(stderr, "cell_variables.get_initial_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_outer_probability() const {
		return outer_probability;
	}

	inline void set_outer_probability(double outer) {
		outer_probability = outer;
	}

	inline bool initialize(double inner, double inner_prior, double initial_prior) {
		inner_probability = inner;
		return true;
	}

	static inline void free(cell_variables<MODE_COMPUTE_BOUNDS, Semantics>& vars) { }
};

template<parse_mode Mode, typename Semantics>
struct cell_variables<Mode, Semantics, USE_SLICE_SAMPLING,
	typename std::enable_if<Mode != MODE_SAMPLE && Mode != MODE_PARSE && Mode != MODE_COMPUTE_BOUNDS>::type>
{
	double inner_probability;
	double outer_probability;

	inline double get_slice_variable() const {
		fprintf(stderr, "cell_variables.get_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void init_slice_variable() const {
		fprintf(stderr, "cell_variables.init_slice_variable ERROR:"
			" This function can only be called in sampling mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_inner_probability() const {
		return inner_probability;
	}

	inline void set_inner_probability(double inner) {
		inner_probability = inner;
	}

	inline double get_inner_prior_probability() const {
		fprintf(stderr, "cell_variables.get_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline void set_inner_prior_probability(double prior) {
		fprintf(stderr, "cell_variables.set_inner_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_initial_prior_probability() const {
		fprintf(stderr, "cell_variables.get_initial_prior_probability ERROR:"
			" This function can only be called in parsing mode.\n");
		exit(EXIT_FAILURE);
	}

	inline double get_outer_probability() const {
		return outer_probability;
	}

	inline void set_outer_probability(double outer) {
		outer_probability = outer;
	}

	inline bool initialize(double inner, double inner_prior, double initial_prior) {
		inner_probability = inner;
		return true;
	}

	static inline bool copy(const cell_variables<Mode, Semantics>& src, cell_variables<Mode, Semantics>& dst) {
		dst.inner_probability = src.outer_probability;
		dst.outer_probability = src.outer_probability;
		return true;
	}

	static inline void free(cell_variables<Mode, Semantics>& vars) { }
};

template<parse_mode Mode, typename Semantics>
struct cell_value {
	cell_variables<Mode, Semantics> var;
	double prior_probability;
	bool expanded;

	/* waiting rule states */
	array<rule_state<Mode, Semantics>*> waiting_states;

	/* completed nonterminal states */
	array<nonterminal_state<Mode, Semantics>> completed;

	rule_completer_state<Mode, Semantics>* completer;

	/**
	 * When the prior is non-zero, a previously-expanded cell can be re-
	 * expanded with a larger log likelihood. Monotonicity ensures that the
	 * quantity log likelihood + log prior is non-increasing, the same is not
	 * guaranteed for the likelihood. When this happens, we re-expand the cell
	 * and store the new cell in a linked list whose root is the originally
	 * expanded cell.
	 */
	cell_value<Mode, Semantics>* next;

	template<bool AllowAmbiguous, unsigned int K>
	inline bool has_completed_parses(
			double search_log_probability,
			unsigned int& completed_derivations,
			double(&best_derivation_probabilities)[K]) const
	{
		if (best_derivation_probabilities[0] >= search_log_probability)
			return true;

		for (; completed_derivations < completed.length; completed_derivations++) {
			const auto& parse = completed[completed_derivations];
			double total_log_probability = parse.log_probability;
			if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
				total_log_probability += log_probability<true>(parse.logical_form_set);
			unsigned int index = linear_search(best_derivation_probabilities, total_log_probability, 0, K);
			if (index == 0 || (!AllowAmbiguous && is_ambiguous(parse.logical_form_set)))
				continue;
			shift_left(best_derivation_probabilities, index - 1);
			best_derivation_probabilities[index - 1] = total_log_probability;
			if (best_derivation_probabilities[0] >= search_log_probability) {
				return true;
			}
		}
		return false;
	}

	template<bool AllowAmbiguous, unsigned int K = 1>
	inline unsigned int get_best_parse(const nonterminal_state<Mode, Semantics>** best) const
	{
		array<pair<double, const nonterminal_state<Mode, Semantics>*>> derivations(32);
		if (completed.length == 0)
			return 0;

		for (const nonterminal_state<Mode, Semantics>& parse : completed) {
			double total_log_probability = parse.log_probability;
			if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
				total_log_probability += log_probability<true>(parse.logical_form_set);
			if (AllowAmbiguous || !is_ambiguous(parse.logical_form_set))
				derivations.add({total_log_probability, &parse});
		}

		if (derivations.length == 0)
			return 0;
		sort(derivations);

		unsigned int length = 0;
		for (unsigned int i = derivations.length; i > 0 && length < K; i--) {
			best[length] = derivations[i - 1].value;
			length++;
		}
		return length;
	}

	static inline bool copy(const cell_value<Mode, Semantics>& src, cell_value<Mode, Semantics>& dst)
	{
		if (src.completer == NULL) {
			dst.completer = NULL;
		} else {
			dst.completer = (rule_completer_state<Mode, Semantics>*) malloc(sizeof(rule_completer_state<Mode, Semantics>));
			if (dst.completer == NULL) return false;
			dst.completer->cell = src.completer->cell;
			dst.completer->iterator = src.completer->iterator;
			dst.completer->log_probability = src.completer->log_probability;
			dst.completer->logical_form_set = src.completer->logical_form_set;
			dst.completer->position = src.completer->position;
			dst.completer->waiting_states = src.completer->waiting_states;
		}

		dst.expanded = src.expanded;
		if (!array_init(dst.waiting_states, max<size_t>(1, src.waiting_states.length))) {
			core::free(*dst.completer); core::free(dst.completer);
			return false;
		} else if (!array_init(dst.completed, max<size_t>(1, src.completed.length))) {
			core::free(*dst.completer); core::free(dst.completer);
			core::free(dst.waiting_states);
			return false;
		} else if (!cell_variables<Mode, Semantics>::copy(src.var, dst.var)) {
			free(dst);
			return false;
		}

		for (rule_state<Mode, Semantics>* waiting_state : src.waiting_states) {
			dst.waiting_states[dst.waiting_states.length] = waiting_state;
			waiting_state->reference_count++;
			dst.waiting_states.length++;
		}
		for (const nonterminal_state<Mode, Semantics>& nonterminal : src.completed) {
			if (!init(dst.completed[dst.completed.length], nonterminal.syntax, nonterminal.positions,
					nonterminal.logical_form_set, nonterminal.log_probability))
			{
				free(dst);
				return false;
			}
#if !defined(NDEBUG)
			dst.completed[dst.completed.length].iteration = nonterminal.iteration;
#endif
			dst.completed.length++;
		}
		return true;
	}

	static inline void free(cell_value<Mode, Semantics>& cell)
	{
		for (nonterminal_state<Mode, Semantics>& state : cell.completed)
			core::free(state);
		for (rule_state<Mode, Semantics>* rule : cell.waiting_states) {
			core::free(*rule);
			if (rule->reference_count == 0)
				core::free(rule);
		}
		if (cell.completer != NULL) {
			core::free(*cell.completer);
			core::free(cell.completer);
		}
		core::free(cell.var);
		core::free(cell.waiting_states);
		core::free(cell.completed);
		if (cell.next != NULL) {
			core::free(*cell.next);
			core::free(cell.next);
		}
	}
};

template<parse_mode Mode, typename Semantics>
inline bool init(cell_value<Mode, Semantics>& cell,
		double inner_probability, double inner_prior_probability,
		double initial_prior_probability)
{
	cell.prior_probability = 0.0;
	if (!array_init(cell.waiting_states, 8)) {
		return false;
	} else if (!array_init(cell.completed, 8)) {
		free(cell.waiting_states);
		return false;
	}
	cell.var.initialize(inner_probability, inner_prior_probability, initial_prior_probability);
	cell.completer = NULL;
	cell.next = NULL;
	cell.expanded = false;
	return true;
}


template<parse_mode Mode, typename Semantics, class Enable = void> struct cell_list;

template<parse_mode Mode, typename Semantics>
struct cell_list<Mode, Semantics,
	typename std::enable_if<Mode == MODE_COMPUTE_BOUNDS || std::is_empty<Semantics>::value>::type>
{
	cell_value<Mode, Semantics> cell;

	/* NOTE: We assume logical_form_subset is a subset of
	   the logical forms in this cell_list structure. */
	template<typename Function>
	inline bool expand_cells(const Semantics& logical_form_subset, Function function)
	{
		return function(cell, logical_form_subset, 0.0);
	}

	template<typename Function>
	inline bool map_cells(const Semantics& logical_form_subset, Function function)
	{
		return function(cell, logical_form_subset, 0.0);
	}

	const double get_inner_probability() const {
		return cell.var.get_inner_probability();
	}

	void set_inner_probability(const double inner) {
		fprintf(stderr, "cell_list.set_inner_probability ERROR: Unsupported.\n");
		exit(EXIT_FAILURE);
	}

	inline cell_value<Mode, Semantics>& get_cell(const Semantics& logical_form_set) {
		return cell;
	}

	static inline void free(cell_list<Mode, Semantics>& list)
	{
		core::free(list.cell);
	}
};

template<parse_mode Mode, typename Semantics>
struct cell_list<Mode, Semantics,
	typename std::enable_if<(Mode == MODE_SAMPLE || Mode == MODE_PARSE || Mode == MODE_GENERATE)
		&& !std::is_empty<Semantics>::value>::type>
{
	hash_map<Semantics, cell_value<Mode, Semantics>*> cells;

	/* TODO: would it be valuable to move this into the cells? */
	double inner_probability;

	template<typename FunctionType>
	bool expand_cells(const Semantics& logical_form_subset, FunctionType function)
	{
		if (!cells.check_size()) return false;

		bool contains; unsigned int bucket;
		cell_value<Mode, Semantics>*& c = cells.get(logical_form_subset, contains, bucket);
		if (!contains) {
			double prior = ((Mode == MODE_PARSE) ? log_probability<false>(logical_form_subset) : 0.0);
			c = (cell_value<Mode, Semantics>*) malloc(sizeof(cell_value<Mode, Semantics>));
			if (c == NULL) {
				return false;
			} else if (!init(*c, inner_probability, prior, prior)) {
				core::free(c);
				return false;
			}
			cells.table.keys[bucket] = logical_form_subset;
			cells.table.size++;
		}
		function(*c, logical_form_subset, (Mode == MODE_PARSE) ? c->var.get_initial_prior_probability() : 0.0);
		return true;
	}

	template<typename FunctionType>
	bool map_cells(const Semantics& logical_form_subset, FunctionType function)
	{
		if (!cells.check_size()) return false;

		bool contains; unsigned int bucket;
		cell_value<Mode, Semantics>*& c = cells.get(logical_form_subset, contains, bucket);
		if (!contains) {
			double prior = ((Mode == MODE_PARSE) ? log_probability<false>(logical_form_subset) : 0.0);
			c = (cell_value<Mode, Semantics>*) malloc(sizeof(cell_value<Mode, Semantics>));
			if (c == NULL) {
				return false;
			} else if (!init(*c, inner_probability, prior, prior)) {
				core::free(c);
				return false;
			}
			cells.table.keys[bucket] = logical_form_subset;
			cells.table.size++;
		}
		function(*c, logical_form_subset, (Mode == MODE_PARSE) ? c->var.get_initial_prior_probability() : 0.0);
		return true;
	}

	inline double get_inner_probability() const {
		return inner_probability;
	}

	inline void set_inner_probability(double inner) {
		inner_probability = inner;
	}

	inline cell_value<Mode, Semantics>& get_cell(const Semantics& logical_form_set) {
		return *cells.get(logical_form_set);
	}

	static inline void free(cell_list<Mode, Semantics>& list)
	{
		for (const auto& entry : list.cells) {
			core::free(entry.key);
			core::free(*entry.value);
			core::free(entry.value);
		}
		core::free(list.cells);
	}
};

template<parse_mode Mode, typename Semantics,
	typename std::enable_if<Mode == MODE_COMPUTE_BOUNDS || std::is_empty<Semantics>::value>::type* = nullptr>
inline bool init(cell_list<Mode, Semantics>& list) {
	return init(list.cell, 0.0, 0.0, 0.0);
}

template<parse_mode Mode, typename Semantics,
	typename std::enable_if<(Mode == MODE_SAMPLE || Mode == MODE_PARSE || Mode == MODE_GENERATE)
		&& !std::is_empty<Semantics>::value>::type* = nullptr>
inline bool init(cell_list<Mode, Semantics>& list)
{
	if (!hash_map_init(list.cells, 16)) {
		fprintf(stderr, "init ERROR: Unable to initialize hash_map in new cell_list.\n");
		return false;
	}
	return true;
}

template<parse_mode Mode, typename Semantics, typename StringMapType>
struct chart
{
	cell_list<Mode, Semantics>*** cells;
	double** max_inner_probabilities;
	unsigned int sentence_length;
	unsigned int nonterminal_count;
	const StringMapType& token_map;

	chart(unsigned int sentence_length, unsigned int nonterminal_count, const StringMapType& token_map) :
		sentence_length(sentence_length), nonterminal_count(nonterminal_count), token_map(token_map)
	{
		cells = (cell_list<Mode, Semantics>***) malloc(
				sizeof(cell_list<Mode, Semantics>**) * (sentence_length + 1));
		max_inner_probabilities = (double**) malloc(sizeof(double*) * (sentence_length + 1));
		if (cells == NULL || max_inner_probabilities == NULL) {
			fprintf(stderr, "chart ERROR: Out of memory.\n");
			exit(EXIT_FAILURE);
		}
		for (unsigned int i = 0; i < sentence_length + 1; i++) {
			cells[i] = (cell_list<Mode, Semantics>**) malloc(
					sizeof(cell_list<Mode, Semantics>*) * (sentence_length - i + 1));
			max_inner_probabilities[i] = (double*) malloc(sizeof(double) * (sentence_length - i + 1));
			if (cells[i] == NULL || max_inner_probabilities[i] == NULL) {
				fprintf(stderr, "chart ERROR: Insufficient memory for chart.\n");
				exit(EXIT_FAILURE);
			}
			for (unsigned int j = 0; j < sentence_length - i + 1; j++) {
				cells[i][j] = (cell_list<Mode, Semantics>*) malloc(
						sizeof(cell_list<Mode, Semantics>) * nonterminal_count);
				if (cells[i][j] == NULL) {
					fprintf(stderr, "chart ERROR: Insufficient memory for cell list.\n");
					exit(EXIT_FAILURE);
				}
				for (unsigned int k = 0; k < nonterminal_count; k++)
					if (!init(cells[i][j][k])) {
						fprintf(stderr, "chart ERROR: Unable to initialize cell list.\n");
						exit(EXIT_FAILURE);
					}
			}
		}
	}

	~chart() {
		for (unsigned int i = 0; i < sentence_length + 1; i++) {
			for (unsigned int j = 0; j < sentence_length - i + 1; j++) {
				for (unsigned int k = 0; k < nonterminal_count; k++)
					free(cells[i][j][k]);
				free(cells[i][j]);
			}
			free(cells[i]);
			free(max_inner_probabilities[i]);
		}
		free(cells);
		free(max_inner_probabilities);
	}

	inline cell_value<Mode, Semantics>* init_cell(
		unsigned int nonterminal, span position,
		const Semantics& logical_form_set,
		double slice_variable,
		unsigned int sample_count)
	{
		cell_list<Mode, Semantics>& list = cells[position.start][position.length()][nonterminal - 1];
		return list.init_cell(prune(logical_form_set, position.length()), slice_variable, sample_count);
	}

	inline cell_value<Mode, Semantics>* init_cell(unsigned int nonterminal,
		span position, const Semantics& logical_form_set, unsigned int sample_count)
	{
		return init_cell(nonterminal, position, logical_form_set, 0.0, sample_count);
	}

	inline cell_list<Mode, Semantics>& get_cells(unsigned int nonterminal, span position) {
		return cells[position.start][position.length()][nonterminal - 1];
	}

	void compute_max_inner_probabilities(unsigned int sentence_length, unsigned int nonterminal_count)
	{
		for (unsigned int length = 1; length < sentence_length + 1; length++) {
			for (unsigned int i = 0; i < sentence_length - length + 1; i++) {
				max_inner_probabilities[i][length] = get_cells(1, {i, i + length}).get_inner_probability();
				for (unsigned int k = 1; k < nonterminal_count; k++) {
					double inner_probability = get_cells(k + 1, {i, i + length}).get_inner_probability();
					max_inner_probabilities[i][length] = max(max_inner_probabilities[i][length], inner_probability);
				}
			}
		}
		for (unsigned int length = 2; length < sentence_length + 1; length++) {
			for (unsigned int i = 0; i < sentence_length - length + 1; i++) {
				for (unsigned int j = 1; j < length; j++) {
					max_inner_probabilities[i][length] = max(max_inner_probabilities[i][length],
							max_inner_probabilities[i][j] + max_inner_probabilities[i + j][length - j]);
				}
			}
		}
	}
};


/* forward declarations */

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology>
bool expand_nonterminal(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const Semantics& logical_form_set,
	unsigned int nonterminal,
	cell_value<Mode, Semantics>& cell,
	span position);


template<parse_mode Mode, typename Semantics, typename Distribution>
inline nonterminal<Semantics, Distribution>& get_nonterminal(
	grammar<Semantics, Distribution>& G, unsigned int id)
{
	return G.nonterminals[id - 1];
}

template<parse_mode Mode, typename Semantics,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline double inner_probability(
		const weighted_feature_set<double>& posterior,
		const cell_value<Mode, Semantics>& cell)
{
	fprintf(stderr, "inner_probability ERROR: This should only be called in sampling mode.\n");
	exit(EXIT_FAILURE);
}

template<typename Semantics>
inline double inner_probability(
		const weighted_feature_set<double>& posterior,
		const cell_value<MODE_SAMPLE, Semantics>& cell)
{
	if (USE_SLICE_SAMPLING)
		return -cell.var.slice_beta;
	else return posterior.log_probability;
}

template<typename Semantics, typename StringMapType>
inline void inner_probability(
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	unsigned int nonterminal,
	const Semantics& logical_form_set,
	span position, double& inner,
	double& prior, double& initial_prior)
{
	/* TODO: we can get a tighter inner probability bound
	   if we use the logical_form_set; otherwise, we can
	   remove the unnecessary arguments to this function */
	cell_list<MODE_PARSE, Semantics>& cells = parse_chart.get_cells(nonterminal, position);

	bool contains;
	cell_value<MODE_PARSE, Semantics>*& c = cells.cells.get(logical_form_set, contains);
	if (contains) {
		inner = c->var.get_inner_probability();
		prior = c->var.get_inner_prior_probability();
		initial_prior = c->var.get_initial_prior_probability();
	} else {
		inner = cells.get_inner_probability();
		prior = 0.0; initial_prior = 0.0;
	}
}

template<typename Semantics, typename StringMapType>
inline void inner_probability(
	chart<MODE_GENERATE, Semantics, StringMapType>& parse_chart,
	unsigned int nonterminal,
	const Semantics& logical_form_set,
	span position, double& inner,
	double& prior, double& initial_prior)
{
	bool contains;
	cell_list<MODE_GENERATE, Semantics>& cells = parse_chart.get_cells(nonterminal, position);
	cell_value<MODE_GENERATE, Semantics>* cell = cells.cells.get(logical_form_set, contains);
	if (contains)
		inner = cell->var.get_inner_probability();
	else inner = 0.0;
	prior = 0.0; initial_prior = 0.0;
}

template<typename Semantics, typename StringMapType>
inline void initialize_message(
	const rule<Semantics>& rule,
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	const Semantics& next_logical_form,
	unsigned int rule_position,
	unsigned int start, unsigned int end,
	double*& message, double*& additive_priors,
	double*& right_priors, double additive_prior,
	double right_prior, const bool* separable)
{
	unsigned int next_nonterminal = rule.nt.nonterminals[rule_position];

	message = (double*) malloc(sizeof(double) * (end - start + 1));
	additive_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	right_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	for (unsigned int k = 0; k < end - start + 1; k++) {
		double inner_prior, initial_prior;
		inner_probability(parse_chart, next_nonterminal,
				next_logical_form, {start, start + k}, message[k], inner_prior, initial_prior);
		if (inner_prior == -std::numeric_limits<double>::infinity()) {
			right_priors[k] = -std::numeric_limits<double>::infinity();
			additive_priors[k] = -std::numeric_limits<double>::infinity();
		} else {
			right_priors[k] = min(right_prior, -additive_prior + !separable[rule_position] * inner_prior);
			additive_priors[k] = additive_prior + separable[rule_position] * (inner_prior - initial_prior);
		}
	}
}

template<typename Semantics, typename StringMapType>
inline void update_message_k(
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	const Semantics& next_logical_form,
	unsigned int nonterminal,
	unsigned int start, unsigned int end,
	const double* message, const double* additive_priors,
	const double* right_priors, double* next_message,
	double* next_additive_priors, double* next_right_priors,
	unsigned int k, bool is_separable)
{
	double inner, inner_prior, initial_prior;
	inner_probability(parse_chart, nonterminal, next_logical_form, {start, start + k}, inner, inner_prior, initial_prior);
	next_message[k] = message[0] + inner;
	if (is_negative_inf(inner_prior)) {
		next_right_priors[k] = -std::numeric_limits<double>::infinity();
		next_additive_priors[k] = -std::numeric_limits<double>::infinity();
	} else {
		next_right_priors[k] = min(right_priors[0], -additive_priors[0] + !is_separable * inner_prior);
		next_additive_priors[k] = additive_priors[0] + is_separable * (inner_prior - initial_prior);
	}
	double best_right = next_message[k] + next_right_priors[k] + next_additive_priors[k];

	for (unsigned int j = 1; j < k + 1; j++) {
		inner_probability(parse_chart, nonterminal, next_logical_form, {start + j, start + k}, inner, inner_prior, initial_prior);
		double message_j = message[j] + inner;
		double right_prior_j = min(right_priors[j], -additive_priors[j] + !is_separable * inner_prior);
		if (is_negative_inf(inner_prior)) continue;
		double additive_prior_j = additive_priors[j] + is_separable * (inner_prior - initial_prior);
		double right_j = message_j + right_prior_j + additive_prior_j;
		if (right_j > best_right) {
			next_message[k] = message_j;
			next_right_priors[k] = right_prior_j;
			next_additive_priors[k] = additive_prior_j;
			best_right = right_j;
		}
	}
}

template<typename Semantics, typename StringMapType>
inline void update_message(const rule<Semantics>& rule,
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	const Semantics& next_logical_form,
	unsigned int rule_position,
	unsigned int start, unsigned int end,
	const double* message, const double* additive_priors,
	const double* right_priors, double* next_message,
	double* next_additive_priors, double* next_right_priors,
	bool is_separable)
{
	unsigned int next_nonterminal = rule.nt.nonterminals[rule_position];
	for (unsigned int k = 0; k < end - start + 1; k++)
		update_message_k(parse_chart, next_logical_form, next_nonterminal, start, end, message, additive_priors,
				right_priors, next_message, next_additive_priors, next_right_priors, k, is_separable);
}

template<typename Semantics, typename StringMapType>
void right_probability(const rule<Semantics>& r,
	const Semantics& logical_form_set,
	const unsigned int* positions,
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
#if !defined(NDEBUG)
	if (r.is_terminal())
		fprintf(stderr, "right_probability WARNING: `r` is a terminal rule.\n");
#endif
	bool* separable = (bool*) alloca(sizeof(bool) * r.nt.length);
	is_separable(r.nt.transformations, r.nt.length, separable);

	Semantics& next_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
	if (!separable[0]) {
		initialize_any(next_logical_form);
	} else if (!apply(r.nt.transformations[0], logical_form_set, next_logical_form)) {
		right = -std::numeric_limits<double>::infinity();
		return;
	}

	unsigned int start = positions[0];
	unsigned int end = positions[r.nt.length];
	if (r.nt.length == 1) {
		/* this is the only nonterminal in this rule */
		double inner_right, inner_prior, initial_prior;
		inner_probability(parse_chart, r.nt.nonterminals[0],
				next_logical_form, {start, end}, inner_right, inner_prior, initial_prior);
		free(next_logical_form);
		if (is_negative_inf(inner_prior)) { right = -std::numeric_limits<double>::infinity(); right_prior = right; return; }
		right_prior = min(right_prior, !separable[0] * inner_prior);
		right = inner_right + right_prior + separable[0] * (inner_prior - initial_prior);
		return;
	}

	/* perform dynamic programming to find the maximizing
	   positions of nonterminals to the right of the current
	   rule position */
	double* message; double* additive_priors; double* right_priors;
	initialize_message(r, parse_chart, next_logical_form, 0, start, end,
			message, additive_priors, right_priors, 0.0, old_prior, separable);
	double* next_message = (double*) malloc(sizeof(double) * (end - start + 1));
	double* next_additive_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	double* next_right_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	for (unsigned int i = 1; i + 1 < r.nt.length; i++) {
		free(next_logical_form);
		if (!separable[i]) {
			initialize_any(next_logical_form);
		} else if (!apply(r.nt.transformations[i], logical_form_set, next_logical_form)) {
			right = -std::numeric_limits<double>::infinity(); return;
		}
		update_message(r, parse_chart, next_logical_form, i, start, end, message, additive_priors,
				right_priors, next_message, next_additive_priors, next_right_priors, separable[i]);
		swap(message, next_message); swap(additive_priors, next_additive_priors); swap(right_priors, next_right_priors);
	}

	free(next_logical_form);
	if (!separable[r.nt.length - 1]) {
		initialize_any(next_logical_form);
	} else if (!apply(r.nt.transformations[r.nt.length - 1], logical_form_set, next_logical_form)) {
		right = -std::numeric_limits<double>::infinity(); return;
	}
	update_message_k(parse_chart, next_logical_form, r.nt.nonterminals[r.nt.length - 1], start, end, message,
			additive_priors, right_priors, next_message, next_additive_priors, next_right_priors, end - start, separable);
	free(next_logical_form);

	right_prior = right_priors[end - start];
	right = next_message[end - start] + right_prior + additive_priors[end - start];
	free(message); free(next_message);
	free(additive_priors); free(next_additive_priors);
	free(right_priors); free(next_right_priors);
}

template<typename Semantics, typename StringMapType>
void right_probability(const rule<Semantics>& r,
	const Semantics& logical_form_set,
	const unsigned int* positions,
	chart<MODE_GENERATE, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
	right = 0.0;
	for (unsigned int i = 0; i < r.length; i++) {
		Semantics& next_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(r.transformations[i], logical_form_set, next_logical_form)) {
			right = -std::numeric_limits<double>::infinity();
			return;
		}

		double inner, initial_prior;
		inner_probability(parse_chart, r.nonterminals[i], next_logical_form, {0, 0}, inner, right_prior, initial_prior);
		free(next_logical_form);
		right += inner;
	}
}

template<typename Semantics, typename StringMapType>
void right_probability(const rule<Semantics>& r,
	const Semantics& logical_form_set,
	const unsigned int* positions,
	chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
	/* use a trivial bound in MODE_COMPUTE_BOUNDS */
	right = 0.0;
}

template<typename Semantics, typename StringMapType>
void right_probability(const rule<Semantics>& r,
	const Semantics& logical_form_set,
	const unsigned int* positions,
	chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
	/* unreachable code */
	fprintf(stderr, "right_probability ERROR: This function"
			" should not be called in sampling mode.");
	exit(EXIT_FAILURE);
}

template<bool IgnoreNext, typename Semantics, typename StringMapType>
void right_probability(
	const rule_state<MODE_PARSE, Semantics>& rule,
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
	unsigned int rule_position = rule.rule_position + 1;
	const ::rule<Semantics>& r = rule.syntax.get_rule();
#if !defined(NDEBUG)
	if (r.is_terminal())
		fprintf(stderr, "right_probability WARNING: `r` is a terminal rule.\n");
#endif
	bool* separable = (bool*) alloca(sizeof(bool) * r.nt.length);
	is_separable(r.nt.transformations, r.nt.length, separable);

	Semantics& next_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
	if (IgnoreNext || !separable[rule.rule_position]) {
		initialize_any(next_logical_form);
	} else if (!apply(r.nt.transformations[rule.rule_position], rule.logical_form_set, next_logical_form)) {
		right = -std::numeric_limits<double>::infinity();
		return;
	}

	double inner_right, inner_prior, initial_prior, additive_prior = 0.0;
	if (IgnoreNext) {
		right_prior = old_prior;
		if (rule_position == r.nt.length) {
			free(next_logical_form);
			right = right_prior;
			return;
		}
	} else {
		inner_probability(parse_chart, r.nt.nonterminals[rule.rule_position], next_logical_form,
				{rule.positions[rule.rule_position], rule.positions[rule_position]}, inner_right, inner_prior, initial_prior);
		if (is_negative_inf(inner_prior)) { right = -std::numeric_limits<double>::infinity(); right_prior = right; return; }
		additive_prior = separable[rule.rule_position] * (inner_prior - initial_prior);
		right_prior = min(old_prior, !separable[rule.rule_position] * inner_prior);
		if (rule_position == r.nt.length) {
			free(next_logical_form);
			right = right_prior + additive_prior;
			return;
		}
	}


	unsigned int start = rule.positions[rule_position];
	unsigned int end = rule.positions[r.nt.length];
	if (rule_position + 1 == r.nt.length) {
		/* this is the last nonterminal in this rule */
		free(next_logical_form);
		if (!separable[rule_position]) {
			initialize_any(next_logical_form);
		} else if (!apply(r.nt.transformations[rule_position], rule.logical_form_set, next_logical_form)) {
			right = -std::numeric_limits<double>::infinity(); return;
		}
		inner_probability(parse_chart, r.nt.nonterminals[rule_position],
				next_logical_form, {start, end}, inner_right, inner_prior, initial_prior);
		free(next_logical_form);
		if (is_negative_inf(inner_prior)) { right = -std::numeric_limits<double>::infinity(); right_prior = right; return; }
		right_prior = min(right_prior, -additive_prior + !separable[rule_position] * inner_prior);
		additive_prior += separable[rule_position] * (inner_prior - initial_prior);
		right = inner_right + right_prior + additive_prior;
		return;
	}


	/* perform dynamic programming to find the maximizing
	   positions of nonterminals to the right of the current
	   rule position */
	double* message; double* additive_priors; double* right_priors;
	initialize_message(r, parse_chart, next_logical_form, rule_position, start, end,
			message, additive_priors, right_priors, additive_prior, right_prior, separable);
	double* next_message = (double*) malloc(sizeof(double) * (end - start + 1));
	double* next_additive_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	double* next_right_priors = (double*) malloc(sizeof(double) * (end - start + 1));
	for (unsigned int i = rule_position + 1; i + 1 < r.nt.length; i++) {
		free(next_logical_form);
		if (!separable[i]) {
			initialize_any(next_logical_form);
		} else if (!apply(r.nt.transformations[i], rule.logical_form_set, next_logical_form)) {
			right = -std::numeric_limits<double>::infinity();
			free(message); free(next_message);
			free(additive_priors); free(next_additive_priors);
			free(right_priors); free(next_right_priors);
			return;
		}
		update_message(r, parse_chart, next_logical_form, i, start, end, message, additive_priors,
				right_priors, next_message, next_additive_priors, next_right_priors, separable[i]);
		swap(message, next_message); swap(additive_priors, next_additive_priors); swap(right_priors, next_right_priors);
	}

	free(next_logical_form);
	if (!separable[r.nt.length - 1]) {
		initialize_any(next_logical_form);
	} else if (!apply(r.nt.transformations[r.nt.length - 1], rule.logical_form_set, next_logical_form)) {
		right = -std::numeric_limits<double>::infinity();
		free(message); free(next_message);
		free(additive_priors); free(next_additive_priors);
		free(right_priors); free(next_right_priors);
		return;
	}
	update_message_k(parse_chart, next_logical_form, r.nt.nonterminals[r.nt.length - 1], start, end, message,
			additive_priors, right_priors, next_message, next_additive_priors, next_right_priors, end - start, separable);
	free(next_logical_form);

	right_prior = right_priors[end - start];
	right = next_message[end - start] + right_prior + additive_priors[end - start];
	free(message); free(next_message);
	free(additive_priors); free(next_additive_priors);
	free(right_priors); free(next_right_priors);
}

template<bool IgnoreNext, typename Semantics, typename StringMapType>
void right_probability(
	const rule_state<MODE_GENERATE, Semantics>& rule,
	chart<MODE_GENERATE, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& right_prior)
{
	right = 0.0;
	unsigned int start = rule.rule_position + (IgnoreNext ? 1 : 0);
	const ::rule<Semantics>& r = rule.syntax.get_rule();
	for (unsigned int i = start; i < r.length; i++) {
		Semantics& next_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(r.transformations[i], rule.logical_form_set, next_logical_form)) {
			right = -std::numeric_limits<double>::infinity();
			return;
		}

		double inner, initial_prior, inner_prior;
		inner_probability(parse_chart, r.nonterminals[i], next_logical_form, {0, 0}, inner, inner_prior, initial_prior);
		free(next_logical_form);
		right_prior = min(right_prior, inner_prior);
		if (IgnoreNext || i > start) right += inner;
	}
	right += right_prior;
}

template<bool IgnoreNext, typename Semantics, typename StringMapType>
inline void right_probability(
	const rule_state<MODE_COMPUTE_BOUNDS, Semantics>& rule,
	const chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType>& parse_chart,
	double old_prior, double& right, double& prior)
{
	/* use a trivial bound in MODE_COMPUTE_BOUNDS */
	right = 0.0;
}

template<bool IgnoreNext, typename Semantics, typename Distribution, typename StringMapType>
inline void outer_probability(
	const rule_state<MODE_SAMPLE, Semantics>& state,
	const chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const nonterminal<Semantics, Distribution>& N,
	double old_prior, double& outer, double& prior)
{
	/* unreachable code */
	fprintf(stderr, "outer_probability ERROR: This function"
			" should not be called in sampling mode.");
	exit(EXIT_FAILURE);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline void outer_probability(
	const rule<Semantics>& r,
	const Semantics& logical_form_set,
	const unsigned int* positions,
	const cell_value<Mode, Semantics>& cell,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	NonterminalType& N, double old_prior,
	double& outer, double& prior)
{
	prior = old_prior;
	if (USE_NONTERMINAL_PREITERATOR) {
		outer = 0.0;
	} else {
		if (Mode == MODE_PARSE || Mode == MODE_GENERATE) {
			outer = max_log_conditional(N.rule_distribution, r, logical_form_set, parse_chart.token_map);
			if (std::isinf(outer)) return;
		} else {
			Semantics any; initialize_any(any);
			outer = max_log_conditional(N.rule_distribution, r, any, parse_chart.token_map);
		}
	}

	if (!r.is_terminal() && (Mode == MODE_PARSE || Mode == MODE_GENERATE)) {
		double right;
		right_probability(r, logical_form_set, positions, parse_chart, old_prior, right, prior);
		outer += right;
	}

	outer += cell.var.get_outer_probability() - cell.prior_probability;
}

template<bool IgnoreNext, parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline void outer_probability(
	const rule_state<Mode, Semantics>& state,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	NonterminalType& N, double old_prior,
	double& outer, double& prior)
{
	prior = old_prior;
	const rule<Semantics>& r = state.syntax.get_rule();
	if (USE_NONTERMINAL_PREITERATOR) {
		outer = 0.0;
	} else {
		if (Mode == MODE_PARSE || Mode == MODE_GENERATE) {
			outer = max_log_conditional(N.rule_distribution, r, state.logical_form_set, parse_chart.token_map);
			if (std::isinf(outer)) return;
		} else {
			Semantics any; initialize_any(any);
			outer = max_log_conditional(N.rule_distribution, r, any, parse_chart.token_map);
		}
	}

	if (!r.is_terminal() && (Mode == MODE_PARSE || Mode == MODE_GENERATE)) {
		double right;
		right_probability<IgnoreNext>(state, parse_chart, old_prior, right, prior);
		outer += right;
	}

	outer += state.cell->var.get_outer_probability() - state.cell->prior_probability;
}

template<typename Semantics, typename StringMapType, typename Distribution>
inline double compute_priority(
	const rule_state<MODE_SAMPLE, Semantics>& state,
	chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	nonterminal<Semantics, Distribution>& N)
{
	return (double) state.positions[0] - state.positions[state.syntax.r.nt.length]
		 + (double) (N.id + 1) / (parse_chart.nonterminal_count + 2);
}

template<typename Semantics, typename StringMapType, typename Distribution>
inline double compute_priority(
	const nonterminal_iterator_state<MODE_SAMPLE, Semantics>& state,
	const chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const nonterminal<Semantics, Distribution>& N)
{
	return (double) state.positions[0] - state.positions[state.syntax.r.is_terminal() ? 1 : state.syntax.r.nt.length]
		 + (double) (N.id + 1) / (parse_chart.nonterminal_count + 2);
}

template<typename Semantics, typename StringMapType, typename Distribution>
inline double compute_priority(
	const invert_iterator_state<MODE_SAMPLE, Semantics>& state,
	const chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const nonterminal<Semantics, Distribution>& N)
{
	return (double) state.rule->positions[0] - state.rule->positions[state.rule->rule_position + 1]
		 + (double) (N.id + 1) / (parse_chart.nonterminal_count + 2);
}

template<typename Semantics, typename StringMapType, typename Distribution>
inline double compute_priority(
	const rule_completer_state<MODE_SAMPLE, Semantics>& state,
	const chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const nonterminal<Semantics, Distribution>& N)
{
	return (double) state.position.start - state.position.end
		 + (double) (N.id + 1) / (parse_chart.nonterminal_count + 2);
}

template<typename Semantics, typename StringMapType, typename NonterminalType>
inline double compute_priority(
	const rule_state<MODE_COMPUTE_BOUNDS, Semantics>& state,
	chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType>& parse_chart,
	NonterminalType& N)
{
	double outer, prior;
	outer_probability<false>(state, parse_chart, N, 0.0, outer, prior);
	return exp(state.log_probability + outer);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode == MODE_PARSE || Mode == MODE_GENERATE>::type* = nullptr>
inline double compute_priority(
	const rule_state<Mode, Semantics>& state,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	NonterminalType& N)
{
	Semantics& logical_form = *((Semantics*) alloca(sizeof(Semantics)));
	const rule<Semantics>& r = state.syntax.get_rule();
	if (!apply(r.nt.transformations[state.rule_position], state.logical_form_set, logical_form))
		return 0.0;

	span positions;
	if (Mode == MODE_GENERATE) {
		positions.start = 0; positions.end = 0;
	} else {
		positions.start = state.positions[state.rule_position];
		positions.end = state.positions[state.rule_position + 1];
	}

	double old_prior = (Mode == MODE_PARSE) ? min(log_probability<false>(state.logical_form_set), state.cell->prior_probability) : 0.0;

	double inner, inner_prior, initial_prior;
	inner_probability(parse_chart, r.nt.nonterminals[state.rule_position],
			logical_form, positions, inner, inner_prior, initial_prior);
	free(logical_form);

	double outer, outer_prior;
	outer_probability<false>(state, parse_chart, N, old_prior, outer, outer_prior);
	return exp(state.log_probability - old_prior + inner + outer);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType>
inline double compute_priority(const terminal_iterator_state<Mode, Semantics>& state,
	const chart<Mode, Semantics, StringMapType>& parse_chart, const NonterminalType& N)
{
	double outer = state.cell->var.get_outer_probability() - state.cell->prior_probability;
	return exp(outer + state.terminals[state.iterator].log_probability);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline double compute_priority(const nonterminal_iterator_state<Mode, Semantics>& state,
	const chart<Mode, Semantics, StringMapType>& parse_chart, const NonterminalType& N)
{
	double outer = state.cell->var.get_outer_probability() - state.cell->prior_probability;
	return exp(outer + state.posterior[state.iterator].log_probability);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline double compute_priority(const invert_iterator_state<Mode, Semantics>& state,
	chart<Mode, Semantics, StringMapType>& parse_chart, NonterminalType& N)
{
	double outer, outer_prior, old_prior = 0.0;
	if (Mode == MODE_PARSE)
		old_prior = min(log_probability<false>(state.inverse[state.index]), state.rule->cell->prior_probability);
	outer_probability<true>(*state.rule, parse_chart, N, old_prior, outer, outer_prior);
	return exp(state.log_probability + outer - old_prior);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename NonterminalType,
	typename std::enable_if<Mode != MODE_SAMPLE>::type* = nullptr>
inline double compute_priority(const rule_completer_state<Mode, Semantics>& state,
	chart<Mode, Semantics, StringMapType>& parse_chart, NonterminalType& N)
{
	/* rule completer is not used during parsing, so we pass 0 as the old prior */
	double outer, outer_prior;
	const rule_state<Mode, Semantics>& waiting = *state.waiting_states->data[state.iterator];
	outer_probability<false>(waiting, parse_chart, N, 0.0, outer, outer_prior);
	return exp(state.log_probability + waiting.log_probability + outer);
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType,
	typename std::enable_if<Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline double max_log_conditional(
		nonterminal<Semantics, Distribution>& N,
		const syntax_state<Mode, Semantics>& syntax,
		const Semantics& logical_form_set,
		const StringMapType& token_map)
{
	Semantics any; initialize_any(any);
	return max_log_conditional(N.rule_distribution, syntax.get_rule(), any, token_map);
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType,
	typename std::enable_if<Mode != MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline double max_log_conditional(
		nonterminal<Semantics, Distribution>& N,
		const syntax_state<Mode, Semantics>& syntax,
		const Semantics& logical_form_set,
		const StringMapType& token_map)
{
	fprintf(stderr, "max_log_conditional ERROR: Unimplemented.\n");
	exit(EXIT_FAILURE);
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename Distribution>
inline bool push_rule_states(
		agenda<Mode, Semantics>& queue,
		grammar<Semantics, Distribution>& G,
		chart<Mode, Semantics, StringMapType>& parse_chart,
		unsigned int nonterminal, const rule<Semantics>& r,
		const Semantics& logical_form_set,
		cell_value<Mode, Semantics>& cell,
		const tokenized_sentence<Semantics>& sentence,
		span position, double rule_log_conditional = 0.0)
{
	auto& N = get_nonterminal<Mode>(G, nonterminal);
	unsigned int end = position.start + 1;
	unsigned int last_end = (Mode == MODE_GENERATE ? 1 : (position.end - r.nt.length + 1));
	if (r.nt.length == 1) end = last_end;
	for (; end < last_end + 1; end++)
	{
		/* check if the next nonterminal is feasible at this position */
		unsigned int next_nonterminal = r.nt.nonterminals[0];
		if (Mode != MODE_GENERATE && !get_nonterminal<Mode>(G, next_nonterminal).rule_distribution.has_nonterminal_rules()) {
			if (end > sentence.end_terminal[position.start])
				break;
		}

		/* expand and push this new rule state */
		rule_state<Mode, Semantics>* new_rule =
			(rule_state<Mode, Semantics>*) malloc(sizeof(rule_state<Mode, Semantics>));
		if (new_rule == NULL || !init(*new_rule, nonterminal, r, position)) {
			if (new_rule != NULL) free(new_rule);
			return false;
		}
		if (Mode != MODE_GENERATE)
			new_rule->positions[1] = end;
		new_rule->cell = &cell;
		new_rule->rule_position = 0;
		if (Mode != MODE_COMPUTE_BOUNDS)
			new_rule->logical_form_set = logical_form_set;
		new_rule->log_probability = rule_log_conditional;
		if (Mode == MODE_PARSE)
			new_rule->log_probability += min(log_probability<false>(logical_form_set), cell.prior_probability);

		double priority = compute_priority(*new_rule, parse_chart, N);
		if (priority == 0.0) {
			free(*new_rule); free(new_rule);
			continue;
		}

		parser_search_state<Mode, Semantics> state;
		state.rule = new_rule;
		state.phase = PHASE_RULE;
		state.priority = priority;
		queue.push(state, cell);
	}
	return true;
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename Distribution>
bool push_invert_state(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	rule_state<Mode, Semantics>& rule,
	const Semantics& logical_form_set,
	const syntax_state<Mode, Semantics>& syntax,
	double inner_probability)
{
#if !defined(NDEBUG)
	if (rule.syntax.get_rule().is_terminal())
		fprintf(stderr, "push_invert_state WARNING: Inverting a terminal rule.\n");
#endif

	invert_iterator_state<Mode, Semantics>* inverse =
		(invert_iterator_state<Mode, Semantics>*) malloc(sizeof(invert_iterator_state<Mode, Semantics>));
	if (inverse == NULL) {
		fprintf(stderr, "push_invert_state ERROR: Out of memory.\n");
		return false;
	} else if (
		Mode != MODE_COMPUTE_BOUNDS
	 && !invert(inverse->inverse, inverse->inverse_count,
		 rule.syntax.get_rule().nt.transformations[rule.rule_position],
		 rule.logical_form_set, logical_form_set))
	{
		/* the inverse is empty, so return quietly */
		free(inverse); return true;
	}
	inverse->index = 0;

if (Mode == MODE_PARSE && debug_flag) {
default_scribe scribe;
check_invariants(G, parse_chart, rule, logical_form_set, inverse->inverse[inverse->index], scribe);
}

	inverse->rule = &rule;
	inverse->log_probability = rule.log_probability + inner_probability;
	/* TODO: make this work for generic inverter structures */
	if (Mode == MODE_PARSE) {
		double prev_prior = min(log_probability<false>(rule.logical_form_set), rule.cell->prior_probability);
		inverse->log_probability += min(log_probability<false>(inverse->inverse[inverse->index]), rule.cell->prior_probability) - prev_prior;
		if (std::isinf(inverse->log_probability)) {
			if (Mode != MODE_COMPUTE_BOUNDS) {
				for (unsigned int i = 0; i < inverse->inverse_count; i++)
					free(inverse->inverse[i]);
				free(inverse->inverse);
			}
			free(inverse); return true;
		}
	}
	if (!init(inverse->syntax, syntax)) {
		if (Mode != MODE_COMPUTE_BOUNDS) {
			for (unsigned int i = 0; i < inverse->inverse_count; i++)
				free(inverse->inverse[i]);
			free(inverse->inverse);
		}
		free(inverse); return false;
	}
	rule.reference_count++;

/* check that the inversion did not change the likelihoods of the completed portion of the rule state */
/*if (Mode == MODE_PARSE && debug_flag) {
check_log_likelihood(G, *inverse, logical_form_set, parse_chart.token_map);
}*/

	parser_search_state<Mode, Semantics> state;
	state.invert_iterator = inverse;
	state.phase = PHASE_INVERT_ITERATOR;
	state.priority = compute_priority(*inverse, parse_chart,
			get_nonterminal<Mode>(G, rule.nonterminal));
	queue.push(state, *rule.cell);
	return true;
}

template<parse_mode Mode, typename Semantics, typename StringMapType, typename Distribution>
inline bool complete_nonterminal(
		agenda<Mode, Semantics>& queue,
		grammar<Semantics, Distribution>& G,
		chart<Mode, Semantics, StringMapType>& parse_chart,
		const tokenized_sentence<Semantics>& sentence,
		unsigned int nonterminal_id,
		cell_value<Mode, Semantics>& completed_cell,
		const syntax_state<Mode, Semantics>& syntax,
		const Semantics& logical_form_set,
		const double log_likelihood,
		const unsigned int* positions)
{
	const rule<Semantics>& rule = syntax.get_rule();
	unsigned int start = (Mode == MODE_GENERATE) ? 0 : positions[0];
	unsigned int end = (Mode == MODE_GENERATE) ? 0 : positions[rule.is_terminal() ? 1 : rule.nt.length];

if (Mode == MODE_PARSE && debug_flag) {
check_log_likelihood(G, syntax, logical_form_set, nonterminal_id, log_likelihood, parse_chart.token_map);
}

	/* check if this completed nonterminal improves upon any of the existing bounds */
	if (Mode == MODE_COMPUTE_BOUNDS) {
		bool dominates = true, is_dominated = true;
		for (const nonterminal_state<Mode, Semantics>& nonterminal : completed_cell.completed) {
			if (nonterminal.log_probability > log_likelihood) dominates = false;
			else if (nonterminal.log_probability < log_likelihood) is_dominated = false;
		}
		if (is_dominated && completed_cell.completed.length > 0)
			return true;
		if (dominates && completed_cell.completed.length > 0) {
			/* TODO: once a correct rule completer is implemented
			   for MODE_COMPUTE_BOUNDS, this code should be
			   unreachable due to monotonicity */
			/* remove the previously-completed suboptimal nonterminals */
			for (nonterminal_state<Mode, Semantics>& nonterminal : completed_cell.completed)
				free(nonterminal);
			completed_cell.completed.clear();
		}
	} else if (Mode == MODE_GENERATE) {
		if (completed_cell.completed.length > 0 && log_likelihood > completed_cell.completed[0].log_probability) {
			fprintf(stderr, "complete_nonterminal WARNING: The completed nonterminal has higher"
					" log probability than an earlier completed nonterminal at the same cell.\n");
		}
	} else if (Mode == MODE_PARSE) {
		double prior = log_probability<false>(logical_form_set);
		if (completed_cell.completed.length > 0) {
			double completed_prior = log_probability<false>(completed_cell.completed[0].logical_form_set);
			if (completed_prior > completed_cell.prior_probability && prior > completed_cell.prior_probability
			 && log_likelihood > completed_cell.completed[0].log_probability + 1.0e-12) {
				fprintf(stderr, "complete_nonterminal WARNING: The completed nonterminal has higher"
						" log probability than an earlier completed nonterminal at the same cell.\n");
			}
		}
	}

if (Mode == MODE_PARSE && detect_duplicate_logical_forms) {
for (const nonterminal_state<Mode, Semantics>& state : completed_cell.completed) {
	if (state.logical_form_set == logical_form_set) {
		fprintf(stderr, "compute_nonterminal WARNING: Detected duplicate logical form in chart cell:\n");
		print(logical_form_set, stderr, *debug_terminal_printer); print('\n', stderr);
#if !defined(NDEBUG)
		fprintf(stderr, "(the duplicate logical form was completed on iteration %u)\n", state.iteration);
#endif

const string** nonterminal_name_map = invert(G.nonterminal_names);
string_map_scribe nonterminal_printer = { nonterminal_name_map, G.nonterminal_names.table.size + 1 };
print(state.syntax.get_tree(), stderr, nonterminal_printer, *debug_terminal_printer, nonterminal_id); print('\n', stderr);
print(syntax.get_tree(), stderr, nonterminal_printer, *debug_terminal_printer, nonterminal_id); print('\n', stderr);
free(nonterminal_name_map);
exit(EXIT_FAILURE);
	}
}
}

	/* add the completed nonterminal to the appropriate chart cell */
	if (!completed_cell.completed.ensure_capacity(completed_cell.completed.length + 1))
		return false;
	nonterminal_state<Mode, Semantics>& new_nonterminal =
		completed_cell.completed[(unsigned int) completed_cell.completed.length];
	if (!init(new_nonterminal, syntax, positions, logical_form_set, log_likelihood))
		return false;
#if !defined(NDEBUG)
	new_nonterminal.iteration = queue.iteration;
#endif
	completed_cell.completed.length++;

	/* create an iterator to complete any waiting rule states with this new nonterminal */
	if (Mode != MODE_SAMPLE) {
		/* TODO: for syntactic parsing, we don't need the invert step */
		for (rule_state<Mode, Semantics>* waiting_state : completed_cell.waiting_states)
		{
			if (!push_invert_state(queue, G, parse_chart, *waiting_state,
					logical_form_set, syntax, log_likelihood)) return false;
		}

	} else if (completed_cell.completer == NULL && completed_cell.waiting_states.length > 0) {
		rule_completer_state<Mode, Semantics>* completer =
			(rule_completer_state<Mode, Semantics>*) malloc(sizeof(rule_completer_state<Mode, Semantics>));
		if (completer == NULL) {
			fprintf(stderr, "complete_nonterminal ERROR: Out of memory.\n");
			return false;
		}
		completer->iterator = 0;
		completer->log_probability = log_likelihood;
		completer->logical_form_set = logical_form_set;
		completer->syntax = syntax;
		completer->position.start = start;
		completer->position.end = end;
		completer->waiting_states = &completed_cell.waiting_states;
		completer->cell = &completed_cell;
		completed_cell.completer = completer;

		parser_search_state<Mode, Semantics> state;
		state.rule_completer = completer;
		state.phase = PHASE_RULE_COMPLETER;
		state.priority = compute_priority(*completer,
				parse_chart, get_nonterminal<Mode>(G, nonterminal_id));
		queue.push(state, completed_cell);
	}
	return true;
}

template<bool AllowAmbiguous, parse_mode Mode, typename Semantics, typename StringMapType, typename Distribution, typename Morphology>
inline bool push_nonterminal_iterator(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	unsigned int nonterminal,
	cell_value<Mode, Semantics>& cell,
	const syntax_state<Mode, Semantics>& syntax,
	const Semantics& logical_form_set,
	unsigned int* positions, double inner_log_probability)
{
	auto& N = get_nonterminal<Mode>(G, nonterminal);
	const rule<Semantics>& r = syntax.get_rule();

	auto push_iterator = [&](const rule<Semantics>& r,
			const syntax_state<Mode, Semantics>& syntax,
			const Semantics& logical_form_set)
		{
			if (Mode == MODE_COMPUTE_BOUNDS) {
				double inside = max_log_conditional(N, syntax, logical_form_set, parse_chart.token_map);
				if (is_negative_inf(inside))
					return true;
				if (USE_NONTERMINAL_PREITERATOR) {
					double prior = 0.0;
					if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
						prior = min(log_probability<false>(logical_form_set), cell.prior_probability);
					unsigned int start = (Mode == MODE_GENERATE) ? 0 : positions[0];
					unsigned int end = (Mode == MODE_GENERATE) ? 0 : positions[r.is_terminal() ? 1 : r.nt.length];
					if (!r.is_terminal())
						return push_rule_states(queue, G, parse_chart, nonterminal, r, logical_form_set,
								cell, sentence, {start, end}, inner_log_probability - prior + inside);
				}
				return complete_nonterminal(queue, G, parse_chart, sentence, nonterminal, cell,
						syntax, logical_form_set, inner_log_probability + inside, positions);
			}

			unsigned int posterior_length;
			weighted<Semantics>* posterior = log_conditional<true, Mode != MODE_SAMPLE && !AllowAmbiguous>(
					N.rule_distribution, r, logical_form_set, parse_chart.token_map, posterior_length);
			if (posterior == NULL) {
				return false;
			} else if (posterior_length == 0) {
				free(posterior);
				return true;
			}

			/* TODO: either remove this special case for the
			   sampler or fix the expand_cells function to perform
			   expansion *after* all modifications to the
			   tree_semantics trie */
			/* TODO: need to debug this optimization */
			constexpr static bool enable_optimization = false; //true;
			if (enable_optimization && Mode == MODE_SAMPLE && posterior_length == 1) {
				/* optimization: directly process the single item in the posterior
				   (this is not available in parse mode since it messes monotonicity) */
				const weighted<Semantics>& singleton = posterior[0];
				if (!complete_nonterminal(queue, G, parse_chart, sentence, nonterminal, cell, syntax,
						singleton.object, singleton.log_probability + inner_log_probability, positions))
					return false;
				free(posterior[0]);
				free(posterior);
			} else if (posterior_length > 0) {
				nonterminal_iterator_state<Mode, Semantics>* iterator =
					(nonterminal_iterator_state<Mode, Semantics>*) malloc(sizeof(nonterminal_iterator_state<Mode, Semantics>));
				if (iterator == NULL) {
					fprintf(stderr, "push_nonterminal_iterator ERROR: Out of memory.\n");
					for (unsigned int i = 0; i < posterior_length; i++)
						free(posterior[i]);
					free(posterior);
					return false;
				} else if (!init(*iterator, parse_chart, nonterminal,
						inner_log_probability, syntax, posterior, posterior_length, &cell, positions))
				{
					free(iterator); return false;
				} else if (iterator->posterior_length == 0) {
					free(*iterator); free(iterator);
					return true;
				}
				iterator->iterator = 0;

				parser_search_state<Mode, Semantics> state;
				state.nonterminal_iterator = iterator;
				state.phase = PHASE_NONTERMINAL_ITERATOR;
				state.priority = compute_priority(*iterator, parse_chart, N);
				queue.push(state, cell);
			}
			return true;
		};

	auto emit_root = [&](const sequence& terminal, const Semantics& logical_form_set)
		{
			rule<Semantics>& terminal_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
			syntax_state<Mode, Semantics>& new_syntax = *((syntax_state<Mode, Semantics>*) alloca(sizeof(syntax_state<Mode, Semantics>)));
			terminal_rule.type = rule_type::TERMINAL;
			terminal_rule.t.terminals = terminal.tokens;
			terminal_rule.t.length = terminal.length;
			terminal_rule.t.inflected = nullptr;
			terminal_rule.t.inflected_length = 0;
			if (!init(new_syntax, terminal_rule)
			 || !push_iterator(terminal_rule, new_syntax, logical_form_set)) {
				free(new_syntax);
				return false;
			}
			free(new_syntax);
			return true;
		};

	if (r.is_terminal()) {
#if !defined(NDEBUG)
		if (Mode == MODE_GENERATE)
			fprintf(stderr, "push_nonterminal_iterator WARNING: `Mode` shouldn't be GENERATE here.\n");
#endif
		if (positions[0] == 0)
			return morphology_parse<true>(morphology_parser, {r.t.terminals, r.t.length}, N.rule_distribution.get_part_of_speech(), logical_form_set, emit_root);
		else return morphology_parse<false>(morphology_parser, {r.t.terminals, r.t.length}, N.rule_distribution.get_part_of_speech(), logical_form_set, emit_root);
	} else {
		return push_iterator(r, syntax, logical_form_set);
	}
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename StringMapType,
	typename Distribution, typename Morphology>
inline bool push_terminal_iterator(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	Morphology& morphology_parser,
	unsigned int nonterminal,
	cell_value<Mode, Semantics>& cell,
	const Semantics& logical_form_set)
{
	unsigned int terminal_count;
	auto& N = get_nonterminal<Mode>(G, nonterminal);
	weighted<sequence>* terminals = get_terminals<!AllowAmbiguous>(
			N.rule_distribution, logical_form_set, parse_chart.token_map, terminal_count);
	if (terminals == NULL) {
		return false;
	}

	unsigned int dst = 0;
	for (unsigned int i = 0; i < terminal_count; i++) {
		if (morphology_is_valid(morphology_parser, terminals[i].object, N.rule_distribution.get_part_of_speech(), logical_form_set)) {
			move(terminals[i], terminals[dst]);
			dst++;
		} else {
			free(terminals[i]);
		}
	}
	if (dst == 0) {
		free(terminals);
		return true;
	} else if (dst > 1) {
		sort(terminals, dst, default_sorter());
	}

	terminal_iterator_state<Mode, Semantics>* iterator =
		(terminal_iterator_state<Mode, Semantics>*) malloc(sizeof(terminal_iterator_state<Mode, Semantics>));
	if (iterator == NULL) {
		fprintf(stderr, "push_terminal_iterator ERROR: Out of memory.\n");
		for (unsigned int i = 0; i < dst; i++)
			free(terminals[i]);
		free(terminals); return false;
	} else if (!init(*iterator, nonterminal, &cell, logical_form_set, terminals, dst)) {
		for (unsigned int i = 0; i < dst; i++)
			free(terminals[i]);
		free(terminals); free(iterator);
		return false;
	}

	parser_search_state<Mode, Semantics> state;
	state.terminal_iterator = iterator;
	state.phase = PHASE_TERMINAL_ITERATOR;
	state.priority = compute_priority(*iterator, parse_chart, N);
	queue.push(state, cell);
	return true;
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename StringMapType,
	typename Distribution, typename Morphology>
bool complete_invert_state(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const rule_state<Mode, Semantics>& completed_rule,
	const syntax_state<Mode, Semantics>& syntax,
	const Semantics& logical_form,
	double inner_probability)
{
	unsigned int rule_position = completed_rule.rule_position + 1;
	const rule<Semantics>& r = completed_rule.syntax.get_rule();
	if (rule_position < r.nt.length) {
		/* the rule has more right-hand nonterminals */

		/* consider all possible end positions for the next nonterminal */
		unsigned int next_end = (Mode == MODE_GENERATE ? 1 : (completed_rule.positions[rule_position] + 1));
		unsigned int last_end = (Mode == MODE_GENERATE ? 1 : (completed_rule.positions[r.nt.length] - r.nt.length + rule_position + 1));
		if (rule_position == completed_rule.syntax.get_rule().nt.length - 1)
			/* this is the last nonterminal, so there's only one possible end position */
			next_end = last_end;
		for (; next_end < last_end + 1; next_end++) {
			/* check if the next nonterminal is feasible at this position */
			unsigned int next_nonterminal = r.nt.nonterminals[rule_position];
			if (Mode != MODE_GENERATE && !get_nonterminal<Mode>(G, next_nonterminal).rule_distribution.has_nonterminal_rules()) {
				if (next_end > sentence.end_terminal[completed_rule.positions[rule_position]])
					break;
			}

			rule_state<Mode, Semantics>* new_rule =
				(rule_state<Mode, Semantics>*) malloc(sizeof(rule_state<Mode, Semantics>));
			if (new_rule == NULL || !init(*new_rule, completed_rule, syntax)) {
				if (new_rule != NULL) free(new_rule);
				return false;
			}
			new_rule->cell = completed_rule.cell;
			if (Mode != MODE_GENERATE)
				new_rule->positions[rule_position + 1] = next_end;
			new_rule->rule_position = rule_position;
			new_rule->log_probability = inner_probability;
			if (Mode != MODE_COMPUTE_BOUNDS)
				new_rule->logical_form_set = logical_form;

			parser_search_state<Mode, Semantics> state;
			state.rule = new_rule;
			state.phase = PHASE_RULE;
			state.priority = compute_priority(*new_rule, parse_chart,
				get_nonterminal<Mode>(G, completed_rule.nonterminal));
			if (state.priority == 0.0) {
				free(*new_rule); free(new_rule);
				continue;
			}
			queue.push(state, *completed_rule.cell);
		}
		return true;
	}

	/* there are no more symbols in the right-hand side of this rule */
	syntax_state<Mode, Semantics> new_syntax(completed_rule.syntax);
	if (!add_child(new_syntax, syntax, completed_rule.rule_position))
		return false;
	double old_prior = 0.0;
	if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
		old_prior = min(log_probability<false>(logical_form), completed_rule.cell->prior_probability);
	if (USE_NONTERMINAL_PREITERATOR) {
		return complete_nonterminal(
				queue, G, parse_chart, sentence, completed_rule.nonterminal,
				*completed_rule.cell, new_syntax, logical_form,
				inner_probability - old_prior, completed_rule.positions);
	} else {
		return push_nonterminal_iterator<AllowAmbiguous>(queue, G, parse_chart,
				sentence, morphology_parser, completed_rule.nonterminal,
				*completed_rule.cell, new_syntax, logical_form, completed_rule.positions,
				inner_probability - old_prior);
	}
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename StringMapType,
	typename Distribution, typename Morphology>
inline bool complete_invert_state(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const invert_iterator_state<Mode, Semantics>& state)
{
	Semantics& logical_form = *((Semantics*) alloca(sizeof(Semantics)));
	if (Mode != MODE_COMPUTE_BOUNDS)
		logical_form = state.inverse[state.index];
	bool result = complete_invert_state<AllowAmbiguous>(queue, G, parse_chart, sentence,
			morphology_parser, *state.rule, state.syntax, logical_form, state.log_probability);
	if (Mode != MODE_COMPUTE_BOUNDS)
		free(logical_form);
	return result;
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename StringMapType,
	typename Distribution, typename Morphology>
bool process_invert_iterator(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	invert_iterator_state<Mode, Semantics>& iterator,
	bool& cleanup)
{
	if (!complete_invert_state<AllowAmbiguous>(queue, G, parse_chart, sentence, morphology_parser, iterator))
		return false;

	/* increment the iterator; add it back to the queue if it's not empty */
	if (Mode == MODE_COMPUTE_BOUNDS)
		return true;
	iterator.index++;
	if (iterator.index < iterator.inverse_count) {
		parser_search_state<Mode, Semantics> state;
		state.invert_iterator = &iterator;
		state.phase = PHASE_INVERT_ITERATOR;
		state.priority = compute_priority(iterator, parse_chart,
			get_nonterminal<Mode>(G, iterator.rule->nonterminal));
		queue.push(state, *iterator.rule->cell);
		cleanup = false;
	}
	return true;
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType, typename Scribe>
bool check_invariants(
		grammar<Semantics, Distribution>& G, chart<Mode, Semantics, StringMapType>& parse_chart,
		const rule_state<Mode, Semantics>& rule, const Semantics& child_logical_form,
		const Semantics& new_logical_form, Scribe& scribe)
{
	/* check the prior probability invariants */
	bool valid = true;
	const transformation<Semantics>& transformation = rule.syntax.get_rule().nt.transformations[rule.rule_position];
	bool* separable = (bool*) alloca(sizeof(bool) * rule.syntax.get_rule().nt.length);
	is_separable(rule.syntax.get_rule().nt.transformations, rule.syntax.get_rule().nt.length, separable);
	if (separable[rule.rule_position]) {
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(transformation, rule.logical_form_set, transformed)) {
			fprintf(stderr, "check_prior_invariants ERROR: Unable to apply semantic transformation function.\n");
			return false;
		}

		if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS
		 && log_probability<false>(new_logical_form) > log_probability<false>(rule.logical_form_set)
		  - log_probability<false>(transformed) + log_probability<false>(child_logical_form) + 1.0e-12)
		{
			print("check_invariants WARNING: Prior probability invariant violated for separable transformation.\n", stderr);
			valid = false;
		}
		free(transformed);
	}

	if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS
	 && log_probability<false>(new_logical_form) > log_probability<false>(child_logical_form)) {
		print("check_invariants WARNING: Prior of new logical form is greater than the prior of the child logical form.\n", stderr);
		valid = false;
	} if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS
	   && log_probability<false>(new_logical_form) > log_probability<false>(rule.logical_form_set)) {
		print("check_invariants WARNING: Prior of new logical form is greater than the prior of the old logical form.\n", stderr);
		valid = false;
	}

	if (!valid) {
		print("  semantic transformation function: ", stderr); print(transformation, stderr); print('\n', stderr);
		print("  old logical form:   ", stderr); print(rule.logical_form_set, stderr, scribe); print('\n', stderr);
		print("  child logical form: ", stderr); print(child_logical_form, stderr, scribe); print('\n', stderr);
		print("  new logical form:   ", stderr); print(new_logical_form, stderr, scribe); print('\n', stderr);
		fprintf(stderr, "  prior of old logical form:   %.*lf\n", PRINT_PROBABILITY_PRECISION, log_probability<false>(rule.logical_form_set));
		fprintf(stderr, "  prior of child logical form: %.*lf\n", PRINT_PROBABILITY_PRECISION, log_probability<false>(child_logical_form));
		fprintf(stderr, "  prior of new logical form:   %.*lf\n", PRINT_PROBABILITY_PRECISION, log_probability<false>(new_logical_form));
	}

	/* check the conditional probability invariant */
	const ::rule<Semantics>& r = rule.syntax.get_rule();
	auto& N = get_nonterminal<Mode>(G, rule.nonterminal);
	double old_max_conditional = max_log_conditional(N.rule_distribution, r, rule.logical_form_set, parse_chart.token_map);
	double new_max_conditional = max_log_conditional(N.rule_distribution, r, new_logical_form, parse_chart.token_map);
	if (new_max_conditional > old_max_conditional) {
		print("check_invariants WARNING: The maximum log conditional probability of the"
				" new logical form is greater than that of the old logical form.\n", stderr);
		print("  old logical form:   ", stderr); print(rule.logical_form_set, stderr, scribe); print('\n', stderr);
		print("  child logical form: ", stderr); print(child_logical_form, stderr, scribe); print('\n', stderr);
		print("  new logical form:   ", stderr); print(new_logical_form, stderr, scribe); print('\n', stderr);
		fprintf(stderr, "  max log conditional of old logical form: %.*lf\n", PRINT_PROBABILITY_PRECISION,
				max_log_conditional(N.rule_distribution, r, rule.logical_form_set, parse_chart.token_map));
		fprintf(stderr, "  max log conditional of new logical form: %.*lf\n", PRINT_PROBABILITY_PRECISION,
				max_log_conditional(N.rule_distribution, r, new_logical_form, parse_chart.token_map));
	}
	return true;
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType>
inline void check_log_likelihood(
		grammar<Semantics, Distribution>& G,
		const syntax_state<Mode, Semantics>& syntax,
		const Semantics& logical_form_set,
		unsigned int nonterminal_id,
		double computed_log_likelihood,
		const StringMapType& token_map)
{
	double expected_log_likelihood = ::log_probability(G, syntax.get_tree(), logical_form_set, token_map, nonterminal_id);
	if (!std::isinf(expected_log_likelihood) && fabs(expected_log_likelihood - computed_log_likelihood) > 1.0e-12) {
		fprintf(stderr, "check_log_likelihood WARNING: The computed log likelihood is incorrect.\n");
		print(logical_form_set, stderr, *debug_terminal_printer); print("\n", stderr);
		print(syntax.get_tree(), stderr, *debug_nonterminal_printer, *debug_terminal_printer, nonterminal_id); print("\n", stderr);
		fprintf(stderr, "  Expected log likelihood = %.*lf\n", PRINT_PROBABILITY_PRECISION, expected_log_likelihood);
		fprintf(stderr, "  Computed log likelihood = %.*lf\n", PRINT_PROBABILITY_PRECISION, computed_log_likelihood);
	}
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType>
inline void check_log_likelihood(
		grammar<Semantics, Distribution>& G,
		const invert_iterator_state<Mode, Semantics>& inverse,
		const Semantics& child_logical_form_set,
		const StringMapType& token_map)
{
	const rule_state<Mode, Semantics>& state = *inverse.rule;
	double expected_log_likelihood = 0.0;
	double computed_log_likelihood = inverse.log_probability - min(log_probability<false>(inverse.inverse[inverse.index]), state.cell->prior_probability);
	for (unsigned int i = 0; i < state.rule_position; i++) {
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(state.syntax.get_rule().transformations[i], *inverse.inverse[inverse.index], transformed)) {
			//fprintf(stderr, "check_log_likelihood WARNING: Unable to apply semantic transformation function at rule position %u.\n", i);
			//print(inverse, stderr, *debug_nonterminal_printer, *debug_terminal_printer);
			return;
		}
		expected_log_likelihood += log_probability(G, *(state.syntax.get_tree().children[i]), transformed, token_map, state.syntax.get_rule().nonterminals[i]);
		free(transformed);
	}
	expected_log_likelihood += log_probability(G, inverse.syntax.get_tree(), child_logical_form_set, token_map, state.syntax.get_rule().nonterminals[state.rule_position]);

	if (!std::isinf(expected_log_likelihood) && fabs(expected_log_likelihood - computed_log_likelihood) > 1.0e-12) {
		fprintf(stderr, "check_log_likelihood WARNING: The computed log likelihood is incorrect.\n");
		print(inverse, stderr, *debug_nonterminal_printer, *debug_terminal_printer);
		fprintf(stderr, "  Expected log likelihood = %.*lf\n", PRINT_PROBABILITY_PRECISION, expected_log_likelihood);
		fprintf(stderr, "  Computed log likelihood = %.*lf\n", PRINT_PROBABILITY_PRECISION, computed_log_likelihood);
	}
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType>
bool process_rule_completer(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	rule_completer_state<Mode, Semantics>& completer,
	bool& cleanup)
{
	if (completer.iterator == 0) {
		/* this is the first iteration */
		/* since we're sampling, we don't need to preserve
		   the full structure of each completed nonterminal;
		   instead, we care about the total probability mass
		   in this chart cell */
		completer_log_probability(completer, completer.cell->completed);
	}

	if (!push_invert_state(
			queue, G, parse_chart, *completer.waiting_states->data[completer.iterator],
			completer.logical_form_set, completer.syntax, completer.log_probability))
	{
		return false;
	}

	/* increment the iterator and push it back on the queue if it's not empty */
	completer.iterator++;
	if (completer.iterator < completer.waiting_states->length) {
		parser_search_state<Mode, Semantics> state;
		state.rule_completer = &completer;
		state.phase = PHASE_RULE_COMPLETER;
		unsigned int nonterminal = completer.waiting_states->first()->nonterminal;
		state.priority = compute_priority(completer,
				parse_chart, get_nonterminal<Mode>(G, nonterminal));
		queue.push(state, *completer.cell);
		cleanup = false;
	}
	return true;
}

template<typename Semantics>
inline void free_rules(array<rule<Semantics>>& rules) {
	for (rule<Semantics>& r : rules)
		free(r);
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology>
bool expand_nonterminal(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const Semantics& logical_form_set,
	unsigned int nonterminal,
	cell_value<Mode, Semantics>& cell,
	span position)
{
	array<rule<Semantics>> rules = array<rule<Semantics>>(16);
	auto& N = get_nonterminal<Mode>(G, nonterminal);
	if (Mode == MODE_SAMPLE) {
		if (!get_rules(N.get_rule_distribution(), logical_form_set, rules, cell.var.get_slice_variable()))
			return false;
	} else {
		if (!get_rules(N.get_rule_distribution(), rules))
			return false;
	}

	for (const rule<Semantics>& r : rules)
	{
#if !defined(NDEBUG)
		if (r.is_terminal())
			fprintf(stderr, "expand_nonterminal WARNING: `r` is a terminal rule.\n");
#endif
		if (Mode != MODE_GENERATE && position.end - position.start < r.nt.length)
			continue;
		if (USE_NONTERMINAL_PREITERATOR) {
			unsigned int* positions = (unsigned int*) alloca(sizeof(unsigned int) * (r.nt.length + 1));
			positions[0] = position.start;
			positions[r.nt.length] = position.end;
			push_nonterminal_iterator<AllowAmbiguous>(queue, G, parse_chart, sentence, morphology_parser,
					nonterminal, cell, syntax_state<Mode, Semantics>(r), logical_form_set, positions, 0.0);
		} else {
			if (!push_rule_states(queue, G, parse_chart, nonterminal,
					r, logical_form_set, cell, sentence, position))
			{
				free_rules(rules);
				return false;
			}
		}
	}
	free_rules(rules);
	return true;
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology>
inline bool expand_nonterminal(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	cell_value<Mode, Semantics>& cell,
	rule_state<Mode, Semantics>& state,
	const Semantics& logical_form_set,
	span position, double initial_prior)
{
	double outer, prior = 0.0;
	cell_value<Mode, Semantics>* cell_to_expand = &cell;
	const rule<Semantics>& r = state.syntax.get_rule();
	if (Mode != MODE_SAMPLE) {
		double old_prior = 0.0;
		if (Mode == MODE_PARSE)
			old_prior = min(state.cell->prior_probability, log_probability<false>(state.logical_form_set));
		outer_probability<false>(state, parse_chart, get_nonterminal<Mode>(G, state.nonterminal), old_prior, outer, prior);
		if (is_negative_inf(outer)) return true;
		outer += state.log_probability - old_prior;

		while (cell_to_expand->expanded && cell_to_expand->var.get_outer_probability() - cell_to_expand->prior_probability + 1.0e-12 < outer - prior) {
			/* the likelihood portion of the outer probability is larger than that of the previously-expanded cell */
			if (cell_to_expand->next == NULL) {
				cell_to_expand->next = (cell_value<Mode, Semantics>*) malloc(sizeof(cell_value<Mode, Semantics>));
				if (cell_to_expand->next == NULL || !init(*cell_to_expand->next,
						cell_to_expand->var.get_inner_probability(),
						cell_to_expand->var.get_inner_prior_probability(),
						cell_to_expand->var.get_initial_prior_probability()))
				{
					if (cell_to_expand->next != NULL) free(cell_to_expand->next);
					fprintf(stderr, "expand_nonterminal ERROR: Out of memory.\n");
					return false;
				}
				cell_to_expand->next->expanded = false;
				cell_to_expand = cell_to_expand->next;
				break;
			}
			cell_to_expand = cell_to_expand->next;
		}
	}

	/* check for any previously completed nonterminal states */
	if (!cell_to_expand->waiting_states.add(&state))
		return false;
	state.reference_count++;
	if (Mode != MODE_SAMPLE) {
		for (unsigned int i = 0; i < cell_to_expand->completed.length; i++) {
			nonterminal_state<Mode, Semantics>& nonterminal = cell_to_expand->completed[i];
			if (!push_invert_state(queue, G, parse_chart, state,
					nonterminal.logical_form_set, nonterminal.syntax, nonterminal.log_probability))
				return false;
		}
	} else if (cell_to_expand->completer != NULL && cell_to_expand->completer->iterator > 0) {
		if (!push_invert_state(
				queue, G, parse_chart, state, cell_to_expand->completer->logical_form_set,
				cell_to_expand->completer->syntax, cell_to_expand->completer->log_probability))
			return false;
	}

	/* cut off the search if this cell was previously expanded */
	if (cell_to_expand->expanded)  return true;
	cell_to_expand->expanded = true;

	/* we're expanding this cell, so set its outer probability */
	if (Mode != MODE_SAMPLE) {
		cell_to_expand->var.set_outer_probability(outer);
		cell_to_expand->prior_probability = prior;
	} else {
		cell_to_expand->var.init_slice_variable();
	}

	/* go ahead and expand this nonterminal at this position */
	/* TODO: even in parsing mode, we're assuming here that
	   whether or not a nonterminal is a preterminal is fixed */
	unsigned int next_nonterminal = r.nt.nonterminals[state.rule_position];
	const auto& next = get_nonterminal<Mode>(G, next_nonterminal);
	if (next.rule_distribution.has_terminal_rules()) {
		if (Mode == MODE_GENERATE) {
			if (!push_terminal_iterator<AllowAmbiguous>(queue, G, parse_chart,
					morphology_parser, next_nonterminal, *cell_to_expand, logical_form_set))
				return false;
		} else {
			unsigned int positions[] = { position.start, position.end };
			if (!push_nonterminal_iterator<AllowAmbiguous>(
					queue, G, parse_chart, sentence, morphology_parser, next_nonterminal, *cell_to_expand,
					syntax_state<Mode, Semantics>(sentence.tokens + position.start, position.end - position.start),
					logical_form_set, positions, 0.0))
				return false;
		}
	} if (next.rule_distribution.has_nonterminal_rules()) {
		if (!expand_nonterminal<AllowAmbiguous>(queue, G, parse_chart,
				sentence, morphology_parser, logical_form_set,
				next_nonterminal, *cell_to_expand, position))
			return false;
	}
	return true;
}

template<bool AllowAmbiguous, parse_mode Mode,
	typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology>
bool process_rule_state(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	rule_state<Mode, Semantics>& state)
{
	/* get the start and end position for this nonterminal */
	span position;
	if (Mode == MODE_GENERATE) {
		position.start = 0; position.end = 0;
	} else {
		position.start = state.positions[state.rule_position];
		position.end = state.positions[state.rule_position + 1];
	}

	/* apply the semantic transformation paired with the next nonterminal */
	Semantics& expanded_logical_forms = *((Semantics*) alloca(sizeof(Semantics)));
	if ((Mode == MODE_SAMPLE || Mode == MODE_PARSE || Mode == MODE_GENERATE)
	 && !apply(state.syntax.get_rule().nt.transformations[state.rule_position],
		 state.logical_form_set, expanded_logical_forms))
	{
		return false;
	}
	if (Mode == MODE_COMPUTE_BOUNDS)
		initialize_any(expanded_logical_forms);

	unsigned int next_nonterminal = state.syntax.get_rule().nt.nonterminals[state.rule_position];
	cell_list<Mode, Semantics>& cells = parse_chart.get_cells(next_nonterminal, position);
	if (Mode != MODE_GENERATE && position.length() == 1 && !sentence.tokens[position.start]->is_terminal()) {
		/* the next token is a subtree */
		double log_probability = sentence.subtree_probability(
				G, next_nonterminal, expanded_logical_forms, parse_chart.token_map, position.start);
		free(expanded_logical_forms);
		if (is_negative_inf(log_probability))
			return true;
		return complete_invert_state<AllowAmbiguous>(
				queue, G, parse_chart, sentence, morphology_parser, state,
				syntax_state<Mode, Semantics>(sentence.tokens[position.start]),
				state.logical_form_set, state.log_probability + log_probability);
	}

	auto expand_cell = [&](
			cell_value<Mode, Semantics>& cell,
			const Semantics& logical_form_set, double prior)
		{
			return expand_nonterminal<AllowAmbiguous>(
					queue, G, parse_chart, sentence, morphology_parser,
					cell, state, logical_form_set, position, prior);
		};
	bool result = cells.expand_cells(expanded_logical_forms, expand_cell);
	free(expanded_logical_forms);
	return result;
}

template<typename Semantics, typename Distribution, typename StringMapType>
bool process_terminal_iterator(
	agenda<MODE_GENERATE, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<MODE_GENERATE, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	terminal_iterator_state<MODE_GENERATE, Semantics>& iterator,
	bool& cleanup)
{
	const sequence& terminal = iterator.terminals[iterator.iterator].object;
	double inner_probability = iterator.terminals[iterator.iterator].log_probability;

	iterator.iterator++;
	if (iterator.iterator < iterator.terminal_count) {
		/* add the iterator back into the search queue if there are remaining items */
		parser_search_state<MODE_GENERATE, Semantics> state;
		state.terminal_iterator = &iterator;
		state.phase = PHASE_TERMINAL_ITERATOR;
		state.priority = compute_priority(iterator, parse_chart,
				get_nonterminal<MODE_GENERATE>(G, iterator.nonterminal));
		queue.push(state, *iterator.cell);
		cleanup = false;
	}

	return complete_nonterminal(
			queue, G, parse_chart, sentence, iterator.nonterminal,
			*iterator.cell, syntax_state<MODE_GENERATE, Semantics>(terminal),
			iterator.logical_form, inner_probability, NULL);
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType,
	typename std::enable_if<Mode != MODE_GENERATE>::type* = nullptr>
bool process_terminal_iterator(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	terminal_iterator_state<Mode, Semantics>& iterator,
	bool& cleanup)
{
	fprintf(stderr, "process_terminal_iterator ERROR: This function should only be called in generation mode.\n");
	return false;
}

template<parse_mode Mode, typename Semantics, typename Distribution, typename StringMapType>
bool process_nonterminal_iterator(
	agenda<Mode, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	nonterminal_iterator_state<Mode, Semantics>& iterator,
	bool& cleanup)
{
	const Semantics& logical_form = iterator.posterior[iterator.iterator].object;
	double inner_probability = iterator.posterior[iterator.iterator].log_probability;

	iterator.iterator++;
	if (iterator.iterator < iterator.posterior_length) {
		/* add the iterator back into the search queue if there are remaining items */
		parser_search_state<Mode, Semantics> state;
		state.nonterminal_iterator = &iterator;
		state.phase = PHASE_NONTERMINAL_ITERATOR;
		state.priority = compute_priority(iterator, parse_chart,
				get_nonterminal<Mode>(G, iterator.nonterminal));
		queue.push(state, *iterator.cell);
		cleanup = false;
	}

	double old_prior = 0.0;
	if (Mode != MODE_SAMPLE && Mode != MODE_GENERATE && Mode != MODE_COMPUTE_BOUNDS)
		old_prior = min(log_probability<false>(logical_form), iterator.cell->prior_probability);
	if (USE_NONTERMINAL_PREITERATOR) {
		double right, prior = old_prior;
		const rule<Semantics>& rule = iterator.syntax.get_rule();
		if (!rule.is_terminal() && (Mode == MODE_PARSE || Mode == MODE_GENERATE)) {
			right_probability(rule, logical_form, iterator.positions, parse_chart, old_prior, right, prior);
		} else {
			right = old_prior; prior = old_prior;
		}
		unsigned int start = (Mode == MODE_GENERATE) ? 0 : iterator.positions[0];
		unsigned int end = (Mode == MODE_GENERATE) ? 0 : iterator.positions[rule.is_terminal() ? 1 : rule.nt.length];
		if (!rule.is_terminal())
			return push_rule_states(queue, G, parse_chart, iterator.nonterminal, rule,
					logical_form, *iterator.cell, sentence, {start, end}, inner_probability - right);
	}
	return complete_nonterminal(queue, G, parse_chart, sentence, iterator.nonterminal,
			*iterator.cell, iterator.syntax, logical_form, inner_probability - old_prior, iterator.positions);
}

/* NOTE: this function assumes syntax.children is NULL */
template<typename Semantics, typename Distribution, typename StringMapType>
bool sample(
	grammar<Semantics, Distribution>& G,
	syntax_node<Semantics>*& syntax,
	chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const cell_value<MODE_SAMPLE, Semantics>& cell,
	const Semantics& logical_form,
	const tokenized_sentence<Semantics>& sentence)
{
	if (cell.completed.length == 0) {
		fprintf(stderr, "sample ERROR: There are no trees with positive probability.\n");
		free(syntax); syntax = NULL;
		return false;
	}

	double* probabilities = (double*) malloc(sizeof(double) * cell.completed.length);
	if (probabilities == NULL) {
		fprintf(stderr, "sample ERROR: Insufficient memory for probability array.\n");
		return false;
	}

	/* sample from this categorical distribution */
	normalize_exp(cell.completed.data, probabilities, (unsigned int) cell.completed.length);
	unsigned int sampled = sample_categorical(probabilities, 1.0, (unsigned int) cell.completed.length);
	const nonterminal_state<MODE_SAMPLE, Semantics>& nonterminal = cell.completed[sampled];
	free(probabilities);
	if (nonterminal.syntax.r.is_terminal()) {
		/* we've sampled a terminal symbol */
		if (!init(*syntax, nonterminal.syntax.r)) {
			free(syntax); syntax = NULL;
			return false;
		}
		return true;
	} else {
		/* we've sampled a production rule */
		if (!init(*syntax, nonterminal.syntax.r)) {
			free(syntax); syntax = NULL;
			return false;
		}

		/* recursively sample the descendant nodes */
		for (unsigned int i = 0; i < nonterminal.syntax.r.nt.length; i++) {
			Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
			if (!apply(nonterminal.syntax.r.nt.transformations[i], logical_form, transformed))
				return false;

			unsigned int start = nonterminal.positions[i];
			unsigned int end = nonterminal.positions[i + 1];
			unsigned int next_nonterminal = nonterminal.syntax.r.nt.nonterminals[i];
			if (end - start == 1 && !sentence.tokens[start]->is_terminal()) {
				syntax->children[i] = NULL;
				continue;
			}

			syntax->children[i] = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
			if (syntax->children[i] == NULL) {
				fprintf(stderr, "sample ERROR: Insufficient memory for syntax_node.\n");
				return false;
			}

			auto sample_cell = [&](
					cell_value<MODE_SAMPLE, Semantics>& cell,
					const Semantics& logical_form_set, double prior)
				{
					return sample(G, syntax->children[i], parse_chart, cell, logical_form_set, sentence);
				};
			cell_list<MODE_SAMPLE, Semantics>& cells =
					parse_chart.get_cells(next_nonterminal, {start, end});
			if (!cells.map_cells(transformed, sample_cell))
			{
				free(transformed);
				free(*syntax); free(syntax);
				syntax = NULL;
				return false;
			}
			free(transformed);
		}
		return true;
	}
}

template<typename Semantics>
inline bool is_sorted(const cell_value<MODE_PARSE, Semantics>& cell, double& best)
{
	if (cell.completed.length == 0) return true;

	double prev = min(log_probability<false>(cell.completed[0].logical_form_set), cell.prior_probability);
	prev += cell.completed[0].log_probability;
	best = max(best, prev);
	for (unsigned int l = 1; l < cell.completed.length; l++) {
		double prior = min(log_probability<false>(cell.completed[l].logical_form_set), cell.prior_probability);
		double current = prior + cell.completed[l].log_probability;
		if (current > prev + 1.0e-12)
			return false;
		best = max(best, current);
		prev = current;
	}

	return true;
}

template<typename Semantics, typename Distribution, typename StringMapType, typename Morphology>
inline bool update_outer_probabilities(
	agenda<MODE_PARSE, Semantics>& queue,
	grammar<Semantics, Distribution>& G,
	chart<MODE_PARSE, Semantics, StringMapType>& parse_chart,
	const tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const Semantics& logical_form,
	double log_search_priority)
{

/*for (unsigned int i = 0; i < sentence.length + 1; i++) {
	for (unsigned int j = 0; j < sentence.length - i + 1; j++) {
		for (unsigned int k = 0; k < G.nonterminals.length; k++) {
			for (auto entry : parse_chart.cells[i][j][k].cells) {
				const cell_value<MODE_PARSE, Semantics>& cell = *entry.value;
				double best = -std::numeric_limits<double>::infinity();
				if (!is_sorted(cell, best)) {
					fprintf(stderr, "WARNING: The list of completed nonterminals is not sorted.\n");
is_sorted(cell, best);
				}

				const cell_value<MODE_PARSE, Semantics>* next = cell.next;
				while (next != NULL) {
					double next_best = -std::numeric_limits<double>::infinity();
					if (!is_sorted(*next, next_best)) {
						fprintf(stderr, "WARNING: The list of completed nonterminals is not sorted.\n");
					} else if (next_best > best + 1.0e-12) {
						if (!std::isinf(best))
							fprintf(stderr, "WARNING: The first cell in the linked list contains a suboptimal nonterminal.\n");
						best = next_best;
					}
					next = next->next;
				}
			}
		}
	}
}
return;*/

	Semantics any;
	initialize_any(any);

	/* clear the search queue */
	for (parser_search_state<MODE_PARSE, Semantics> state : queue)
		free(state);
	queue.clear();

	/* clear the chart, tightening the inner probabilities at every cell */
	for (unsigned int i = 0; i < sentence.length + 1; i++) {
		for (unsigned int j = 0; j < sentence.length - i + 1; j++) {
			for (unsigned int k = 0; k < G.nonterminals.length; k++) {
				bool contains;
				cell_value<MODE_PARSE, Semantics>* any_cell = parse_chart.cells[i][j][k].cells.get(any, contains);
				if (contains && any_cell->completed.length > 0) {
//					double prior = min(log_probability<false>(any_cell->completed[0].logical_form_set), any_cell->prior_probability);
//					parse_chart.cells[i][j][k].set_inner_probability(prior + any_cell->completed[0].log_probability);
				}

				for (auto entry : parse_chart.cells[i][j][k].cells) {
					cell_value<MODE_PARSE, Semantics>& cell = *entry.value;
					cell_value<MODE_PARSE, Semantics>* curr = entry.value;

					do {
						if (curr->completed.length == 0) {
							cell.var.set_inner_prior_probability(min(cell.var.get_inner_prior_probability(),
									log_search_priority - curr->var.get_outer_probability() - curr->prior_probability));
						} else if (log_probability<false>(entry.key) < curr->prior_probability) {
							double prior = log_probability<false>(curr->completed[0].logical_form_set);
							cell.var.set_inner_prior_probability(curr->completed[0].log_probability
									+ prior - parse_chart.cells[i][j][k].inner_probability);
						} else {
							//cell.var.set_inner_prior_probability(min(cell.var.get_inner_prior_probability(),
							//		curr->completed[0].log_probability - parse_chart.cells[i][j][k].inner_probability));
						}
						curr = curr->next;
					} while (curr != NULL);

					/* clear the cell */
					cell.expanded = false;
					for (rule_state<MODE_PARSE, Semantics>* rule : cell.waiting_states) {
						core::free(*rule);
						if (rule->reference_count == 0)
							core::free(rule);
					}
					for (nonterminal_state<MODE_PARSE, Semantics>& state : cell.completed)
						core::free(state);
					cell.waiting_states.clear();
					cell.completed.clear();

					if (cell.next != NULL) {
						free(*cell.next);
						free(cell.next);
						cell.next = NULL;
					}
				}
			}
		}
	}

	/* re-expand the root cell */
	cell_list<MODE_PARSE, Semantics>& root_cells = parse_chart.get_cells(1, {0, sentence.length});
	auto expand_cell = [&](
			cell_value<MODE_PARSE, Semantics>& cell,
			const Semantics& logical_form_set, double prior)
		{
			if (cell.expanded) return true;
			cell.expanded = true;
			cell.prior_probability = prior;
			cell.var.set_outer_probability(prior);
			return expand_nonterminal(queue, G, parse_chart, sentence, morphology_parser, logical_form_set, 1, cell, {0, sentence.length});
		};
	/* TODO: should parse_chart.cell_count be re-initialized to 0 here? */
	return root_cells.expand_cells(logical_form, expand_cell);

	/*std::multiset<parser_search_state<MODE_PARSE, Semantics>> new_queue;
	for (parser_search_state<MODE_PARSE, Semantics> state : queue) {
		switch (state.phase) {
		case PHASE_RULE:
			state.priority = compute_priority(*state.rule, parse_chart,
				get_nonterminal<MODE_PARSE>(G, state.rule->nonterminal));
			break;
		case PHASE_NONTERMINAL_ITERATOR:
			state.priority = compute_priority(*state.nonterminal_iterator, parse_chart,
				get_nonterminal<MODE_PARSE>(G, state.nonterminal_iterator->nonterminal));
			break;
		case PHASE_INVERT_ITERATOR:
			state.priority = compute_priority(*state.invert_iterator, parse_chart,
				get_nonterminal<MODE_PARSE>(G, state.invert_iterator->rule->nonterminal));
			break;
		case PHASE_RULE_COMPLETER:
		case PHASE_TERMINAL_ITERATOR:
			fprintf(stderr, "update_outer_probabilities ERROR: Unimplemented.\n");
			exit(EXIT_FAILURE);
		}
		new_queue.insert(state);
	}
	std::swap(new_queue, queue);*/
}

template<parse_mode Mode, typename Semantics,
	typename Distribution, typename StringMapType, typename Morphology,
	typename std::enable_if<Mode != MODE_PARSE>::type* = nullptr>
inline void update_outer_probabilities(
		agenda<Mode, Semantics>& queue,
		grammar<Semantics, Distribution>& G,
		chart<Mode, Semantics, StringMapType>& parse_chart,
		const tokenized_sentence<Semantics>& sentence,
		const Morphology& morphology_parser,
		const Semantics& logical_form,
		double log_search_priority)
{ }

enum parse_result {
	PARSE_SUCCESS,
	PARSE_FAILURE,
	PARSE_TIME_EXCEEDED
};

template<bool AllowAmbiguous, bool Quiet, unsigned int K = 1,
		parse_mode Mode, typename Semantics,
		typename Distribution, typename StringMapType,
		typename Morphology>
parse_result parse(
	grammar<Semantics, Distribution>& G,
	chart<Mode, Semantics, StringMapType>& parse_chart,
	const Semantics& logical_form,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	unsigned int time_limit = UINT_MAX)
{
	agenda<Mode, Semantics> queue;

	/* expand the root cell to create the initial agenda items */
	cell_list<Mode, Semantics>& root_cells = parse_chart.get_cells(1, {0, sentence.length});
	auto expand_cell = [&](
			cell_value<Mode, Semantics>& cell,
			const Semantics& logical_form_set, double prior)
		{
			cell.prior_probability = prior;
			if (Mode != MODE_SAMPLE)
				cell.var.set_outer_probability(prior);
			if (cell.expanded) return true;

			cell.expanded = true;
			return expand_nonterminal<AllowAmbiguous>(queue, G, parse_chart, sentence,
					morphology_parser, logical_form_set, 1, cell, {0, sentence.length});
		};
	if (!root_cells.expand_cells(logical_form, expand_cell))
		return PARSE_FAILURE;
	cell_value<Mode, Semantics>& root_cell = root_cells.get_cell(logical_form);

	timer stopwatch; parse_result result = PARSE_SUCCESS;
	double last_log_priority = std::numeric_limits<double>::infinity();
	unsigned int completed_derivations = 0;
	double best_derivation_probabilities[K];
	for (unsigned int i = 0; i < K; i++)
		best_derivation_probabilities[i] = -std::numeric_limits<double>::infinity();
	for (queue.iteration = 0; !queue.is_empty(); queue.iteration++)
	{
/*if (Mode == MODE_PARSE && queue.iteration == 144)
fprintf(stderr, "DEBUG: BREAKPOINT\n");*/

		/* pop the next item from the priority queue */
		parser_search_state<Mode, Semantics> state = queue.pop(queue.iteration);
		last_log_priority = log(queue.priority(root_cell));

/*if (Mode == MODE_PARSE) {
default_scribe scribe;
print("[ITERATION ", stderr); print(queue.iteration, stderr); print("] ", stderr);
print(state, stderr, scribe, *debug_terminal_printer); print("\n\n", stderr);
}*/
		bool cleanup = true;
		switch (state.phase) {
		case PHASE_RULE:
			process_rule_state<AllowAmbiguous>(queue, G, parse_chart, sentence, morphology_parser, *state.rule);
			free(*state.rule);
			if (state.rule->reference_count == 0)
				free(state.rule);
			break;
		case PHASE_TERMINAL_ITERATOR:
			process_terminal_iterator(queue, G, parse_chart, sentence, *state.terminal_iterator, cleanup);
			if (cleanup) { free(*state.terminal_iterator); free(state.terminal_iterator); }
			break;
		case PHASE_NONTERMINAL_ITERATOR:
			process_nonterminal_iterator(queue, G, parse_chart, sentence, *state.nonterminal_iterator, cleanup);
			if (cleanup) { free(*state.nonterminal_iterator); free(state.nonterminal_iterator); }
			break;
		case PHASE_INVERT_ITERATOR:
			process_invert_iterator<AllowAmbiguous>(queue, G, parse_chart, sentence, morphology_parser, *state.invert_iterator, cleanup);
			if (cleanup) { free(*state.invert_iterator); free(state.invert_iterator); }
			break;
		case PHASE_RULE_COMPLETER:
			process_rule_completer(queue, G, parse_chart, *state.rule_completer, cleanup);
			/* the completer is cleaned up when the chart is freed */
			break;
		}

		/* check termination condition */
		if (Mode == MODE_PARSE || Mode == MODE_GENERATE) {
#if defined(NDEBUG)
			if (stopwatch.milliseconds() > time_limit) {
				if (!Quiet) fprintf(stderr, "%sparse: Reached time limit; terminating search...\n", parser_prefix);
				result = PARSE_TIME_EXCEEDED; break;
			}
#endif

			if (root_cell.template has_completed_parses<AllowAmbiguous>(
					last_log_priority, completed_derivations, best_derivation_probabilities)) {
				if (!Quiet) printf("%sTerminating search after visiting %u states.\n", parser_prefix, queue.iteration);
				break;
			}
		}


		if (USE_BEAM_SEARCH && (Mode == MODE_PARSE || Mode == MODE_GENERATE))
			queue.prune_beam();

		/*auto first = queue.cbegin();
		while (Mode == MODE_PARSE && !queue.is_empty() && (first->priority < minimum_priority || first->priority == 0.0)) {
			parser_search_state<Mode, Semantics> state = *first;
			free(state);
			queue.erase(first);
			first = queue.cbegin();
		}*/
	}

	return result;
}

template<typename Semantics, typename Distribution, typename StringMapType, typename Morphology>
inline bool sample(
	syntax_node<Semantics>*& syntax,
	grammar<Semantics, Distribution>& G,
	chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const Semantics& logical_form,
	tokenized_sentence<Semantics>& sentence,
	Morphology& morphology_parser)
{
	if (parse<false, true>(G, parse_chart, logical_form, sentence, morphology_parser) != PARSE_SUCCESS)
		return false;

	auto expand_cell = [&](
			cell_value<MODE_SAMPLE, Semantics>& cell,
			const Semantics& logical_form_set, double prior)
		{
			return sample(G, syntax, parse_chart, cell, logical_form_set, sentence);
		};
	cell_list<MODE_SAMPLE, Semantics>& cells = parse_chart.get_cells(1, {0, sentence.length});
	bool result = cells.map_cells(logical_form, expand_cell);
	return result;
}

template<typename Semantics, typename Distribution, typename StringMapType>
bool sample_chart(unsigned int nonterminal_id,
	const syntax_node<Semantics>& syntax,
	grammar<Semantics, Distribution>& G,
	chart<MODE_SAMPLE, Semantics, StringMapType>& parse_chart,
	const Semantics& logical_form,
	unsigned int start, unsigned int& end)
{
	nonterminal<Semantics, Distribution>& N = G.nonterminals[nonterminal_id - 1];
	const array<weighted_feature_set<double>>* posterior = log_conditional<true, false>(N.rule_distribution, syntax.right, logical_form);
	if (posterior == NULL) return false;

	if (syntax.is_terminal()) {
		end = start + syntax.right.t.length;
	} else {
		unsigned int k = start;
		for (unsigned int i = 0; i < syntax.right.nt.length; i++) {
			if (syntax.children[i] == NULL) {
				end = k + 1;
				continue;
			}

			Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
			if (!apply(syntax.right.nt.transformations[i], logical_form, transformed))
				return false;

			if (!sample_chart(syntax.right.nt.nonterminals[i],
				*syntax.children[i], G, parse_chart, transformed, k, end))
			{
				free(transformed);
				return false;
			}
			free(transformed);
			k = end;
		}
	}

	double slice_variable = sample_uniform<double>() * exp(posterior->data[0].log_probability);

	auto init_slice_variable = [=](
			cell_value<MODE_SAMPLE, Semantics>& cell,
			const Semantics& logical_form_set, double prior)
		{
			if (!cell.expanded)
				cell.var.init_slice_variable(slice_variable);
			return true;
		};
	cell_list<MODE_SAMPLE, Semantics>& cells = parse_chart.get_cells(nonterminal_id, {start, end});
	return cells.expand_cells(logical_form, init_slice_variable);
}

template<typename Semantics, typename Distribution,
	typename Morphology, typename StringMapType>
inline bool sample(syntax_node<Semantics>*& syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics& logical_form,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const StringMapType& token_map,
	unsigned int nonterminal = 1)
{
	/* perform block sampling */
	chart<MODE_SAMPLE, Semantics, StringMapType> parse_chart = chart<MODE_SAMPLE, Semantics, StringMapType>(sentence.length, G.nonterminals.length, token_map);
	if (!sample(syntax, G, parse_chart, logical_form, sentence, morphology_parser))
		return false;

	G.clear();
	return true;
}

template<typename Semantics, typename Distribution, typename Morphology, typename StringMapType>
bool resample(syntax_node<Semantics>*& syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics& logical_form,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const StringMapType& token_map,
	unsigned int nonterminal = 1)
{
	/* compute the (fully factorized) probability of the old tree */
	syntax_node<Semantics> old_tree = *syntax;

	double old_probability = 0.0, new_probability = 0.0;
	if (!remove_tree(nonterminal, *syntax, logical_form, G, token_map, old_probability)) return false;
	double old_factored_probability = log_probability(G, *syntax, logical_form, token_map);
	chart<MODE_SAMPLE, Semantics, StringMapType> parse_chart = chart<MODE_SAMPLE, Semantics, StringMapType>(sentence.length, G.nonterminals.length, token_map);

	/* sample the slice variables for the occupied cells */
	unsigned int end;
	if (!sample_chart(nonterminal, *syntax, G, parse_chart, logical_form, 0, end))
		return false;
	free(*syntax);

	/* perform block sampling */
	if (!sample(syntax, G, parse_chart, logical_form, sentence, morphology_parser))
		return false;

	/* compute the (fully factorized) probability of the new tree */
	double new_factored_probability = log_probability(G, *syntax, logical_form, token_map);
	if (!add_tree(nonterminal, *syntax, logical_form, G, token_map, new_probability))
		return false;

	/* perform Metropolis-Hastings rejection test */
	double acceptance_probability = exp(old_factored_probability + new_probability - old_probability - new_factored_probability);
	if (!sample_bernoulli(acceptance_probability)) {
		/* reject the new tree */
		if (!remove_tree(nonterminal, *syntax, logical_form, G, token_map, old_probability)
		 || !add_tree(nonterminal, old_tree, logical_form, G, token_map, new_probability))
			return false;
		free(*syntax);
		*syntax = old_tree;
	}
	G.clear();
	return true;
}

template<typename Semantics, typename Distribution, typename StringMapType, typename Morphology>
bool resample(syntax_node<Semantics>** syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics* logical_forms,
	tokenized_sentence<Semantics>* sentences,
	const Morphology& morphology_parser,
	unsigned int* nonterminals,
	unsigned int sentence_count)
{
	for (unsigned int i = 0; i < sentence_count; i++) {
		double old_probability = 0.0;
		if (!remove_tree(nonterminals[i], *syntax[i], logical_forms[i], G, old_probability)) return false;
	}

	for (unsigned int i = 0; i < sentence_count; i++) {
		chart<MODE_SAMPLE, Semantics, StringMapType> parse_chart = chart<MODE_SAMPLE, Semantics, StringMapType>(sentences[i].length, G.nonterminals.length);

		/* sample the slice variables for the occupied cells */
		unsigned int end;
		if (!sample_chart(nonterminals[i], *syntax[i], G, parse_chart, logical_forms[i], 0, end))
			return false;
		free(*syntax[i]);

		/* perform block sampling */
		if (!sample(syntax[i], G, parse_chart, logical_forms[i], sentences[i], morphology_parser))
			return false;

		/* compute the (fully factorized) probability of the new tree */
		double new_probability;
		if (!add_tree(nonterminals[i], *syntax[i], logical_forms[i], G, new_probability))
			return false;
		G.clear();
	}
	return true;
}

template<bool AllowAmbiguous, typename Semantics,
	typename Distribution, typename Morphology,
	typename StringMapType>
bool reparse(syntax_node<Semantics>*& syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics& logical_form,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const StringMapType& token_map,
	unsigned int nonterminal = 1)
{
	double old_probability = 0.0, new_probability = 0.0;
	if (!remove_tree(nonterminal, *syntax, logical_form, G, old_probability)) return false;

	/* first compute upper bounds on the inner probabilities */
	chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType> syntax_chart =
			chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType>(sentence.length, G.nonterminals.length, token_map);
	if (parse<AllowAmbiguous, true>(G, syntax_chart, logical_form, sentence, morphology_parser) != PARSE_SUCCESS)
		return false;

	/* construct the chart for the semantic parser */
	chart<MODE_PARSE, Semantics, StringMapType> parse_chart = chart<MODE_PARSE, Semantics, StringMapType>(sentence.length, G.nonterminals.length, token_map);

	/* initialize the inner probabilities */
	for (unsigned int i = 0; i < sentence.length + 1; i++) {
		for (unsigned int j = 0; j < sentence.length - i + 1; j++) {
			for (unsigned int k = 0; k < G.nonterminals.length; k++) {
				cell_list<MODE_COMPUTE_BOUNDS, Semantics>& value = syntax_chart.cells[i][j][k];
				cell_list<MODE_PARSE, Semantics>& cells = parse_chart.get_cells(k + 1, {i, i + j});
				double inner = compute_inner_probability(&value.cell);
				cells.set_inner_probability(inner);
			}
		}
	}
	parse_chart.compute_max_inner_probabilities(sentence.length, G.nonterminals.length);

	parse_result result = parse<AllowAmbiguous, true>(G, parse_chart, logical_form, sentence, morphology_parser);
	if (result == PARSE_FAILURE) return false;

	/* return the best parse */
	cell_value<MODE_PARSE, Semantics>& root_cell = parse_chart.get_cells(nonterminal, {0, sentence.length}).get_cell(logical_form);
	const nonterminal_state<MODE_PARSE, Semantics>* best_parse = NULL;
	root_cell.template get_best_parse<AllowAmbiguous>(&best_parse);
	if (result == PARSE_SUCCESS && best_parse == NULL) {
		free(*syntax);
		*syntax = best_parse->syntax.tree;
	}

	if (!add_tree(nonterminal, *syntax, logical_form, G, new_probability))
		return false;
	G.clear();
	return true;
}

template<typename Semantics>
struct internal_node {
	unsigned int nonterminal;
	syntax_node<Semantics>* node;
	Semantics logical_form;

	static inline void swap(internal_node<Semantics>& first, internal_node<Semantics>& second) {
		core::swap(first.nonterminal, second.nonterminal);
		core::swap(first.node, second.node);
		core::swap(first.logical_form, second.logical_form);
	}

	static inline void free(internal_node<Semantics>& n) {
		core::free(n.logical_form);
	}
};

template<typename T>
inline void free_array(T* objects, unsigned int length) {
	for (unsigned int i = 0; i < length; i++)
		free(objects[i]);
	free(objects);
}

template<typename Semantics>
bool remove_subtree(
		syntax_node<Semantics>*& syntax,
		const Semantics& logical_form,
		unsigned int subtree_depth,
		array<syntax_node<Semantics>*>& tokens,
		array<internal_node<Semantics>>& queue)
{
	if (syntax->is_terminal())
		return tokens.add(syntax);

	if (syntax->children != NULL) {
		for (unsigned int i = 0; i < syntax->right.length; i++) {
			Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
			if (!apply(syntax->right.transformations[i], logical_form, transformed))
				return false;

			if (subtree_depth == 0) {
				if (!tokens.add(syntax->children[i]))
					return false;
				if (!syntax->children[i]->is_terminal()) {
					if (!queue.add({syntax->right.nonterminals[i], syntax->children[i], transformed}))
						return false;
					syntax->children[i] = NULL;
				}
			} else if (!remove_subtree(syntax->children[i],
					transformed, subtree_depth - 1, tokens, queue))
			{
				free(transformed);
				return false;
			}
			free(transformed);
		}
	}
	return true;
}

template<typename Semantics, typename Distribution>
unsigned int add_subtree(
		grammar<Semantics, Distribution>& G,
		syntax_node<Semantics>*& syntax,
		const Semantics& logical_form,
		syntax_node<Semantics>** tokens,
		array<internal_node<Semantics>>& queue,
		unsigned int index)
{
	if (syntax->is_terminal())
		return syntax->right.length;

	unsigned int width = 0;
	for (unsigned int i = 0; i < syntax->right.length; i++) {
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(syntax->right.transformations[i], logical_form, transformed)) {
			fprintf(stderr, "add_subtree ERROR: Unable to transform logical form.\n");
			return false;
		}

		if (syntax->children[i] == NULL) {
			syntax->children[i] = tokens[index + width];
			width++;

			double dummy;
			if (!remove_tree(
					queue[queue.length].nonterminal, *queue[queue.length].node,
					queue[queue.length].logical_form, G, dummy))
				return false;
			core::free(queue[queue.length].logical_form);
			queue[queue.length].nonterminal = syntax->right.nonterminals[i];
			queue[queue.length].node = syntax->children[i];
			queue[queue.length].logical_form = transformed;
			free(transformed);
			if (!add_tree(
					queue[queue.length].nonterminal, *queue[queue.length].node,
					queue[queue.length].logical_form, G, dummy))
				return false;
			queue.length++;
		} else {
			width += add_subtree(G, syntax->children[i], transformed, tokens, queue, index + width);
			free(transformed);
		}
	}
	return width;
}

template<typename Semantics>
bool add_tree_to_queue(
		array<internal_node<Semantics>>& queue,
		syntax_node<Semantics>*& syntax,
		const Semantics& logical_form,
		unsigned int nonterminal,
		unsigned int& depth,
		unsigned int subtree_depth)
{
	if (syntax->is_terminal())
		return true;
	//syntax->reference_count++;

	for (unsigned int i = 0; i < syntax->right.length; i++) {
		unsigned int child_depth = 0;
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(syntax->right.transformations[i], logical_form, transformed)
		 || !add_tree_to_queue(queue, syntax->children[i], transformed, syntax->right.nonterminals[i], child_depth, subtree_depth))
			return false;
		free(transformed);
		depth = max(depth, child_depth + 1);
	}
	return (depth < subtree_depth + 1 || queue.add({nonterminal, syntax, logical_form}));
}

template<typename Semantics, typename Distribution>
bool resample_locally(syntax_node<Semantics>*& syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics& logical_form,
	unsigned int subtree_depth)
{
	unsigned int depth = 0;
	array<internal_node<Semantics>> queue(16);
	if (!add_tree_to_queue(queue, syntax, logical_form, 1, depth, subtree_depth))
		return false;
	if (queue.length == 0) {
		queue.add({1, syntax, logical_form});
	} else {
		shuffle(queue);
	}

	unsigned int index = 0;
	array<syntax_node<Semantics>*> tokens(16);
	while (index < queue.length) {
		syntax_node<Semantics>*& node = queue[index].node;
		unsigned int nonterminal = queue[index].nonterminal;
		const Semantics& logical_form = queue[index].logical_form;
		index++;

		unsigned int old_queue_length = queue.length;
		if (!remove_subtree(node, logical_form, subtree_depth, tokens, queue))
			return false;
		auto sentence = tokenized_sentence<Semantics>(tokens.data, tokens.length);
		if (!resample(node, G, logical_form, sentence, nonterminal))
			return false;

		/* splice the new subtree back into the full derivation tree */
		queue.length = old_queue_length;
		if (!add_subtree(G, node, logical_form, sentence.tokens, queue, 0))
			return false;
		tokens.clear();

		/* choose next nodes to sample */
		/*queue.length = old_queue_length;
		if (!node->is_terminal()) {
			for (unsigned int i = 0; i < node->right.length; i++) {
				if (node->children[i]->is_terminal())
					continue;

				Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
				apply(node->right.transformations[i], logical_form, transformed); // TODO: if this returns false, `transformed` is uninitialized
				queue.add({node->right.nonterminals[i], node->children[i], transformed});
				free(transformed);
			}
		}*/
		break;
	}
	return true;
}

template<typename Semantics>
bool find_subtrees(
		syntax_node<Semantics>* syntax,
		const rule<Semantics>& subtree,
		const Semantics& logical_form,
		array<internal_node<Semantics>>& queue,
		unsigned int& subtree_count,
		unsigned int nonterminal = 1)
{
	if (syntax->is_terminal())
		return true;

	unsigned int old_queue_length = queue.length;
	unsigned int descendant_subtree_count = 0;
	for (unsigned int i = 0; i < syntax->right.length; i++) {
		Semantics& transformed = *((Semantics*) alloca(sizeof(Semantics)));
		if (!apply(syntax->right.transformations[i], logical_form, transformed)
		 || !find_subtrees(syntax->children[i], subtree, transformed, queue, descendant_subtree_count, syntax->right.nonterminals[i]))
			return false;
		free(transformed);
	}

	if (syntax->right == subtree) {
		descendant_subtree_count++;
		if (sample_uniform(descendant_subtree_count) == 0) {
			queue.length = old_queue_length;
			if (!queue.add({nonterminal, syntax, logical_form}))
				return false;
		}
	}
	subtree_count += descendant_subtree_count;
	return true;
}

template<typename Semantics, typename Distribution>
bool resample_type(
	const rule<Semantics>& type,
	syntax_node<Semantics>** syntax,
	grammar<Semantics, Distribution>& G,
	const Semantics* logical_forms,
	unsigned int sentence_count,
	unsigned int subtree_depth)
{
	/* find every occurrence of this rule in every tree */
	array<internal_node<Semantics>> queue(16);
	for (unsigned int i = 0; i < sentence_count; i++) {
		unsigned int subtree_count = 0;
		if (!find_subtrees(syntax[i], type, logical_forms[i], queue, subtree_count))
			return false;
	}
	if (queue.length == 0)
		return true;
	shuffle(queue);

	/* remove all of the subtrees */
	array<syntax_node<Semantics>*> tokens(16);
	tokenized_sentence<Semantics>* sentences = (tokenized_sentence<Semantics>*)
			malloc(sizeof(tokenized_sentence<Semantics>) * queue.length);
	syntax_node<Semantics>** syntax_sites = (syntax_node<Semantics>**)
			malloc(sizeof(syntax_node<Semantics>*) * queue.length);
	Semantics* logical_form_sites = (Semantics*) malloc(sizeof(Semantics) * queue.length);
	unsigned int* nonterminal_sites = (unsigned int*) malloc(sizeof(unsigned int) * queue.length);
	if (sentences == NULL || syntax_sites == NULL || logical_form_sites == NULL || nonterminal_sites == NULL) {
		if (sentences != NULL) free(sentences);
		if (syntax_sites != NULL) free(syntax_sites);
		if (logical_form_sites != NULL) free(logical_form_sites);
		if (nonterminal_sites != NULL) free(nonterminal_sites);
		fprintf(stderr, "resample_type ERROR: Out of memory.\n");
		return false;
	}
	unsigned int site_count = queue.length;
	for (unsigned int i = 0; i < site_count; i++) {
		syntax_sites[i] = queue[i].node;
		logical_form_sites[i] = queue[i].logical_form;
		nonterminal_sites[i] = queue[i].nonterminal;

		if (!remove_subtree(syntax_sites[i], logical_form_sites[i], subtree_depth, tokens, queue))
			return false;
		if (!init(sentences[i], tokens.data, tokens.length)) {
			free_array(logical_form_sites, i);
			free_array(sentences, site_count);
			free(syntax_sites); free(nonterminal_sites);
			return false;
		}
		tokens.clear();
	}
	queue.length = site_count;

	/* resample the subtrees, one by one */
	if (!resample(syntax_sites, G, logical_form_sites, sentences, nonterminal_sites, site_count)) {
		free_array(logical_form_sites, site_count);
		free_array(sentences, site_count);
		free(syntax_sites); free(nonterminal_sites);
		return false;
	}

	/* splice each subtree back into their respective derivation trees */
	for (unsigned int i = 0; i < site_count; i++) {
		if (!add_subtree(G, syntax_sites[i], logical_form_sites[i], sentences[i].tokens, queue, 0)) {
			free_array(logical_form_sites, site_count);
			free_array(sentences, site_count);
			free(syntax_sites); free(nonterminal_sites);
			return false;
		}
	}

	free_array(logical_form_sites, site_count);
	free_array(sentences, site_count);
	free(syntax_sites); free(nonterminal_sites);
	return true;
}

template<parse_mode Mode, typename Semantics, typename std::enable_if<Mode == MODE_COMPUTE_BOUNDS>::type* = nullptr>
inline double compute_inner_probability(
	const cell_value<Mode, Semantics>* cell)
{
	double inner = -std::numeric_limits<double>::infinity();
	while (cell != NULL) {
		for (const nonterminal_state<Mode, Semantics>& completed : cell->completed)
			inner = max(inner, completed.log_probability);
		cell = cell->next;
	}
	return inner;
}

template<bool AllowAmbiguous, bool Quiet, unsigned int K = 1,
	typename Semantics, typename Distribution,
	typename Morphology, typename StringMapType>
bool parse(
	syntax_node<Semantics>* syntax,
	unsigned int& derivation_count,
	const Semantics& logical_form_input,
	Semantics* logical_form_output,
	grammar<Semantics, Distribution>& G,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	const StringMapType& token_map,
	unsigned int time_limit = UINT_MAX)
{
	/* first compute upper bounds on the inner probabilities */
	chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType> syntax_chart(sentence.length, G.nonterminals.length, token_map);
	if (parse<AllowAmbiguous, true>(G, syntax_chart, logical_form_input, sentence, morphology_parser, time_limit) != PARSE_SUCCESS)
		return false;

	/* construct the chart for the semantic parser */
	chart<MODE_PARSE, Semantics, StringMapType> parse_chart(sentence.length, G.nonterminals.length, token_map);

	/* initialize the inner probabilities */
	for (unsigned int i = 0; i < sentence.length + 1; i++) {
		for (unsigned int j = 0; j < sentence.length - i + 1; j++) {
			for (unsigned int k = 0; k < G.nonterminals.length; k++) {
				cell_list<MODE_COMPUTE_BOUNDS, Semantics>& value = syntax_chart.cells[i][j][k];
				cell_list<MODE_PARSE, Semantics>& cells = parse_chart.get_cells(k + 1, {i, i + j});
				double inner = compute_inner_probability(&value.cell);
				cells.set_inner_probability(inner);
			}
		}
	}
	parse_chart.compute_max_inner_probabilities(sentence.length, G.nonterminals.length);

	parse_result result = parse<AllowAmbiguous, Quiet, K>(G, parse_chart, logical_form_input, sentence, morphology_parser, time_limit);
	if (result == PARSE_FAILURE)
		return false;

	/* return the best parse */
	cell_value<MODE_PARSE, Semantics>& root_cell = parse_chart.get_cells(1, {0, sentence.length}).get_cell(logical_form_input);
	const nonterminal_state<MODE_PARSE, Semantics>* best_parses[K];
	derivation_count = root_cell.template get_best_parse<AllowAmbiguous, K>(best_parses);
	if (derivation_count == 0)
		return false;

	for (unsigned int i = 0; i < derivation_count; i++) {
		syntax[i] = best_parses[i]->syntax.tree;
		logical_form_output[i] = best_parses[i]->logical_form_set;
	}
	return true;
}

template<unsigned int K = 1, typename Semantics,
	typename Distribution, typename Morphology>
bool generate(
	syntax_node<Semantics>* syntax,
	unsigned int& derivation_count,
	const Semantics& logical_form,
	grammar<Semantics, Distribution>& G,
	const Morphology& morphology_parser,
	hash_map<string, unsigned int>& token_map,
	unsigned int time_limit = UINT_MAX)
{
	/* construct the chart for the semantic parser */
	tokenized_sentence<Semantics> empty_sentence = tokenized_sentence<Semantics>(sequence(NULL, 0));
	chart<MODE_GENERATE, Semantics, decltype(token_map)> parse_chart(0, G.nonterminals.length, token_map);
	for (unsigned int k = 0; k < G.nonterminals.length; k++) {
		cell_list<MODE_GENERATE, Semantics>& cells = parse_chart.get_cells(k + 1, {0, 0});
		cells.set_inner_probability(0.0);
	}
	parse_result result = parse<false, true, K>(G, parse_chart, logical_form, empty_sentence, morphology_parser, time_limit);
	if (result == PARSE_FAILURE || result == PARSE_TIME_EXCEEDED)
		return false;

	/* return the best parse */
	cell_value<MODE_GENERATE, Semantics>& root_cell = parse_chart.get_cells(1, {0, 0}).get_cell(logical_form);
	const nonterminal_state<MODE_GENERATE, Semantics>* best_parses[K];
	derivation_count = root_cell.template get_best_parse<false, K>(best_parses);
	if (derivation_count == 0 || result == PARSE_TIME_EXCEEDED)
		return false;

	for (unsigned int i = 0; i < derivation_count; i++)
		syntax[i] = best_parses[i]->syntax.tree;
	return true;
}


/**
 * A branch-and-bound algorithm for parsing.
 */

#include <thread>

template<typename Semantics>
struct branch_and_bound_state {
	Semantics* logical_form_set;
	double upper_bound;
};

template<typename Semantics>
inline bool operator < (
		const branch_and_bound_state<Semantics>& first,
		const branch_and_bound_state<Semantics>& second)
{
	return first.upper_bound < second.upper_bound;
}

template<typename Semantics>
inline void free_queue(array<branch_and_bound_state<Semantics>>& queue) {
	for (unsigned int i = 0; i < queue.length; i++) {
		free(*queue[i].logical_form_set);
		free(queue[i].logical_form_set);
	}
}

template<typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology>
inline bool bound(
	double& upper_bound, const Semantics& set,
	grammar<Semantics, Distribution>& G,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser)
{
	chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType> syntax_chart =
			chart<MODE_COMPUTE_BOUNDS, Semantics, StringMapType>(sentence.length, G.nonterminals.length);
	if (!parse(G, syntax_chart, set, sentence, morphology_parser))
		return false;

	bool contains;
	auto cell = syntax_chart.get_cells(1, {0, sentence.length}).cells.get(set, contains);
	if (!contains) {
		fprintf(stderr, "DEBUG: WTF?\n");
		return false;
	}
	upper_bound = cell.value->completed[0].log_probability;
	return true;
}

template<typename Semantics, typename Distribution>
bool bound(array<Semantics*>& sets,
	grammar<Semantics, Distribution>& G,
	tokenized_sentence<Semantics>& sentence,
	double log_probability_bound,
	array<branch_and_bound_state<Semantics>>& queue,
	std::mutex& queue_lock)
{
	queue_lock.lock();
	if (!queue.ensure_capacity(queue.length + sets.length)) {
		queue_lock.unlock();
		return false;
	}
	queue_lock.unlock();

	for (Semantics* set : sets) {
		double upper_bound;
		if (!bound(upper_bound, *set, G, sentence))
			return false;
		if (log_probability_bound > upper_bound) {
			/* this set is worse than our best solution so far, so prune it */
			free(*set); free(set); continue;
		}

		queue_lock.lock();
		queue[queue.length] = {set, upper_bound};
		queue.length++;
		std::push_heap(queue.data, queue.data + queue.length);
		queue_lock.unlock();
	}
	return true;
}

template<typename Semantics, typename Distribution,
	typename StringMapType, typename Morphology, typename... Args>
bool parse_branch_and_bound(
	syntax_node<Semantics>& syntax,
	Semantics& logical_form,
	array<Semantics*>& initial_partition,
	grammar<Semantics, Distribution>& G,
	tokenized_sentence<Semantics>& sentence,
	const Morphology& morphology_parser,
	Args&&... split_args)
{
	initialize_any(logical_form);
	double best_score = -std::numeric_limits<double>::infinity();
	syntax.children = NULL;
	if (!init(syntax.right, 0))
		return false;
	syntax.reference_count = 1;

	std::mutex queue_lock; timer stopwatch;
	array<branch_and_bound_state<Semantics>> queue(64);
	if (!bound(initial_partition, G, sentence, best_score, queue, queue_lock)) {
		free_queue(queue);
		return false;
	}

	array<Semantics*> ambiguous_sets(16);
	array<Semantics*> unambiguous_sets(16);
	for (unsigned int iteration = 0; queue.length > 0; iteration++) {
		queue_lock.lock();
		std::pop_heap(queue.data, queue.data + queue.length);
		queue.length--;
		branch_and_bound_state<Semantics> state = queue[queue.length];
		queue_lock.unlock();

		/* check termination condition */
		if (best_score > state.upper_bound) {
			printf("parse_branch_and_bound: Terminating after %u branches.\n", iteration + 1);
			free(*state.logical_form_set);
			free(state.logical_form_set);
			break;
		}

		/* split the logical form set of this state */
		if (!split(state.logical_form_set, ambiguous_sets, unambiguous_sets, std::forward<Args>(split_args)...)) {
			free_queue(queue);
			return false;
		}
		free(*state.logical_form_set);
		free(state.logical_form_set);

		/* bound the sets containing more than one item */
		if (!bound(ambiguous_sets, G, sentence, best_score, queue, queue_lock)) {
			free_queue(queue);
			return false;
		}
		ambiguous_sets.clear();

		/* parse the singleton sets (containing only 1 logical form) */
		for (unsigned int i = 0; i < unambiguous_sets.length; i++)
		{
			/* construct the chart for the semantic parser */
			chart<MODE_PARSE, Semantics, StringMapType> parse_chart = chart<MODE_PARSE, Semantics, StringMapType>(sentence.length, G.nonterminals.length);
			for (unsigned int i = 0; i < sentence.length + 1; i++) {
				for (unsigned int j = 0; j < sentence.length - i + 1; j++) {
					for (unsigned int k = 0; k < G.nonterminals.length; k++) {
						cell_list<MODE_PARSE, Semantics>& cells = parse_chart.get_cells(k + 1, {i, i + j});
						cells.set_inner_probability(0.0);
					}
				}
			}

			if (!parse(G, parse_chart, *unambiguous_sets[i], sentence, morphology_parser))
				return false;
			free(*unambiguous_sets[i]);
			free(unambiguous_sets[i]);

			/* return the best parse */
			cell_list<MODE_PARSE, Semantics>& root_cells = parse_chart.get_cells(1, {0, sentence.length});
			const nonterminal_state<MODE_PARSE, Semantics>*  best_parse = root_cells.get_best_parse();
			if (best_parse == NULL) continue;
			if (best_parse->log_probability > best_score) {
				free(logical_form); free(syntax);
				best_score = best_parse->log_probability;
				logical_form = best_parse->logical_form_set;
				syntax = best_parse->syntax.tree;
			}
		}
		unambiguous_sets.clear();
	}

	free_queue(queue);
	return best_score != -std::numeric_limits<double>::infinity();
}

#endif /* PARSER_H_ */
