/**
 * hdp_grammar.h
 *
 *  Created on: Jul 18, 2015
 *      Author: asaparov
 */

#ifndef HDP_GRAMMAR_H_
#define HDP_GRAMMAR_H_

#include <core/lex.h>
#include <hdp/mcmc.h>
#include <cinttypes>

#include "grammar.h"
#include "morphology.h"

struct nonterminal_pair {
	unsigned int first;
	unsigned int second;
	double prior_probability;
};

struct nonterminal_pair_iterator {
	unsigned int first;
	unsigned int second;
	unsigned int nonterminal_count;

	template<typename V>
	nonterminal_pair_iterator(const dense_categorical<V>& prior) :
		first(1), second(1), nonterminal_count(prior.atom_count) { }

	inline bool has_next() const {
		return first <= nonterminal_count;
	}

	inline nonterminal_pair next() {
		nonterminal_pair pair;
		pair.first = first;
		pair.second = second;
		pair.prior_probability = 1.0 / (nonterminal_count * nonterminal_count);

		second++;
		if (second > nonterminal_count) {
			first++;
			second = 1;
		}
		return pair;
	}
};

template<typename NonterminalPrior, typename TerminalPrior>
struct rule_prior
{
	typedef double value_type;

	NonterminalPrior nonterminal_prior;
	TerminalPrior terminal_prior;
	double max_nonterminal_probability;
	double max_nonterminal_log_probability;

	rule_prior(const NonterminalPrior& nonterminal, const TerminalPrior& terminal)
		: nonterminal_prior(nonterminal), terminal_prior(terminal)
	{
		compute_max_nonterminal_probability();
	}

	rule_prior(const rule_prior<NonterminalPrior, TerminalPrior>& src)
		: nonterminal_prior(src.nonterminal_prior), terminal_prior(src.terminal_prior),
		  max_nonterminal_probability(src.max_nonterminal_probability),
		  max_nonterminal_log_probability(src.max_nonterminal_log_probability)
	{ }

	constexpr part_of_speech get_part_of_speech() const {
		return POS_OTHER;
	}

	template<typename Semantics>
	double probability(const rule<Semantics>& observation) const {
		if (observation.is_terminal()) {
			return terminal_prior.probability(sequence(observation.t.terminals, observation.t.length));
		} else {
			if (observation.nt.length != 2)
				return 0.0;
			auto nonterminals = array_multiset<unsigned int>(2);
			if (!get_nonterminals(nonterminals, observation)) exit(EXIT_FAILURE);
			double score = nonterminal_prior.probability(nonterminals)
				 / (array_length(Semantics::functions) * array_length(Semantics::functions));
			return score * pow(max_nonterminal_probability, 2 - observation.nt.length);
		}
	}

	template<typename Semantics>
	inline double probability(const array_multiset<rule<Semantics>>& observations) const {
		double product = 1.0;
		for (const auto& entry : observations.counts)
			product *= pow(probability(entry.key), entry.value);
		return product;
	}

	template<typename Semantics>
	double log_probability(const rule<Semantics>& observation) const {
		if (observation.is_terminal()) {
			return terminal_prior.log_probability(sequence(observation.t.terminals, observation.t.length));
		} else {
			if (observation.nt.length != 2)
				return -std::numeric_limits<double>::infinity();
			auto nonterminals = array_multiset<unsigned int>(2);
			if (!get_nonterminals(nonterminals, observation)) exit(EXIT_FAILURE);
			double score = nonterminal_prior.log_probability(nonterminals) - 2 * Semantics::log_function_count;
			return score + max_nonterminal_log_probability * (2 - observation.nt.length);
		}
	}

	template<typename Semantics>
	inline double log_probability(const array_multiset<rule<Semantics>>& observations) const {
		double sum = 0.0;
		for (const auto& entry : observations.counts)
			sum += log_probability(entry.key) * entry.value;
		return sum;
	}

	inline void compute_max_nonterminal_probability() {
		double maximum = 0.0;
		for (unsigned int i = 0; i < nonterminal_prior.atom_count; i++)
			maximum = max(maximum, nonterminal_prior.probability(i + 1));
		max_nonterminal_probability = maximum;
		max_nonterminal_log_probability = log(maximum);
	}

	static inline bool copy(
			const rule_prior<NonterminalPrior, TerminalPrior>& src,
			rule_prior<NonterminalPrior, TerminalPrior>& dst)
	{
		if (!core::copy(src.nonterminal_prior, dst.nonterminal_prior)
		 || !core::copy(src.terminal_prior, dst.terminal_prior))
			return false;
		dst.compute_max_nonterminal_probability();
		return true;
	}

	static inline void free(rule_prior<NonterminalPrior, TerminalPrior>& prior) {
		core::free(prior.nonterminal_prior);
		core::free(prior.terminal_prior);
	}

private:
	template<typename Semantics>
	static inline bool get_nonterminals_helper(
		array_multiset<unsigned int>& nonterminals,
		const rule<Semantics>& observation,
		unsigned int count = 1)
	{
		for (unsigned int i = 0; i < observation.nt.length; i++)
			if (!nonterminals.add_unsorted(observation.nt.nonterminals[i], count))
				return false;
		return true;
	}

	template<typename Semantics>
	static bool get_nonterminals(
		array_multiset<unsigned int>& nonterminals,
		const rule<Semantics>& observation)
	{
		if (!get_nonterminals_helper(nonterminals, observation)) return false;
		if (nonterminals.counts.size > 1)
			insertion_sort(nonterminals.counts.keys, nonterminals.counts.values, (unsigned int) nonterminals.counts.size);
		return true;
	}

	template<typename Semantics>
	static bool get_nonterminals(
		array_multiset<unsigned int>& nonterminals,
		const array_multiset<rule<Semantics>>& observations)
	{
		for (auto entry : observations.counts) {
			if (!get_nonterminals_helper(nonterminals, entry.key, entry.value))
				return false;
		}
		if (nonterminals.counts.size > 1)
			insertion_sort(nonterminals.counts.keys, nonterminals.counts.values, (unsigned int) nonterminals.counts.size);
		return true;
	}
};

template<typename NonterminalPrior, typename TerminalPrior>
inline bool init(
	rule_prior<NonterminalPrior, TerminalPrior>& pi,
	const rule_prior<NonterminalPrior, TerminalPrior>& src)
{
	if (!init(pi.nonterminal_prior, src.nonterminal_prior)) return false;
	if (!init(pi.terminal_prior, src.terminal_prior)) {
		free(pi.nonterminal_prior);
		return false;
	}
	pi.compute_max_nonterminal_probability();
	return true;
}

template<typename NonterminalPrior, typename TerminalPrior, typename Stream>
inline bool read(rule_prior<NonterminalPrior, TerminalPrior>& prior, Stream& stream)
{
	if (!read(prior.nonterminal_prior, stream) || !read(prior.terminal_prior, stream))
		return false;
	prior.compute_max_nonterminal_probability();
	return true;
}

template<typename NonterminalPrior, typename TerminalPrior, typename Stream>
inline bool write(const rule_prior<NonterminalPrior, TerminalPrior>& prior, const Stream& stream)
{
	return write(prior.nonterminal_prior, stream)
		&& write(prior.terminal_prior, stream);
}

template<typename NonterminalPrior, typename TerminalPrior, typename Semantics>
bool sample(const rule_prior<NonterminalPrior, TerminalPrior>& prior, rule<Semantics>& output, bool is_preterminal)
{
	typedef typename Semantics::function function;

	if (is_preterminal) {
		sequence& tokens = *((sequence*) alloca(sizeof(sequence)));
		if (!sample(prior.terminal_prior, tokens))
			return false;
		output.nonterminals = tokens.tokens;
		output.functions = (function*) malloc(sizeof(function));
		output.length = tokens.length;
		if (output.functions == NULL) {
			fprintf(stderr, "sample ERROR: Insufficient memory for terminal production rule.\n");
			free(output.nonterminals);
			return false;
		}
		output.functions[0] = Semantics::terminal_function();
	} else {
		core::pair<function, function> sampled_transformations =
				sample_uniform(Semantics::transformations);

		if (!init(output, 2)) return false;
		output.functions[0] = sampled_transformations.key;
		output.functions[1] = sampled_transformations.value;
		if (!sample(prior.nonterminal_prior, output.nonterminals[0])
		 || !sample(prior.nonterminal_prior, output.nonterminals[1]))
		{
			free(output);
			return false;
		}
	}
	return true;
}

template<typename TerminalPrior>
struct terminal_prior
{
	typedef double value_type;

	TerminalPrior prior;
	hash_set<sequence> excluded;
	part_of_speech pos;

	terminal_prior(const TerminalPrior& prior, part_of_speech pos) : prior(prior), excluded(16), pos(pos) { }

	terminal_prior(const terminal_prior<TerminalPrior>& src) :
		prior(src.prior), excluded(src.excluded.capacity), pos(src.pos)
	{
		if (!excluded.add_all(src.excluded)) exit(EXIT_FAILURE);
	}

	inline part_of_speech get_part_of_speech() const {
		return pos;
	}

	template<typename Semantics>
	double probability(const rule<Semantics>& observation) const {
		sequence seq(observation.t.terminals, observation.t.length);
		if (excluded.contains(seq)) return 0.0;
		else return prior.probability(seq);
	}

	template<typename Semantics>
	inline double probability(const array_multiset<rule<Semantics>>& observations) const {
		double product = 1.0;
		for (const auto& entry : observations.counts)
			product *= pow(probability(entry.key), entry.value);
		return product;
	}

	template<typename Semantics>
	double log_probability(const rule<Semantics>& observation) const {
		sequence seq(observation.t.terminals, observation.t.length);
		if (excluded.contains(seq)) return -std::numeric_limits<double>::infinity();
		else return prior.log_probability(seq);
	}

	template<typename Semantics>
	inline double log_probability(const array_multiset<rule<Semantics>>& observations) const {
		double sum = 0.0;
		for (const auto& entry : observations.counts)
			sum += log_probability(entry.key) * entry.value;
		return sum;
	}

	static inline bool copy(
			const terminal_prior<TerminalPrior>& src,
			terminal_prior<TerminalPrior>& dst)
	{
		return core::copy(src.prior, dst.prior)
			&& core::copy(src.excluded, dst.excluded)
			&& core::copy(src.pos, dst.pos);
	}

	static inline void free(terminal_prior<TerminalPrior>& prior) {
		core::free(prior.prior);
		for (sequence& entry : prior.excluded)
			core::free(entry);
		core::free(prior.excluded);
	}
};

template<typename RulePrior>
inline bool init(
		terminal_prior<RulePrior>& pi,
	const terminal_prior<RulePrior>& src)
{
	pi.pos = src.pos;
	if (!init(pi.prior, src.prior)) return false;
	if (!hash_set_init(pi.excluded, src.excluded.capacity)) {
		free(pi.prior); return false;
	} else if (!pi.excluded.add_all(src.excluded)) {
		free(pi.excluded); free(pi.prior);
		return false;
	}
	return true;
}

template<typename RulePrior, typename Stream>
inline bool read(terminal_prior<RulePrior>& prior, Stream& stream)
{
	if (!read(prior.pos, stream)
	 || !read(prior.prior, stream)) return false;
	if (!read(prior.excluded, stream)) {
		free(prior.prior); return false;
	}
	return true;
}

template<typename RulePrior, typename Stream>
inline bool write(const terminal_prior<RulePrior>& prior, const Stream& stream)
{
	return write(prior.pos, stream) && write(prior.prior, stream) && write(prior.excluded, stream);
}

template<typename TerminalPrior, typename Semantics>
bool sample(const terminal_prior<TerminalPrior>& prior, rule<Semantics>& output)
{
	sequence& tokens = *((sequence*) alloca(sizeof(sequence)));
	while (true) {
		if (!sample(prior.prior, tokens))
			return false;
		if (!prior.excluded.contains(tokens)) break;
		free(tokens);
	}
	output.type = rule_type::TERMINAL;
	output.t.terminals = tokens.tokens;
	output.t.length = tokens.length;
	output.t.inflected = nullptr;
	output.t.inflected_length = 0;
	return true;
}

template<typename RulePrior, typename Semantics>
struct rule_list_prior
{
	typedef double value_type;

	RulePrior backoff_prior;
	hash_map<rule<Semantics>, pair<double, double>> rules;

	rule_list_prior(const RulePrior& backoff_prior) : backoff_prior(backoff_prior), rules(4) { }

	rule_list_prior(const rule_list_prior<RulePrior, Semantics>& src) :
		backoff_prior(src.backoff_prior), rules(src.rules.table.capacity)
	{
		if (!initialize(src.rules)) exit(EXIT_FAILURE);
	}

	~rule_list_prior() {
		free();
	}

	inline part_of_speech get_part_of_speech() const {
		return backoff_prior.get_part_of_speech();
	}

	double probability(const rule<Semantics>& observation) const {
		if (rules.table.size == 0) {
			return backoff_prior.probability(observation);
		} else {
			bool contains;
			pair<double, double>& entry = rules.get(observation, contains);
			if (contains)
				return entry.key;
			else return 0.0;
		}
	}

	inline double probability(const array_multiset<rule<Semantics>>& observations) const {
		double product = 1.0;
		for (const auto& entry : observations.counts)
			product *= pow(probability(entry.key), entry.value);
		return product;
	}

	inline double log_probability(const rule<Semantics>& observation) const {
		if (rules.table.size == 0) {
			return backoff_prior.log_probability(observation);
		} else {
			bool contains;
			pair<double, double>& entry = rules.get(observation, contains);
			if (contains)
				return entry.value;
			else return -std::numeric_limits<double>::infinity();
		}
	}

	inline double log_probability(const array_multiset<rule<Semantics>>& observations) const {
		double sum = 0.0;
		for (const auto& entry : observations.counts)
			sum += log_probability(entry.key) * entry.value;
		return sum;
	}

	bool finish() {
		double total = 0.0;
		unsigned int uniform_rules = 0;
		for (const auto& entry : rules) {
			if (entry.value.key == 0.0) uniform_rules++;
			else total += entry.value.key;
		}

		if (total > 1.0) {
			fprintf(stderr, "rule_list_prior.finish WARNING: Total probability is greater than 1.\n");
			return false;
		}
		double uniform_probability = (1.0 - total) / uniform_rules;
		double log_uniform_probability = log(uniform_probability);
		for (pair<rule<Semantics>&, pair<double, double>&> entry : rules) {
			if (entry.value.key == 0.0) {
				entry.value.key = uniform_probability;
				entry.value.value = log_uniform_probability;
			} else {
				entry.value.value = log(entry.value.key);
			}
		}
		return true;
	}

	static inline bool copy(const rule_list_prior<RulePrior, Semantics>& src, rule_list_prior<RulePrior, Semantics>& dst) {
		return init(dst, src);
	}

	static inline void free(rule_list_prior<RulePrior, Semantics>& prior) {
		prior.free();
		core::free(prior.backoff_prior);
		core::free(prior.rules);
	}

private:
	inline bool initialize(const hash_map<rule<Semantics>, pair<double, double>>& src) {
		return rules.put_all(src);
	}

	inline void free() {
		for (auto entry : rules)
			core::free(entry.key);
	}

	template<typename A, typename B>
	friend bool init(rule_list_prior<A, B>&, const rule_list_prior<A, B>&);
};

template<typename RulePrior, typename Semantics>
inline bool init(rule_list_prior<RulePrior, Semantics>& prior,
		const rule_list_prior<RulePrior, Semantics>& src)
{
	if (!init(prior.backoff_prior, src.backoff_prior)) return false;
	if (!hash_map_init(prior.rules, src.rules.table.capacity)) {
		free(prior.backoff_prior);
		return false;
	} else if (!prior.initialize(src.rules)) {
		free(prior.backoff_prior);
		free(prior.rules);
		return false;
	}
	return true;
}

template<typename RulePrior, typename Semantics, typename Stream, typename RuleReader>
inline bool read(rule_list_prior<RulePrior, Semantics>& prior, Stream& stream, RuleReader& reader)
{
	if (!read(prior.backoff_prior, stream)) return false;
	if (!read(prior.rules, stream, reader)) {
		free(prior.backoff_prior);
		return false;
	}
	return true;
}

template<typename RulePrior, typename Semantics, typename Stream, typename RuleWriter>
inline bool write(const rule_list_prior<RulePrior, Semantics>& prior, Stream& stream, RuleWriter& writer)
{
	return write(prior.backoff_prior, stream) && write(prior.rules, stream, writer);
}

template<typename RulePrior, typename Semantics>
bool sample(const rule_list_prior<RulePrior, Semantics>& prior, rule<Semantics>& output)
{
	if (prior.rules.table.size == 0) {
		return sample(prior.backoff_prior, output);
	} else {
		unsigned int index = 0;
		double* probabilities = (double*) malloc(sizeof(double) * prior.rules.table.size);
		for (const auto& entry : prior.rules) {
			probabilities[index] = entry.value.key;
			index++;
		}

		index = 0;
		unsigned int selected = sample_categorical(probabilities, prior.rules.table.size);
		free(probabilities);
		for (const rule<Semantics>& r : prior.rules.table) {
			if (index == selected)
				return init(output, r);
			index++;
		}

		/* unreachable */
		return false;
	}
}

enum nonterminal_type {
	NONTERMINAL = 1,
	PRETERMINAL = 2,
	PRETERMINAL_NUMBER = 3,
	PRETERMINAL_STRING = 4
};

template<typename Stream>
inline bool read(nonterminal_type& type, Stream& in) {
	unsigned char c;
	if (!read(c, in)) return false;
	type = static_cast<nonterminal_type>(c);
	return true;
}

template<typename Stream>
inline bool write(const nonterminal_type& type, Stream& out) {
	return write((unsigned char) type, out);
}

template<typename Stream>
bool print(const nonterminal_type& type, Stream& out) {
	switch (type) {
	case NONTERMINAL: return print("nonterminal", out);
	case PRETERMINAL: return print("preterminal", out);
	case PRETERMINAL_NUMBER: return print("preterminal_number", out);
	case PRETERMINAL_STRING: return print("preterminal_string", out);
	default:
		fprintf(stderr, "print ERROR: Unrecognized nonterminal_type.\n");
		return false;
	}
}

template<typename RulePrior, typename Semantics>
struct hdp_rule_distribution
{
	struct cache_value {
		hash_map<feature_set, double*> probabilities;
		hash_map<rule<Semantics>, array<weighted_feature_set<double>>*> posterior;

		static inline void move(const cache_value& src, cache_value& dst) {
			core::move(src.probabilities, dst.probabilities);
			core::move(src.posterior, dst.posterior);
		}

		static inline void free(cache_value& value)
		{
			for (auto entry : value.probabilities) {
				core::free(entry.key);
				core::free(entry.value);
			}
			for (auto entry : value.posterior) {
				core::free(entry.key);
				if (entry.value != NULL) {
					for (auto& element : *entry.value)
						core::free(element);
					core::free(*entry.value);
					core::free(entry.value);
				}
			}
			core::free(value.probabilities);
			core::free(value.posterior);
		}
	};

	nonterminal_type type;
	typename Semantics::feature* feature_sequence;
	unsigned int feature_count;

	array_multiset<rule<Semantics>> observations;
	hdp<RulePrior, constant<rule<Semantics>>, rule<Semantics>, double> h;
	hdp_sampler<RulePrior, constant<rule<Semantics>>, rule<Semantics>, double> sampler;
	cache<RulePrior, constant<rule<Semantics>>, rule<Semantics>, double> hdp_cache;
	double* a; double* b;

	hash_map<feature_set, cache_value> likelihood_cache;
	array<unsigned int>* root_probabilities;

	inline bool has_terminal_rules() const {
		return type != NONTERMINAL;
	}

	inline bool has_nonterminal_rules() const {
		return type == NONTERMINAL;
	}

	inline bool is_string_preterminal() const {
		return type == PRETERMINAL_STRING;
	}

	inline part_of_speech get_part_of_speech() const {
		return h.pi.get_part_of_speech();
	}

	inline void on_resize() {
		sampler.n = &h;
	}

	void clear() {
		for (auto entry : likelihood_cache) {
			core::free(entry.key);
			core::free(entry.value);
		}
		likelihood_cache.clear();
		remove_empty_tables(sampler, hdp_cache);
		recompute_root_assignments(sampler);
		if (root_probabilities != NULL) {
			cleanup_root_probabilities(root_probabilities, (unsigned int) observations.counts.size);
			root_probabilities = NULL;
		}
	}

	static void free(hdp_rule_distribution<RulePrior, Semantics>& distribution)
	{
		if (distribution.feature_count > 0)
			core::free(distribution.feature_sequence);
		for (auto entry : distribution.likelihood_cache) {
			core::free(entry.key);
			core::free(entry.value);
		}
		if (distribution.root_probabilities != NULL) {
			cleanup_root_probabilities(distribution.root_probabilities, (unsigned int) distribution.observations.counts.size);
			distribution.root_probabilities = NULL;
		}
		core::free(distribution.likelihood_cache);
		core::free(distribution.observations);
		core::free(distribution.hdp_cache);
		core::free(distribution.sampler);
		core::free(distribution.h);
		core::free(distribution.a); core::free(distribution.b);
	}
};

template<typename RulePrior, typename Semantics>
bool init(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	nonterminal_type type, const RulePrior& rule_prior,
	const typename Semantics::feature* features,
	const double* a, const double* b, unsigned int feature_count)
{
	unsigned int depth = feature_count + 1;
	double* alpha = (double*) alloca(sizeof(double) * depth);
	if (alpha == NULL) return false;
	for (unsigned int i = 0; i < depth; i++)
		alpha[i] = a[i] / b[i];

	distribution.type = type;
	distribution.root_probabilities = NULL;
	distribution.feature_count = feature_count;
	if (feature_count > 0) {
		distribution.feature_sequence = (typename Semantics::feature*)
			malloc(sizeof(typename Semantics::feature) * feature_count);
		if (distribution.feature_sequence == NULL) {
			fprintf(stderr, "init ERROR: Insufficient memory for feature sequence in hdp_rule_distribution.\n");
			return false;
		}
		memcpy(distribution.feature_sequence, features, sizeof(typename Semantics::feature) * feature_count);
	}
	if (!init(distribution.observations, 16)) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		return false;
	} else if (!hash_map_init(distribution.likelihood_cache, 32)) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); return false;
	} else if (!init(distribution.h, rule_prior, alpha, depth)) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); free(distribution.likelihood_cache); return false;
	} else if (!init(distribution.sampler, distribution.h)) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); free(distribution.likelihood_cache);
		free(distribution.h); return false;
	} else if (!init(distribution.hdp_cache, distribution.sampler)) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); free(distribution.likelihood_cache);
		free(distribution.h); free(distribution.sampler); return false;
	}
	distribution.a = (double*) malloc(sizeof(double) * depth);
	if (distribution.a == NULL) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); free(distribution.likelihood_cache);
		free(distribution.h); free(distribution.sampler); free(distribution.hdp_cache);
		return false;
	}
	distribution.b = (double*) malloc(sizeof(double) * depth);
	if (distribution.b == NULL) {
		if (distribution.feature_count > 0) free(distribution.feature_sequence);
		free(distribution.observations); free(distribution.likelihood_cache);
		free(distribution.h); free(distribution.sampler); free(distribution.hdp_cache);
		free(distribution.a); return false;
	}
	memcpy(distribution.a, a, sizeof(double) * depth);
	memcpy(distribution.b, b, sizeof(double) * depth);
	return true;
}

/* NOTE: this constructor is not a copy; it initializes
   'distribution' with the same parameters as 'src' */
template<typename RulePrior, typename Semantics>
inline bool init(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const hdp_rule_distribution<RulePrior, Semantics>& src)
{
	return init(distribution, src.h.pi, src.feature_sequence, src.a, src.b, src.feature_count);
}

template<typename RulePrior, typename Semantics>
bool copy(
		const hdp_rule_distribution<RulePrior, Semantics>& src,
		hdp_rule_distribution<RulePrior, Semantics>& dst)
{
	dst.type = src.type;
	if (src.root_probabilities == NULL) {
		dst.root_probabilities = NULL;
	} else {
		dst.root_probabilities = copy_root_probabilities(src.sampler, src.root_probabilities, src.observations.counts.size);
		if (dst.root_probabilities == NULL) return false;
	}

	hash_map<const node<rule<Semantics>, double>*, node<rule<Semantics>, double>*> node_map(256);
	dst.feature_count = src.feature_count;
	if (dst.feature_count > 0) {
		dst.feature_sequence = (typename Semantics::feature*)
			malloc(sizeof(typename Semantics::feature) * src.feature_count);
		if (dst.feature_sequence == NULL) {
			fprintf(stderr, "copy ERROR: Insufficient memory for feature sequence in hdp_rule_distribution.\n");
			return false;
		}
		memcpy(dst.feature_sequence, src.feature_sequence, sizeof(typename Semantics::feature) * dst.feature_count);
	}
	if (!init(dst.observations, src.observations)) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		return false;
	} else if (!hash_map_init(dst.likelihood_cache, src.likelihood_cache.table.capacity)) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); return false;
	} else if (!copy(src.h, dst.h, node_map)) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); free(dst.likelihood_cache);
		return false;
	} else if (!copy(src.sampler, dst.sampler, dst.h, node_map)) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); free(dst.likelihood_cache);
		free(dst.h); return false;
	} else if (!init(dst.hdp_cache, src.sampler)) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); free(dst.likelihood_cache);
		free(dst.h); free(dst.sampler); return false;
	}
	dst.a = (double*) malloc(sizeof(double) * src.h.depth);
	if (dst.a == NULL) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); free(dst.likelihood_cache);
		free(dst.h); free(dst.sampler); free(dst.hdp_cache);
		return false;
	}
	dst.b = (double*) malloc(sizeof(double) * src.h.depth);
	if (dst.b == NULL) {
		if (dst.feature_count > 0) free(dst.feature_sequence);
		free(dst.observations); free(dst.likelihood_cache);
		free(dst.h); free(dst.sampler); free(dst.hdp_cache);
		free(dst.a); return false;
	}
	memcpy(dst.a, src.a, sizeof(double) * src.h.depth);
	memcpy(dst.b, src.b, sizeof(double) * src.h.depth);
	return true;
}

/* TODO: the priors should also be read from/written to file,
   as each nonterminal could have a different set of priors. */
template<typename RulePrior, typename Semantics, typename Stream, typename AtomReader>
bool read(hdp_rule_distribution<RulePrior, Semantics>& distribution, Stream& stream, AtomReader& atom_reader)
{
	distribution.root_probabilities = NULL;
	if (!read(distribution.type, stream)
	 || !read(distribution.feature_count, stream)
	 || !read(distribution.observations, stream, atom_reader)) {
		return false;
	} else if (!read(distribution.h, stream, atom_reader, atom_reader, atom_reader)) {
		free(distribution.observations);
		return false;
	} else if (!read(distribution.sampler, stream, distribution.h, atom_reader)) {
		free(distribution.observations);
		free(distribution.h);
		return false;
	} else if (!hash_map_init(distribution.likelihood_cache, 32)) {
		free(distribution.observations);
		free(distribution.sampler);
		free(distribution.h);
		return false;
	} else if (!init(distribution.hdp_cache, distribution.sampler)) {
		free(distribution.likelihood_cache);
		free(distribution.observations);
		free(distribution.sampler);
		free(distribution.h);
		return false;
	}
	distribution.a = NULL; distribution.b = NULL; distribution.feature_sequence = NULL;
	distribution.a = (double*) malloc(sizeof(double) * distribution.h.depth);
	distribution.b = (double*) malloc(sizeof(double) * distribution.h.depth);
	if (distribution.feature_count > 0) {
		distribution.feature_sequence = (typename Semantics::feature*)
			malloc(sizeof(typename Semantics::feature) * distribution.feature_count);
	}
	if (distribution.a == NULL || distribution.b == NULL
	 || (distribution.feature_count > 0 && distribution.feature_sequence == NULL)
	 || !read(distribution.a, stream, distribution.h.depth)
	 || !read(distribution.b, stream, distribution.h.depth)
	 || !Semantics::read(distribution.feature_sequence, stream, distribution.feature_count))
	{
		free(distribution.likelihood_cache); free(distribution.observations);
		free(distribution.sampler); free(distribution.h); free(distribution.hdp_cache);
		if (distribution.a != NULL) free(distribution.a);
		if (distribution.b != NULL) free(distribution.b);
		if (distribution.feature_sequence != NULL) free(distribution.feature_sequence);
		return false;
	}
	return true;
}

template<typename RulePrior, typename Semantics, typename Stream, typename AtomWriter>
bool write(const hdp_rule_distribution<RulePrior, Semantics>& distribution, Stream& stream, AtomWriter& atom_writer)
{
	return write(distribution.type, stream)
		&& write(distribution.feature_count, stream)
		&& write(distribution.observations, stream, atom_writer)
		&& write(distribution.h, stream, atom_writer, atom_writer, atom_writer)
		&& write(distribution.sampler, stream, atom_writer)
		&& write(distribution.a, stream, distribution.h.depth)
		&& write(distribution.b, stream, distribution.h.depth)
		&& Semantics::write(distribution.feature_sequence, stream, distribution.feature_count);
}

template<typename Semantics>
bool get_features(feature_set& set, const Semantics& logical_form,
	const typename Semantics::feature* features, unsigned int feature_count)
{
	for (unsigned int i = 0; i < feature_count; i++)
	{
		if (!get_feature(features[i], logical_form, set.features[i], set.excluded[i], set.excluded_counts[i]))
			return false;
#if !defined(NDEBUG)
		if (set.features[i] == UNION_NODE && set.excluded_counts[i] <= 1)
			fprintf(stderr, "get_features WARNING: `get_feature` returned UNION_NODE but `excluded_count` is not greater than 1.\n");
#endif
	}
	return true;
}

template<typename Semantics>
bool set_features(
	Semantics& logical_form,
	const weighted_feature_set<double>& posterior,
	const typename Semantics::feature* features,
	unsigned int feature_count)
{
	for (unsigned int i = 0; i < feature_count; i++) {
#if !defined(NDEBUG)
		if (posterior.features[i] == UNION_NODE)
			fprintf(stderr, "set_features WARNING: Feature with value `UNION_NODE` is unsupported.\n");
#endif
		if (posterior.features[i] == IMPLICIT_NODE) {
			if (!exclude_features(features[i], logical_form,
				posterior.features.excluded[i], posterior.features.excluded_counts[i]))
			{
				return false;
			}
		} else if (!set_feature(features[i], logical_form, posterior.features[i]))
			/* setting this feature resulted in an empty set of logical forms, so return quietly */
			return false;
	}
	logical_form.recompute_hash();
	return true;
}

template<typename RulePrior, typename Semantics>
using hdp_grammar = grammar<Semantics, hdp_rule_distribution<RulePrior, Semantics>>;

template<typename RulePrior, typename Semantics>
bool add(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& r, const Semantics& logical_form)
{
	feature_set set = feature_set(distribution.feature_count);
	if (r.is_terminal()) {
		rule<Semantics> terminal_rule(sequence(r.t.terminals, r.t.length));
		return get_features(set, logical_form, distribution.feature_sequence, distribution.feature_count)
			&& distribution.observations.add(terminal_rule)
			&& add(distribution.sampler, set.features, set.feature_count, terminal_rule, distribution.hdp_cache);
	} else {
		return get_features(set, logical_form, distribution.feature_sequence, distribution.feature_count)
			&& distribution.observations.add(r)
			&& add(distribution.sampler, set.features, set.feature_count, r, distribution.hdp_cache);
	}
}

template<typename RulePrior, typename Semantics>
bool remove(hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& r, const Semantics& logical_form)
{
	feature_set set = feature_set(distribution.feature_count);
	if (r.is_terminal()) {
		rule<Semantics> terminal_rule(sequence(r.t.terminals, r.t.length));
		return get_features(set, logical_form, distribution.feature_sequence, distribution.feature_count)
			&& distribution.observations.subtract(terminal_rule) < distribution.observations.counts.size
			&& remove(distribution.sampler, set.features, set.feature_count, terminal_rule, distribution.hdp_cache);
	} else {
		return get_features(set, logical_form, distribution.feature_sequence, distribution.feature_count)
			&& distribution.observations.subtract(r) < distribution.observations.counts.size
			&& remove(distribution.sampler, set.features, set.feature_count, r, distribution.hdp_cache);
	}
}

template<typename RulePrior, typename Semantics>
inline double log_probability(const hdp_rule_distribution<RulePrior, Semantics>& distribution)
{
	return log_probability(distribution.sampler)
		 + log_probability_each_level(distribution.sampler, distribution.a, distribution.b);
}

template<typename RulePrior, typename Semantics, typename StringMapType>
inline double log_probability(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& observation,
	const Semantics& logical_form,
	const StringMapType& token_map)
{
	unsigned int length;
	weighted<Semantics>* posterior;
	if (observation.is_terminal()) {
		rule<Semantics> terminal_rule(sequence(observation.t.terminals, observation.t.length));
		posterior = log_conditional<false, false>(distribution, terminal_rule, logical_form, token_map, length);
	} else {
		posterior = log_conditional<false, false>(distribution, observation, logical_form, token_map, length);
	}

	double weight;
	if (length == 0)
		weight = -std::numeric_limits<double>::infinity();
	else weight = posterior[0].log_probability;

	if (posterior != NULL) {
		for (unsigned int i = 0; i < length; i++)
			free(posterior[i]);
		free(posterior);
	}
	return weight;
}

template<typename RulePrior, typename Semantics>
inline void sample(hdp_rule_distribution<RulePrior, Semantics>& distribution)
{
	distribution.clear();
	sample_alpha_each_level(distribution.sampler, distribution.a, distribution.b);
	sample_hdp<true>(distribution.sampler, distribution.hdp_cache);
}

template<typename RulePrior, typename Semantics>
inline bool sample(
		const hdp_rule_distribution<RulePrior, Semantics>& distribution,
		rule<Semantics>& sampled_rule, const Semantics& logical_form)
{
	feature_set set = feature_set(distribution.feature_count);
	return get_features(set, logical_form, distribution.feature_sequence, distribution.feature_count)
		&& sample(distribution.sampler, sampled_rule, set.features, set.feature_count, distribution.hdp_cache);
}

template<typename TerminalPrior, typename Semantics>
inline bool add_rule(
		hdp_rule_distribution<rule_list_prior<TerminalPrior, Semantics>, Semantics>& distribution,
		const rule<Semantics>& new_rule, double prior)
{
	if (!distribution.h.pi.rules.check_size()) return false;

	bool contains; unsigned int bucket;
	distribution.h.pi.rules.get(new_rule, contains, bucket);
	if (contains) {
		print("add_rule ERROR: Duplicate rule.\n", stderr);
		return false;
	} else {
		distribution.h.pi.rules.table.keys[bucket] = new_rule;
		distribution.h.pi.rules.values[bucket] = make_pair(prior, 0.0);
		distribution.h.pi.rules.table.size++;
	}
	return true;
}

template<typename RulePrior, typename Semantics>
typename hdp_rule_distribution<RulePrior, Semantics>::cache_value&
get_cache_entry(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const feature_set& features)
{
	typedef typename hdp_rule_distribution<RulePrior, Semantics>::cache_value cache_value;

	if (!distribution.likelihood_cache.check_size())
		exit(EXIT_FAILURE);

	bool contains; unsigned int index;
	unsigned int observation_count = (unsigned int) distribution.observations.counts.size;
	cache_value& value = distribution.likelihood_cache.get(features, contains, index);
	if (!contains) {
		if (distribution.root_probabilities == NULL)
			distribution.root_probabilities = distribution.hdp_cache.compute_root_probabilities(
				distribution.sampler, distribution.observations.counts.keys, observation_count);

		if (!hash_map_init(value.probabilities, 32)) {
			exit(EXIT_FAILURE);
		} else if (!hash_map_init(value.posterior, 32)) {
			free(value.probabilities);
			exit(EXIT_FAILURE);
		}
		predict(distribution.sampler, features.features,
			features.excluded, features.excluded_counts, value.probabilities,
			distribution.observations.counts.keys, observation_count,
			distribution.root_probabilities);

		if (!init(distribution.likelihood_cache.table.keys[index], features)) {
			free(value.probabilities);
			free(value.posterior);
			exit(EXIT_FAILURE);
		}
		distribution.likelihood_cache.table.size++;
	}
	return value;
}

template<bool DiscardImpossible, bool PruneAmbiguousLogicalForms, typename RulePrior, typename Semantics>
const array<weighted_feature_set<double>>* log_conditional(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& observation, const Semantics& logical_form)
{
	typedef typename hdp_rule_distribution<RulePrior, Semantics>::cache_value cache_value;

	feature_set features = feature_set(distribution.feature_count);
	if (!get_features(features, logical_form, distribution.feature_sequence, distribution.feature_count))
		return NULL;
	cache_value& value = get_cache_entry(distribution, features);

	bool contains; unsigned int index;
	if (!value.posterior.check_size()) return NULL;
	array<weighted_feature_set<double>>*& posterior = value.posterior.get(observation, contains, index);
	if (contains) return posterior;

	posterior = (array<weighted_feature_set<double>>*) malloc(sizeof(array<weighted_feature_set<double>>));
	if (posterior == NULL) {
		fprintf(stderr, "log_conditional ERROR: Insufficient memory for array of weighted_feature_lists.\n");
		return NULL;
	} else if (!array_init(*posterior, value.probabilities.table.size)) {
		free(posterior);
		return NULL;
	}

	unsigned int observation_index = distribution.observations.counts.index_of(observation);
	for (const auto& entry : value.probabilities) {
		double log_probability = log(entry.value[observation_index]);
		if (entry.value[observation_index] == 0.0) {
			if (DiscardImpossible) continue;
			log_probability = -std::numeric_limits<double>::infinity();
		}

		if (observation_index == distribution.observations.counts.size) {
			/* this is an unobserved rule */
			log_probability += distribution.h.pi.log_probability(observation);
		}
		if (DiscardImpossible && log_probability == -std::numeric_limits<double>::infinity())
			continue;

		/* prune paths that don't contain the observation */
		unsigned int* path = (unsigned int*) alloca(sizeof(unsigned int) * entry.key.feature_count);
		for (unsigned int i = 0; PruneAmbiguousLogicalForms && i < distribution.feature_count; i++) {
			if (!Semantics::is_feature_pruneable(distribution.feature_sequence[i]))
				path[i] = IMPLICIT_NODE;
			else path[i] = entry.key.features[i];
		}
		if (PruneAmbiguousLogicalForms && value.probabilities.table.size > 1
		 && index_of(IMPLICIT_NODE, entry.key.features, entry.key.feature_count) == entry.key.feature_count
		 && !::contains(distribution.h, path, entry.key.feature_count, observation))
			continue;

		if (!init(posterior->data[posterior->length], entry.key, log_probability)) {
			fprintf(stderr, "log_conditional ERROR: Unable to initialize weighted_feature_list.\n");
			return NULL;
		}
		posterior->length++;
	}
	value.posterior.table.keys[index] = observation;
	value.posterior.values[index] = posterior;
	value.posterior.table.size++;
	insertion_sort(*posterior, default_sorter());
	return posterior;
}

inline const string& map_to_string(const string** map, unsigned int id) {
	return *map[id];
}

template<typename Parser>
inline const string& map_to_string(const Parser& parser, unsigned int id) {
	return parser.map_to_string(id);
}

const string& map_to_string(const hash_map<string, unsigned int>& map, unsigned int id) {
	fprintf(stderr, "map_to_string ERROR: This function can"
			" only be called with an integer-to-string map.\n");
	exit(EXIT_FAILURE);
}

constexpr bool parse_written_number(const string** map,
		unsigned int* terminals, const unsigned int length, int64_t& integer)
{
	return false;
}

bool parse_written_number(const hash_map<string, unsigned int>& map,
		unsigned int* terminals, const unsigned int length, int64_t& integer)
{
	fprintf(stderr, "parse_written_number ERROR: This function can"
			" only be called with an integer-to-string map.\n");
	exit(EXIT_FAILURE);
}

bool get_token(const string& identifier, unsigned int& id, const string** map) {
	fprintf(stderr, "get_token ERROR: This function can"
			" only be called with a string-to-integer map.\n");
	exit(EXIT_FAILURE);
}

inline bool get_token(const string& identifier, unsigned int& id, const hash_map<string, unsigned int>& parser) {
	bool contains;
	id = parser.get(identifier, contains);
	return contains;
}

template<typename Parser>
bool get_token(const string& identifier, unsigned int& id, const Parser& parser) {
	fprintf(stderr, "get_token ERROR: This function can"
			" only be called with a string-to-integer map.\n");
	exit(EXIT_FAILURE);
}

template<typename Semantics, typename StringMapType>
inline bool parse_number(const rule<Semantics>& observation,
		const Semantics& src_logical_form, Semantics& dst_logical_form,
		const StringMapType& token_map)
{
	if (!observation.is_terminal())
		return false;

	array<char> integer_str(16);
	unsigned long long decimal = 0;
	bool could_be_numerical = true;
	for (unsigned int i = 0; i < observation.t.length; i++) {
		const string& token = map_to_string(token_map, observation.t.terminals[i]);
		if (!integer_str.append(token.data, token.length))
			return false;

		i++;
		if (i == observation.t.length)
			break;

		const string& next = map_to_string(token_map, observation.t.terminals[i]);
		if (next == ",") {
			if (!integer_str.append(token.data, token.length)) return false;
		} else if (next == ".") {
			i++;
			if (i + 1 != observation.t.length
			 || !parse_ulonglong(map_to_string(token_map, observation.t.terminals[i]), decimal))
			{
				could_be_numerical = false;
			}
			break;
		} else {
			could_be_numerical = false;
			break;
		}
	}

	int64_t integer;
	if (could_be_numerical && parse_long(integer_str, integer)) {
		return set_number(dst_logical_form, src_logical_form, integer, decimal);
	} else if (parse_written_number(token_map, observation.t.terminals, observation.t.length, integer)) {
		return set_number(dst_logical_form, src_logical_form, integer, 0);
	} else {
		return false;
	}
}

template<typename Semantics, typename StringMapType>
inline bool parse_string(const rule<Semantics>& observation,
		const Semantics& src_logical_form, Semantics& dst_logical_form,
		const StringMapType& token_map)
{
	if (!observation.is_terminal())
		return false;

	array<char> new_string(64);
	for (unsigned int i = 0; i < observation.t.length; i++) {
		const string& token = map_to_string(token_map, observation.t.terminals[i]);
		if (!new_string.ensure_capacity(new_string.length + token.length + 1))
			return false;
		if (i != 0) new_string[new_string.length++] = ' ';
		for (unsigned int j = 0; j < token.length; j++)
			new_string[new_string.length++] = token[j];
	}

	string& concatenated = *((string*) alloca(sizeof(string)));
	concatenated.data = new_string.data;
	concatenated.length = new_string.length;
	return set_string(dst_logical_form, src_logical_form, concatenated);
}

template<typename Semantics, typename StringMapType>
inline bool get_string(const Semantics& src_logical_form,
		sequence& dst, const StringMapType& token_map)
{
	string& str = *((string*) alloca(sizeof(string)));
	if (!get_string(src_logical_form, str))
		return false;

	unsigned int new_token;
	array<unsigned int>& tokens = *((array<unsigned int>*) alloca(sizeof(array<unsigned int>)));
	if (!array_init(tokens, 8)) {
		free(str);
		return false;
	}
	unsigned int token_start = 0;
	for (unsigned int i = 0; i < str.length; i++) {
		if (str[i] == ' ') {
			if (token_start != i
			 && (!get_token(string(str.data + token_start, i - token_start), new_token, token_map) || !tokens.add(new_token)))
			{
				free(str); free(tokens);
				return false;
			}
			token_start = i + 1;
		}
	}

	if (token_start != str.length
	 && (!get_token(string(str.data + token_start, str.length - token_start), new_token, token_map) || !tokens.add(new_token)))
	{
		free(str); free(tokens);
		return false;
	}
	free(str);

	dst.tokens = tokens.data;
	dst.length = tokens.length;
	return true;
}

template<bool DiscardImpossible, bool PruneAmbiguousLogicalForms,
		typename RulePrior, typename Semantics, typename StringMapType>
inline weighted<Semantics>* log_conditional(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& observation, const Semantics& logical_form,
	const StringMapType& token_map, unsigned int& length)
{
	length = 0;
	if (distribution.type == PRETERMINAL_NUMBER) {
		weighted<Semantics>* weighted_logical_forms =
				(weighted<Semantics>*) malloc(sizeof(weighted<Semantics>) * 1);

		if (!parse_number(observation, logical_form, weighted_logical_forms[0].object, token_map))
			return weighted_logical_forms;
		weighted_logical_forms[0].log_probability = 0.0;
		length++; return weighted_logical_forms;
	} else if (distribution.type == PRETERMINAL_STRING) {
		weighted<Semantics>* weighted_logical_forms =
				(weighted<Semantics>*) malloc(sizeof(weighted<Semantics>) * 1);

		if (!parse_string(observation, logical_form, weighted_logical_forms[0].object, token_map))
			return weighted_logical_forms;
		weighted_logical_forms[0].log_probability = 0.0;
		length++; return weighted_logical_forms;
	}

	const array<weighted_feature_set<double>>* posterior =
			log_conditional<DiscardImpossible, PruneAmbiguousLogicalForms>(distribution, observation, logical_form);
	if (posterior == NULL) return NULL;

	weighted<Semantics>* weighted_logical_forms =
			(weighted<Semantics>*) malloc(sizeof(weighted<Semantics>) * max((size_t) 1, posterior->length));
	if (weighted_logical_forms == NULL) {
		fprintf(stderr, "log_conditional ERROR: Unable to initialize weighted logical form array.\n");
		return NULL;
	}
	for (unsigned int i = 0; i < posterior->length; i++)
	{
		weighted<Semantics>& item = weighted_logical_forms[length];
		item.object = logical_form;
		if (!set_features(item.object, posterior->data[i],
				distribution.feature_sequence, distribution.feature_count))
		{
			/* this logical form is impossible, so skip it */
			core::free(item.object);
			continue;
		}
		item.log_probability = posterior->data[i].log_probability;
		length++;
	}
	return weighted_logical_forms;
}

template<bool PruneUnobservedTerminals, typename RulePrior, typename Semantics, typename StringMapType>
inline weighted<sequence>* get_terminals(
	hdp_rule_distribution<RulePrior, Semantics>& distribution, const Semantics& logical_form,
	StringMapType& token_map, unsigned int& length)
{
	length = 0;
	if (distribution.type == PRETERMINAL_NUMBER) {
		weighted<sequence>* weighted_terminals =
				(weighted<sequence>*) malloc(sizeof(weighted<sequence>) * 1);
		if (weighted_terminals == NULL) {
			fprintf(stderr, "get_terminals ERROR: Out of memory.\n");
			return NULL;
		}

		int64_t integer; uint64_t decimal;
		if (any_number(logical_form)) {
			if (!PruneUnobservedTerminals) {
				weighted_terminals[0].log_probability = 0.0;
				if (!init(weighted_terminals[0].object, 1))
					weighted_terminals[0].object[0] = NEW_TERMINAL;
				length++;
			}
			return weighted_terminals;
		} else if (!get_number(logical_form, integer, decimal)) {
			return weighted_terminals;
		}

		weighted_terminals[0].log_probability = 0.0;
		if (!init(weighted_terminals[0].object, 1)) {
			free(weighted_terminals);
			return NULL;
		}

		int string_length;
		if (decimal == 0)
			string_length = snprintf(NULL, 0, "%" PRId64, integer);
		else string_length = snprintf(NULL, 0, "%" PRId64 ".%" PRIu64, integer, decimal);
		string buffer = string(string_length + 1);
		buffer.length = string_length;
		if ((decimal == 0 && snprintf(buffer.data, string_length + 1, "%" PRId64, integer) != string_length)
		 || (decimal != 0 && snprintf(buffer.data, string_length + 1, "%" PRId64 ".%" PRIu64, integer, decimal) != string_length)
		 || !get_token(buffer, weighted_terminals[0].object[0], token_map))
		{
			free(weighted_terminals[0]);
			free(weighted_terminals);
			return NULL;
		}

		length++; return weighted_terminals;
	} else if (distribution.type == PRETERMINAL_STRING) {
		weighted<sequence>* weighted_terminals =
				(weighted<sequence>*) malloc(sizeof(weighted<sequence>) * 1);
		if (weighted_terminals == NULL) {
			fprintf(stderr, "get_terminals ERROR: Out of memory.\n");
			return NULL;
		}

		if (any_string(logical_form)) {
			if (!PruneUnobservedTerminals) {
				weighted_terminals[0].log_probability = 0.0;
				if (!init(weighted_terminals[0].object, 1))
					weighted_terminals[0].object[0] = NEW_TERMINAL;
				length++;
			}
			return weighted_terminals;
		} else if (!get_string(logical_form, weighted_terminals[0].object, token_map)) {
			return weighted_terminals;
		}

		weighted_terminals[0].log_probability = 0.0;
		length++; return weighted_terminals;
	}

	typedef typename hdp_rule_distribution<RulePrior, Semantics>::cache_value cache_value;

	feature_set features = feature_set(distribution.feature_count);
	if (!get_features(features, logical_form, distribution.feature_sequence, distribution.feature_count))
		return NULL;
	cache_value& value = get_cache_entry(distribution, features);

	weighted<sequence>* weighted_terminals = (weighted<sequence>*)
			malloc(sizeof(weighted<sequence>) * (distribution.observations.counts.size + 1));
	if (weighted_terminals == NULL) {
		fprintf(stderr, "get_terminals ERROR: Out of memory.\n");
		return NULL;
	} else if (value.probabilities.table.size == 0) {
		return weighted_terminals;
	}

	for (unsigned int i = 0; i < distribution.observations.counts.size; i++) {
		const rule<Semantics>& observation = distribution.observations.counts.keys[i];
		if (!observation.is_terminal()) continue;
		if (!init(weighted_terminals[length].object, {observation.t.terminals, observation.t.length})) {
			for (unsigned int j = 0; j < length; j++)
				free(weighted_terminals[j]);
			free(weighted_terminals);
			return NULL;
		}
		weighted_terminals[length].log_probability = 0.0;
		length++;
	}

	for (const auto& entry : value.probabilities) {
		unsigned int index = 0;
		for (unsigned int i = 0; i < distribution.observations.counts.size; i++) {
			const rule<Semantics>& observation = distribution.observations.counts.keys[i];
			if (!observation.is_terminal()) continue;
			weighted_terminals[index].log_probability =
					max(weighted_terminals[index].log_probability, entry.value[i]);
			index++;
		}
	}

	for (unsigned int i = 0; i < length; i++)
		weighted_terminals[i].log_probability = log(weighted_terminals[i].log_probability);
	return weighted_terminals;
}

template<typename RulePrior, typename Semantics>
inline bool add_unobserved_rule(
	const hdp_rule_distribution<RulePrior, Semantics>& distribution,
	array<rule<Semantics>>& rules, const rule<Semantics>& new_rule)
{
	if (distribution.observations.counts.contains(new_rule))
		return true;

	if (!rules.ensure_capacity(rules.length + 1)
	 || !init(rules[(unsigned int) rules.length], new_rule))
		return false;
	rules.length++;
	return true;
}

template<typename RulePrior, typename Semantics>
bool add_unobserved_rule(
	const hdp_rule_distribution<RulePrior, Semantics>& distribution,
	array<rule<Semantics>>& rules, const rule<Semantics>& new_rule,
	const typename Semantics::function& first, const typename Semantics::function& second)
{
#if !defined(NDEBUG)
	if (new_rule.nt.length != 2)
		fprintf(stderr, "add_unobserved_rule WARNING: `new_rule` doesn't have length 2.\n");
	if (new_rule.nt.transformations[0].function_count != 1
	 || new_rule.nt.transformations[1].function_count != 1)
		fprintf(stderr, "add_unobserved_rule WARNING: A transformation in `new_rule` doesn't have 1 function.\n");
#endif
	new_rule.nt.transformations[0].functions[0] = first;
	new_rule.nt.transformations[1].functions[0] = second;
	return add_unobserved_rule(distribution, rules, new_rule);
}

template<typename NonterminalPrior, typename TerminalPrior, typename Semantics>
bool get_rules(
	hdp_rule_distribution<rule_prior<NonterminalPrior, TerminalPrior>, Semantics>& distribution,
	const Semantics& logical_form, array<rule<Semantics>>& rules, double min_probability)
{
	typedef typename Semantics::function function;
	typedef typename hdp_rule_distribution<rule_prior<NonterminalPrior, TerminalPrior>, Semantics>::cache_value cache_value;

	feature_set features = feature_set(distribution.feature_count);
	if (!get_features(features, logical_form, distribution.feature_sequence, distribution.feature_count))
		return true; /* the logical form cannot be expanded here, so return quietly */
	cache_value& value = get_cache_entry(distribution, features);

	/* get maximum likelihoods across all paths */
	unsigned int observation_count = (unsigned int) distribution.observations.counts.size;
	double* max_likelihoods = (double*) calloc(observation_count + 1, sizeof(double));
	if (max_likelihoods == NULL) {
		fprintf(stderr, "get_rules ERROR: Out of memory.\n");
		return false;
	}
	for (const auto& entry : value.probabilities) {
		for (unsigned int i = 0; i < observation_count + 1; i++) {
			if (entry.value[i] > max_likelihoods[i])
				max_likelihoods[i] = entry.value[i];
		}
	}

	/* first consider all observed rules */
	for (unsigned int i = 0; i < observation_count; i++) {
		if (max_likelihoods[i] + 1.0e-9 > min_probability) {
			if (!rules.ensure_capacity(rules.length + 1)
			 || !init(rules[(unsigned int) rules.length], distribution.observations.counts.keys[i])) {
				free(max_likelihoods);
				fprintf(stderr, "get_rules ERROR: Unable to add observed rule.\n");
				return false;
			}
			rules.length++;
		}
	}

	/* next, consider unobserved rules */
	if (max_likelihoods[observation_count] + 1.0e-9 > min_probability) {
		auto iterator = nonterminal_pair_iterator(distribution.h.pi.nonterminal_prior);
		while (iterator.has_next()) {
			nonterminal_pair pair = iterator.next();
			pair.prior_probability *= max_likelihoods[observation_count] / array_length(Semantics::transformations);
			if (pair.prior_probability + 1.0e-9 <= min_probability)
				break;

			rule<Semantics>& new_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
			new_rule.type = rule_type::NONTERMINAL;
			new_rule.nt.length = 2;
			new_rule.nt.transformations = (transformation<Semantics>*) malloc(sizeof(transformation<Semantics>) * new_rule.nt.length);
			new_rule.nt.nonterminals = (unsigned int*) malloc(sizeof(unsigned int) * new_rule.nt.length);
			new_rule.nt.transformations[0].function_count = 1;
			new_rule.nt.transformations[0].functions = (function*) malloc(sizeof(function) * new_rule.nt.transformations[0].function_count);
			new_rule.nt.transformations[1].function_count = 1;
			new_rule.nt.transformations[1].functions = (function*) malloc(sizeof(function) * new_rule.nt.transformations[1].function_count);
			new_rule.nt.nonterminals[0] = pair.first;
			new_rule.nt.nonterminals[1] = pair.second;

			for (unsigned int i = 0; i < array_length(Semantics::transformations); i++) {
				const core::pair<function, function>& transformation = Semantics::transformations[i];
				if (!add_unobserved_rule(distribution, rules, new_rule, transformation.key, transformation.value))
				{
					free(max_likelihoods);
					fprintf(stderr, "get_rules ERROR: Unable to add unobserved rule.\n");
					return false;
				}
			}

			free(new_rule);
		}
	}
	free(max_likelihoods);
	return true;
}

template<typename NonterminalPrior, typename TerminalPrior, typename Semantics>
bool get_rules(hdp_rule_distribution<rule_prior<NonterminalPrior, TerminalPrior>, Semantics>& distribution, array<rule<Semantics>>& rules)
{
	typedef typename Semantics::function function;

	/* for now, just retrieve all rules */
	const NonterminalPrior& nonterminal_prior = distribution.h.pi.nonterminal_prior;
	auto iterator = nonterminal_pair_iterator(nonterminal_prior);
	while (iterator.has_next()) {
		nonterminal_pair pair = iterator.next();
		rule<Semantics>& new_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
		new_rule.type = rule_type::NONTERMINAL;
		new_rule.nt.length = 2;
		new_rule.nt.transformations = (transformation<Semantics>*) malloc(sizeof(transformation<Semantics>) * new_rule.nt.length);
		new_rule.nt.nonterminals = (unsigned int*) malloc(sizeof(unsigned int) * new_rule.nt.length);
		new_rule.nt.transformations[0].function_count = 1;
		new_rule.nt.transformations[0].functions = (function*) malloc(sizeof(function) * new_rule.nt.transformations[0].function_count);
		new_rule.nt.transformations[1].function_count = 1;
		new_rule.nt.transformations[1].functions = (function*) malloc(sizeof(function) * new_rule.nt.transformations[1].function_count);
		new_rule.nt.nonterminals[0] = pair.first;
		new_rule.nt.nonterminals[1] = pair.second;

		for (unsigned int i = 0; i < array_length(Semantics::transformations); i++) {
			const core::pair<function, function>& transformation = Semantics::transformations[i];
			new_rule.nt.transformations[0].functions[0] = transformation.key;
			new_rule.nt.transformations[1].functions[0] = transformation.value;

			if (!rules.ensure_capacity(rules.length + 1)
			 || !init(rules[(unsigned int) rules.length], new_rule))
			{
				fprintf(stderr, "get_rules ERROR: Unable to add unobserved rule.\n");
				return false;
			}
			rules.length++;
		}
		free(new_rule);
	}
	return true;
}

template<typename NonterminalPrior, typename TerminalPrior, typename Semantics>
bool get_rules(
	hdp_rule_distribution<rule_list_prior<NonterminalPrior, TerminalPrior>, Semantics>& distribution,
	const Semantics& logical_form, array<rule<Semantics>>& rules, double min_probability)
{
	typedef typename hdp_rule_distribution<rule_list_prior<NonterminalPrior, TerminalPrior>, Semantics>::cache_value cache_value;

	feature_set features = feature_set(distribution.feature_count);
	if (!get_features(features, logical_form, distribution.feature_sequence, distribution.feature_count))
		return true; /* the logical form cannot be expanded here, so return quietly */
	cache_value& value = get_cache_entry(distribution, features);

	/* get maximum likelihoods across all paths */
	unsigned int observation_count = (unsigned int) distribution.observations.counts.size;
	double* max_likelihoods = (double*) calloc(observation_count + 1, sizeof(double));
	if (max_likelihoods == NULL) {
		fprintf(stderr, "get_rules ERROR: Out of memory.\n");
		return false;
	}
	for (const auto& entry : value.probabilities) {
		for (unsigned int i = 0; i < observation_count + 1; i++) {
			if (entry.value[i] > max_likelihoods[i])
				max_likelihoods[i] = entry.value[i];
		}
	}

	/* first consider all observed rules */
	for (unsigned int i = 0; i < observation_count; i++) {
		if (max_likelihoods[i] + 1.0e-9 > min_probability) {
			if (!rules.ensure_capacity(rules.length + 1)
			 || !init(rules[(unsigned int) rules.length], distribution.observations.counts.keys[i])) {
				free(max_likelihoods);
				fprintf(stderr, "get_rules ERROR: Unable to add observed rule.\n");
				return false;
			}
			rules.length++;
		}
	}

	/* next, consider unobserved rules */
	if (max_likelihoods[observation_count] + 1.0e-9 > min_probability) {
		for (const auto& entry : distribution.h.pi.rules) {
			const rule<Semantics>& new_rule = entry.key;
			if (!add_unobserved_rule(distribution, rules, new_rule)) {
				free(max_likelihoods);
				fprintf(stderr, "get_rules ERROR: Unable to add unobserved rule.\n");
				return false;
			}
		}
	}
	free(max_likelihoods);
	return true;
}

template<typename NonterminalPrior, typename TerminalPrior, typename Semantics>
bool get_rules(hdp_rule_distribution<rule_list_prior<NonterminalPrior, TerminalPrior>, Semantics>& distribution, array<rule<Semantics>>& rules)
{
	/* for now, just retrieve all rules */
	for (const auto& entry : distribution.h.pi.rules) {
		const rule<Semantics>& new_rule = entry.key;
		if (!rules.ensure_capacity(rules.length + 1)
		 || !init(rules[(unsigned int) rules.length], new_rule))
		{
			fprintf(stderr, "get_rules ERROR: Unable to add unobserved rule.\n");
			return false;
		}
		rules.length++;
	}
	return true;
}


template<typename RulePrior, typename Semantics, typename StringMapType>
double max_log_conditional(
	hdp_rule_distribution<RulePrior, Semantics>& distribution,
	const rule<Semantics>& observation, const Semantics& logical_form,
	const StringMapType& token_map)
{
	typedef typename hdp_rule_distribution<RulePrior, Semantics>::cache_value cache_value;

	if (distribution.type == PRETERMINAL_NUMBER) {
		Semantics& dst_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
		if (!parse_number(observation, logical_form, dst_logical_form, token_map))
			return -std::numeric_limits<double>::infinity();
		free(dst_logical_form); return 0.0;
	} else if (distribution.type == PRETERMINAL_STRING) {
		Semantics& dst_logical_form = *((Semantics*) alloca(sizeof(Semantics)));
		if (!parse_string(observation, logical_form, dst_logical_form, token_map))
			return -std::numeric_limits<double>::infinity();
		free(dst_logical_form); return 0.0;
	}

	double prior = 0.0;
	unsigned int index = distribution.observations.counts.index_of(observation);
	bool is_unobserved = (index == distribution.observations.counts.size);
	if (is_unobserved) {
		prior = distribution.h.pi.log_probability(observation);
		if (prior == -std::numeric_limits<double>::infinity()) return prior;
	}

	feature_set features = feature_set(distribution.feature_count);
	if (!get_features(features, logical_form, distribution.feature_sequence, distribution.feature_count))
		return -std::numeric_limits<double>::infinity();
	const cache_value& value = get_cache_entry(distribution, features);

	/* get maximum likelihoods across all paths */
	double maximum = -std::numeric_limits<double>::infinity();
	for (const auto& entry : value.probabilities) {
		if (entry.value[index] > maximum)
			maximum = entry.value[index];
	}

	maximum = log(maximum);
	if (is_unobserved) maximum += prior;
	return maximum;
}

bool is_subset(
		unsigned int first_feature, const unsigned int* first_excluded, unsigned int first_excluded_count,
		unsigned int second_feature, const unsigned int* second_excluded, unsigned int second_excluded_count)
{
	if (first_feature == IMPLICIT_NODE) {
		if (second_feature == IMPLICIT_NODE)
			return is_subset(second_excluded, second_excluded_count, first_excluded, first_excluded_count);
		else return false;
	} else if (second_feature == IMPLICIT_NODE) {
		if (first_feature == UNION_NODE) {
			for (unsigned int i = 0; i < first_excluded_count; i++)
				if (index_of(first_excluded[i], second_excluded, second_excluded_count) < second_excluded_count) return false;
			return true;
		} else {
			return index_of(first_feature, second_excluded, second_excluded_count) == second_excluded_count;
		}
	} else if (first_feature == UNION_NODE) {
		if (second_feature == UNION_NODE) {
			return is_subset(first_excluded, first_excluded_count, second_excluded, second_excluded_count);
		} else {
			return false;
		}
	} else if (second_feature == UNION_NODE) {
		return index_of(first_feature, second_excluded, second_excluded_count) < second_excluded_count;
	} else {
		return first_feature == second_feature;
	}
}

template<typename RulePrior, typename Semantics,
	typename TerminalPrinter, typename NonterminalPrinter,
	typename StringMapType>
bool is_parseable(hdp_rule_distribution<RulePrior, Semantics>& distribution,
		const syntax_node<Semantics>& syntax,
		const Semantics& logical_form, Semantics& logical_form_set,
		pair<TerminalPrinter&, NonterminalPrinter&>& printers,
		const StringMapType& token_map)
{
	if (distribution.type == PRETERMINAL_NUMBER) {
		Semantics& new_logical_form_set = *((Semantics*) alloca(sizeof(Semantics)));
		if (!parse_number(syntax.right, logical_form_set, new_logical_form_set, token_map)) {
			print("is_parseable ERROR: Unable to interpret number for preterminal_number at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			return false;
		}
		free(logical_form_set);
		move(new_logical_form_set, logical_form_set);
		return true;
	} else if (distribution.type == PRETERMINAL_STRING) {
		Semantics& new_logical_form_set = *((Semantics*) alloca(sizeof(Semantics)));
		if (!parse_string(syntax.right, logical_form_set, new_logical_form_set, token_map)) {
			print("is_parseable ERROR: Unable to interpret string for preterminal_string at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			return false;
		}
		free(logical_form_set);
		move(new_logical_form_set, logical_form_set);
		return true;
	}

	double prior_probability;
	if (syntax.right.is_terminal()) {
		rule<Semantics> terminal_rule(sequence(syntax.right.t.terminals, syntax.right.t.length));
		prior_probability = distribution.h.pi.probability(terminal_rule);
	} else {
		prior_probability = distribution.h.pi.probability(syntax.right);
	}
	if (prior_probability == 0.0) {
		print("is_parseable ERROR: The following rule has zero prior probability: ", stderr);
		print(syntax.right, stderr, printers); print('\n', stderr);
		return false;
	}

	/* set the semantic features */
	for (unsigned int i = 0; i < distribution.feature_count; i++) {
		unsigned int expected_feature;
		unsigned int* expected_excluded;
		unsigned int expected_excluded_count = 0;
		if (!get_feature(distribution.feature_sequence[i], logical_form,
				expected_feature, expected_excluded, expected_excluded_count))
		{
			print("is_parseable ERROR: Unable to get semantic feature '", stderr);
			Semantics::print(distribution.feature_sequence[i], stderr);
			print("' from ground truth logical form at rule: ", stderr);
			print("      True logical form: ", stderr); print(logical_form, stderr, printers.key); print('\n', stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			return false;
		}

		unsigned int feature;
		unsigned int* excluded;
		unsigned int excluded_count = 0;
		if (!get_feature(distribution.feature_sequence[i], logical_form_set, feature, excluded, excluded_count)) {
			print("is_parseable ERROR: Unable to get semantic feature '", stderr);
			Semantics::print(distribution.feature_sequence[i], stderr);
			print("' from logical form set at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			print("  Logical form: ", stderr); print(logical_form_set, stderr, printers.key); print('\n', stderr);
			if (expected_excluded_count != 0) free(expected_excluded);
			return false;
		} else if (!is_subset(expected_feature, expected_excluded, expected_excluded_count, feature, excluded, excluded_count)) {
			print("is_parseable ERROR: The semantic feature '", stderr);
			Semantics::print(distribution.feature_sequence[i], stderr);
			print("' of the ground truth logical form is not a subset of that of the logical form set at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			print("      True logical form: ", stderr); print(logical_form, stderr, printers.key); print('\n', stderr);
			print("  Computed logical form: ", stderr); print(logical_form_set, stderr, printers.key); print('\n', stderr);
			if (expected_excluded_count != 0) free(expected_excluded);
			if (excluded_count != 0) free(excluded);
			return false;
		}
		if (excluded_count != 0) free(excluded);

		Semantics old_logical_form_set = logical_form_set;
		if (expected_feature == IMPLICIT_NODE) {
			if (!exclude_features(distribution.feature_sequence[i], logical_form_set, expected_excluded, expected_excluded_count)) {
				print("is_parseable ERROR: Unable to exclude semantic feature '", stderr);
				Semantics::print(distribution.feature_sequence[i], stderr); print("' at rule: ", stderr);
				print(syntax.right, stderr, printers); print('\n', stderr);
				if (expected_excluded_count != 0) free(expected_excluded);
				return false;
			}
		} else if (!set_feature(distribution.feature_sequence[i], logical_form_set, expected_feature)) {
			fprintf(stderr, "is_parseable ERROR: Unable to set semantic feature '");
			Semantics::print(distribution.feature_sequence[i], stderr); print("' for logical form ", stderr);
			print(old_logical_form_set, stderr, printers.key); print(" at rule: ", stderr);
			print(syntax.right, stderr, printers); print('\n', stderr);
			if (expected_excluded_count != 0) free(expected_excluded);
			return false;
		}
		if (expected_excluded_count != 0) free(expected_excluded);
	}
	return true;
}


/**
 * Functions for reading/writing hdp_tree_grammar structure from/to a file.
 */

template<typename RulePrior, typename Semantics, typename Stream, typename... Args>
bool read(
		hdp_grammar<RulePrior, Semantics>& G,
		syntax_node<Semantics>** syntax,
		unsigned int sentence_count,
		Stream& stream, Args&&... scribes)
{
	if (!read_random_state(stream) || !read(G, stream, std::forward<Args>(scribes)...))
		return false;
	for (unsigned int i = 0; i < sentence_count; i++) {
		syntax[i] = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
		if (syntax[i] == NULL || !read(*syntax[i], stream, std::forward<Args>(scribes)...))
		{
			fprintf(stderr, "read ERROR: Unable to read syntax tree %u from saved sampler state.\n", i);
			free(G);
			if (syntax[i] != NULL)
				free(syntax[i]);
			syntax[i] = NULL;
			for (unsigned int j = 0; j < i; j++) {
				free(*syntax[j]); free(syntax[j]);
				syntax[j] = NULL;
				return false;
			}
		}
	}
	return true;
}

template<typename RulePrior, typename Semantics, typename Stream, typename... Args>
bool write(const hdp_grammar<RulePrior, Semantics>& G,
	const syntax_node<Semantics>* const* syntax,
	unsigned int sentence_count, Stream& stream, Args&&... scribes)
{
	if (!write_random_state(stream) || !write(G, stream, std::forward<Args>(scribes)...))
		return false;
	for (unsigned int i = 0; i < sentence_count; i++)
		if (!write(*syntax[i], stream, std::forward<Args>(scribes)...)) return false;
	return true;
}

#endif /* HDP_GRAMMAR_H_ */
