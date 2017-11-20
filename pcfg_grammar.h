/**
 * pcfg_grammar.h
 *
 *  Created on: Jul 18, 2016
 *      Author: asaparov
 */

#ifndef PCFG_GRAMMAR_H_
#define PCFG_GRAMMAR_H_

#include "grammar.h"
#include "morphology.h"

#include <math/multiset.h>

template<typename BaseDistribution, typename Likelihood>
struct conjugate_pair {
	bool preterminal;

	BaseDistribution pi;
	array_multiset<unsigned int> rules;
	unsigned int nonterminal_count;

	hash_map<rule<null_semantics>, array<weighted_feature_set<double>>*> posterior;
	hash_map<sequence, unsigned int> token_ids;

	inline bool has_nonterminal_rules() const {
		return !preterminal;
	}

	inline bool has_terminal_rules() const {
		return preterminal;
	}

	constexpr part_of_speech get_part_of_speech() const {
		return POS_OTHER;
	}

	inline void clear() {
		for (auto entry : posterior) {
			core::free(entry.key);
			for (unsigned int i = 0; i < entry.value->length; i++)
				core::free(entry.value->data[i]);
			core::free(*entry.value);
			core::free(entry.value);
		}
		posterior.clear();
	}

	static inline void free(conjugate_pair<BaseDistribution, Likelihood>& distribution) {
		distribution.clear();
		core::free(distribution.pi);
		core::free(distribution.rules);
		for (auto entry : distribution.token_ids)
			core::free(entry.key);
		core::free(distribution.token_ids);
		core::free(distribution.posterior);
	}
};

template<typename BaseDistribution, typename Likelihood, typename BaseParameters>
inline bool init(conjugate_pair<BaseDistribution, Likelihood>& distribution,
	bool is_preterminal, unsigned int nonterminal_count, const BaseParameters& params)
{
	distribution.preterminal = is_preterminal;
	distribution.nonterminal_count = nonterminal_count;
	if (!init(distribution.pi, params)) {
		return false;
	} else if (!init(distribution.rules, 16)) {
		free(distribution.pi);
		return false;
	} else if (!hash_map_init(distribution.token_ids, 32)) {
		free(distribution.pi);
		free(distribution.rules);
		return false;
	} else if (!hash_map_init(distribution.posterior, 32)) {
		free(distribution.pi);
		free(distribution.rules);
		free(distribution.token_ids);
		return false;
	}
	return true;
}

template<typename BaseDistribution, typename Likelihood, typename Semantics>
using pcfg_grammar = grammar<Semantics, conjugate_pair<BaseDistribution, Likelihood>>;

template<typename BaseDistribution, typename Likelihood, typename Semantics>
inline unsigned int get_rule_id(
	conjugate_pair<BaseDistribution, Likelihood>& distribution,
	const rule<Semantics>& rule)
{
	if (rule.is_terminal()) {
		if (!distribution.token_ids.check_size())
			exit(EXIT_FAILURE);

		bool contains; unsigned int index;
		const sequence& terminal = rule.get_terminal();
		unsigned int& id = distribution.token_ids.get(terminal, contains, index);
		if (!contains) {
			sequence::copy(terminal, distribution.token_ids.table.keys[index]);
			distribution.token_ids.table.size++;
			id = distribution.token_ids.table.size;
		}
		return id;
	} else {
		return rule.nonterminals[0] * distribution.nonterminal_count + rule.nonterminals[1];
	}
}

template<typename BaseDistribution, typename Likelihood, typename Semantics>
bool add(conjugate_pair<BaseDistribution, Likelihood>& distribution, const rule<Semantics>& rule, const null_semantics& logical_form, unsigned int count = 1)
{
	return distribution.rules.add(get_rule_id(distribution, rule), count);
}

template<typename BaseDistribution, typename Likelihood, typename Semantics>
bool remove(conjugate_pair<BaseDistribution, Likelihood>& distribution, const rule<Semantics>& rule, const null_semantics& logical_form)
{
	return distribution.rules.subtract(get_rule_id(distribution, rule)) < distribution.rules.counts.size;
}

template<bool DiscardImpossible, bool PruneAmbiguousLogicalForms,
	typename BaseDistribution, typename Likelihood, typename Semantics>
array<weighted_feature_set<double>>* log_conditional(
	conjugate_pair<BaseDistribution, Likelihood>& distribution,
	const rule<Semantics>& observation, const null_semantics& logical_form)
{
	if (!distribution.posterior.check_size())
		return NULL;

	bool contains; unsigned int index;
	array<weighted_feature_set<double>>*& list = distribution.posterior.get(observation, contains, index);
	if (!contains) {
		list = (array<weighted_feature_set<double>>*) malloc(sizeof(array<weighted_feature_set<double>>));
		if (list == NULL) return NULL;
		if (!array_init(*list, 1))  {
			free(list);
			return NULL;
		}
		distribution.posterior.table.keys[index] = observation;
		distribution.posterior.table.size++;
	}
	if (list->length > 0)
		return list;

	if (!init(list->data[0], 1))
		return NULL;
	list->length = 1;
	if (observation.is_terminal()) {
		/* every preterminal is assigned to a single terminal */
		if (observation.length > 1
		|| get_rule_id(distribution, observation) != distribution.rules.counts.keys[0]) {
			free(list->data[0]);
			list->length = 0;
		} else {
			list->data[0].log_probability = 0.0;
		}
	} else {
		/* nonterminal rules follow a Dirichlet-multinomial distribution */
		list->data[0].log_probability =
			Likelihood::log_conditional(distribution.pi, get_rule_id(distribution, observation), distribution.rules);
	}
	return list;
}

template<bool DiscardImpossible, bool PruneAmbiguousLogicalForms,
	typename BaseDistribution, typename Likelihood, typename StringMapType>
inline weighted<null_semantics>* log_conditional(
	conjugate_pair<BaseDistribution, Likelihood>& distribution,
	const rule<null_semantics>& observation, const null_semantics& logical_form,
	const StringMapType& token_map, unsigned int& length)
{
	length = 0;
	const array<weighted_feature_set<double>>* posterior =
			log_conditional<DiscardImpossible, PruneAmbiguousLogicalForms>(distribution, observation, logical_form);
	if (posterior == NULL) return NULL;

	weighted<null_semantics>* weighted_logical_forms = (weighted<null_semantics>*)
			malloc(sizeof(weighted<null_semantics>) * max((size_t) 1, posterior->length));
	if (weighted_logical_forms == NULL) {
		fprintf(stderr, "log_conditional ERROR: Unable to initialize weighted logical form array.\n");
		return NULL;
	}
	for (unsigned int i = 0; i < posterior->length; i++)
	{
		weighted<null_semantics>& item = weighted_logical_forms[length];
		item.log_probability = posterior->data[i].log_probability;
		length++;
	}
	return weighted_logical_forms;
}

template<typename BaseDistribution, typename Likelihood, typename Semantics>
bool get_rules(const conjugate_pair<BaseDistribution, Likelihood>& distribution,
	const null_semantics& logical_form, array<rule<Semantics>>& rules, double min_probability)
{
	/* naively consider every possible rule */
	/* TODO: this can obviously be made more efficient */
	double log_min_probability = log(min_probability);
	for (unsigned int i = 0; i < distribution.nonterminal_count; i++) {
		for (unsigned int j = 0; j < distribution.nonterminal_count; j++) {
			double log_conditional = Likelihood::log_conditional(
				distribution.pi, (i + 1) * distribution.nonterminal_count + (j + 1), distribution.rules);
			if (log_conditional + 1.0e-9 > log_min_probability) {
				if (!rules.ensure_capacity(rules.length + 1)) return false;
				rule<Semantics>& new_rule = rules[(unsigned int) rules.length];
				if (!init(new_rule, 2)) return false;
				new_rule.nonterminals[0] = i + 1;
				new_rule.nonterminals[1] = j + 1;
				new_rule.functions[0] = null_semantics::FUNCTION_IDENTITY;
				new_rule.functions[1] = null_semantics::FUNCTION_IDENTITY;
				rules.length++;
			}
		}
	}
	return true;
}

template<typename BaseDistribution, typename Likelihood, typename Semantics>
bool get_rules(const conjugate_pair<BaseDistribution, Likelihood>& distribution, array<rule<Semantics>>& rules) {
	/* for now, just retrieve all rules */
	for (unsigned int i = 0; i < distribution.nonterminal_count; i++) {
		for (unsigned int j = 0; j < distribution.nonterminal_count; j++) {
			if (!rules.ensure_capacity(rules.length + 1)) return false;
			rule<Semantics>& new_rule = rules[(unsigned int) rules.length];
			if (!init(new_rule, 2)) return false;
			new_rule.nonterminals[0] = i + 1;
			new_rule.nonterminals[1] = j + 1;
			new_rule.functions[0] = null_semantics::FUNCTION_IDENTITY;
			new_rule.functions[1] = null_semantics::FUNCTION_IDENTITY;
			rules.length++;
		}
	}
	return true;
}

template<typename BaseDistribution, typename Likelihood>
double max_log_conditional(
	conjugate_pair<BaseDistribution, Likelihood>& distribution,
	const rule<null_semantics>& observation, const null_semantics& logical_form,
	const string** token_map)
{
	array<weighted_feature_set<double>>* posterior = log_conditional<true, false>(distribution, observation, logical_form);
	if (posterior == NULL)
		exit(EXIT_FAILURE);
	else if (posterior->length == 0)
		return -std::numeric_limits<double>::infinity();

	return posterior->data[0].log_probability;
}

#endif /* PCFG_GRAMMAR_H_ */
