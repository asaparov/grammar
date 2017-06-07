/**
 * tree_semantics_hdp.h
 *
 *  Created on: Nov 14, 2016
 *      Author: asaparov
 */

#ifndef TREE_SEMANTICS_HDP_H_
#define TREE_SEMANTICS_HDP_H_

#include <hdp/mcmc.h>

#include "tree_semantics.h"

using namespace core;

struct tree_semantics_prior
{
	hdp<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> left_hdp;
	hdp_sampler<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> left_sampler;
	cache<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> left_cache;
	array_map<unsigned int, array<unsigned int>*> left_root_probabilities;
	array<unsigned int>* unseen_left_root_probabilities;

	hdp<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> right_hdp;
	hdp_sampler<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> right_sampler;
	cache<uniform_distribution<double>, constant<unsigned int>, unsigned int, double> right_cache;
	array_map<unsigned int, array<unsigned int>*> right_root_probabilities;
	array<unsigned int>* unseen_right_root_probabilities;

	array_map<unsigned int, pair<unsigned int*, unsigned int>> left_observations;
	array_map<unsigned int, pair<unsigned int*, unsigned int>> right_observations;
	pair<unsigned int*, unsigned int> all_labels;

	hash_map<tree_semantics, double> probability_cache;
	std::mutex lock;

	tree_semantics_prior(unsigned int entity_count, const double* left_alpha, const double* right_alpha) :
		left_hdp(entity_count, left_alpha, 2), left_sampler(left_hdp),
		left_cache(left_sampler), left_root_probabilities(256), unseen_left_root_probabilities(NULL),
		right_hdp(entity_count, right_alpha, 3), right_sampler(right_hdp),
		right_cache(right_sampler), right_root_probabilities(256), unseen_right_root_probabilities(NULL),
		left_observations(16), right_observations(16), all_labels(NULL, 0), probability_cache(1024)
	{ }

	~tree_semantics_prior() {
		for (auto entry : left_root_probabilities)
			cleanup_root_probabilities(entry.value, left_sampler.posterior.length);
		for (auto entry : right_root_probabilities)
			cleanup_root_probabilities(entry.value, right_sampler.posterior.length);
		for (auto entry : probability_cache)
			core::free(entry.key);
		if (unseen_left_root_probabilities != NULL)
			cleanup_root_probabilities(unseen_left_root_probabilities, left_sampler.posterior.length);
		if (unseen_right_root_probabilities != NULL)
			cleanup_root_probabilities(unseen_right_root_probabilities, right_sampler.posterior.length);
		for (auto entry : left_observations)
			core::free(entry.value.key);
		for (auto entry : right_observations)
			core::free(entry.value.key);
		if (all_labels.key != NULL)
			core::free(all_labels.key);
	}

	bool train(const tree_semantics* examples, unsigned int length,
			unsigned int burn_in, unsigned int iterations, unsigned int skip)
	{
		hash_map<unsigned int, hash_set<unsigned int>> train_left_observations(64);
		hash_map<unsigned int, hash_set<unsigned int>> train_right_observations(64);
		for (unsigned int i = 0; i < length; i++) {
			if (!add_training_example(examples[i], train_left_observations, train_right_observations)) {
				free_observations(train_left_observations);
				free_observations(train_right_observations);
				return false;
			}
		}

		/* perform MCMC on the left semantics model */
		prepare_sampler(left_sampler, left_cache);
		for (unsigned int i = 0; i < burn_in; i++)
			sample_hdp<true>(left_sampler, left_cache);
		for (unsigned int i = 0; i < iterations; i++) {
			sample_hdp<true>(left_sampler, left_cache);
			if (i % skip == 0 && !left_sampler.add_sample()) {
				free_observations(train_left_observations);
				free_observations(train_right_observations);
				return false;
			}
		}

		/* perform MCMC on the right semantics model */
		prepare_sampler(right_sampler, right_cache);
		for (unsigned int i = 0; i < burn_in; i++)
			sample_hdp<true>(right_sampler, right_cache);
		for (unsigned int i = 0; i < iterations; i++) {
			sample_hdp<true>(right_sampler, right_cache);
			if (i % skip == 0 && !right_sampler.add_sample()) {
				free_observations(train_left_observations);
				free_observations(train_right_observations);
				return false;
			}
		}

		/* compute left_observations and right_observations */
		if (!left_observations.ensure_capacity(train_left_observations.table.size)
		 || !right_observations.ensure_capacity(train_right_observations.table.size)
		 || !add_observations(train_left_observations, left_observations)
		 || !add_observations(train_right_observations, right_observations)) {
			free_observations(train_left_observations);
			free_observations(train_right_observations);
			return false;
		}
		free_observations(train_left_observations);
		free_observations(train_right_observations);

		/* compute the set of all labels */
		all_labels.key = (unsigned int*) malloc(sizeof(unsigned int) * (left_observations.size + right_observations.size + 1));
		if (all_labels.key == NULL) {
			fprintf(stderr, "tree_semantics_prior.train ERROR: Out of memory.\n");
			return false;
		}
		set_union(all_labels.key, all_labels.value,
				left_observations.keys, left_observations.size,
				right_observations.keys, right_observations.size);
		all_labels.key[all_labels.value] = LABEL_EMPTY;
		all_labels.value++;
		insertion_sort(all_labels.key, all_labels.value);

		/* take the union of the left and right observation sets */
		hash_set<unsigned int> all_left_observations(64);
		hash_set<unsigned int> all_right_observations(64);
		for (auto entry : left_observations)
			if (!all_left_observations.add_all(entry.value.key, entry.value.value))
				return false;
		for (auto entry : right_observations)
			if (!all_right_observations.add_all(entry.value.key, entry.value.value))
				return false;

		/* precompute the root probabilities */
		for (unsigned int& observation : all_left_observations)
			if (!left_root_probabilities.put(observation, left_cache.compute_root_probabilities(left_sampler, observation)))
				return false;
		unseen_left_root_probabilities = left_cache.compute_root_probabilities(left_sampler, IMPLICIT_NODE);
		for (unsigned int& observation : all_right_observations)
			if (!right_root_probabilities.put(observation, right_cache.compute_root_probabilities(right_sampler, observation)))
				return false;
		unseen_right_root_probabilities = right_cache.compute_root_probabilities(right_sampler, IMPLICIT_NODE);

		if (left_root_probabilities.size > 1)
			sort(left_root_probabilities.keys, left_root_probabilities.values, left_root_probabilities.size);
		if (right_root_probabilities.size > 1)
			sort(right_root_probabilities.keys, right_root_probabilities.values, right_root_probabilities.size);

		return (unseen_left_root_probabilities != NULL && unseen_right_root_probabilities != NULL);
	}

	inline double log_probability(const tree_semantics& example) {
		if (example.label == LABEL_WILDCARD_TREE)
			return 0.0;
		return log_probability(example, example.label);
	}

private:
	inline void free_observations(hash_map<unsigned int, hash_set<unsigned int>>& map) {
		for (auto entry : map)
			core::free(entry.value);
	}

	inline bool add_observations(
			const hash_map<unsigned int, hash_set<unsigned int>>& train_observations,
			array_map<unsigned int, pair<unsigned int*, unsigned int>>& observations)
	{
		for (auto entry : train_observations) {
			unsigned int length = 0;
			unsigned int* set = (unsigned int*) malloc(sizeof(unsigned int) * entry.value.size);
			if (set == NULL)
				return false;
			for (unsigned int element : entry.value) {
				set[length] = element;
				length++;
			}
			sort(set, length);
			observations.keys[observations.size] = entry.key;
			observations.values[observations.size] = { set, length };
			observations.size++;
		}
		return true;
	}

	bool add_training_example(const tree_semantics& example,
			hash_map<unsigned int, hash_set<unsigned int>>& left_observations,
			hash_map<unsigned int, hash_set<unsigned int>>& right_observations)
	{
		unsigned int left = (example.left_child == NULL ? LABEL_EMPTY : example.left_child->label);
		unsigned int right = (example.right_child == NULL ? LABEL_EMPTY : example.right_child->label);
		unsigned int path[] = { example.label, left, right };

		bool contains; unsigned int left_index, right_index;
		if (!left_observations.check_size() || !right_observations.check_size())
			return false;
		hash_set<unsigned int>& left_observation_set = left_observations.get(example.label, contains, left_index);
		hash_set<unsigned int>& right_observation_set = right_observations.get(example.label, contains, right_index);
		if (!contains) {
			if (!hash_set_init(left_observation_set, 16)) {
				return false;
			} else if (!hash_set_init(right_observation_set, 16)) {
				core::free(left_observation_set);
				return false;
			}
			left_observations.table.keys[left_index] = example.label;
			right_observations.table.keys[right_index] = example.label;
			left_observations.table.size++;
			right_observations.table.size++;
		}

		if (!add(left_sampler, path, 1, left, left_cache)
		 || !add(right_sampler, path, 2, right, right_cache)
		 || !left_observation_set.add(left) || !right_observation_set.add(right))
			return false;
		if (example.left_child != NULL && !add_training_example(*example.left_child, left_observations, right_observations))
			return false;
		if (example.right_child != NULL && !add_training_example(*example.right_child, left_observations, right_observations))
			return false;
		return true;
	}

	inline double max_left_posterior(
			unsigned int left, const unsigned int* path,
			const unsigned int* const* excluded,
			const unsigned int* excluded_counts,
			const array<unsigned int>* left_root)
	{
		array<weighted_feature_set<double>> paths = array<weighted_feature_set<double>>(8);
		predict(left_sampler, left, path, excluded, excluded_counts, paths, left_root);
		double score = max(paths);
		for (weighted_feature_set<double>& path : paths)
			core::free(path);
		return score;
	}

	inline double max_right_posterior(
			unsigned int right, const unsigned int* path,
			const unsigned int* const* excluded,
			const unsigned int* excluded_counts,
			const array<unsigned int>* right_root)
	{
		array<weighted_feature_set<double>> paths = array<weighted_feature_set<double>>(8);
		predict(right_sampler, right, path, excluded, excluded_counts, paths, right_root);

		double score = max(paths);
		for (weighted_feature_set<double>& path : paths)
			core::free(path);
		return score;
	}

	double log_probability(const tree_semantics& example, unsigned int label)
	{
		/* first check the cache if we've computed the probability of this logical form before */
		bool contains; unsigned int index;
		lock.lock();
		if (!probability_cache.check_size()) {
			fprintf(stderr, "tree_semantics_prior.probabililty ERROR: Unable to expand probability cache.\n");
			exit(EXIT_FAILURE);
		}
		double score = probability_cache.get(example, contains, index);
		lock.unlock();
		if (contains) return score;
		score = 0.0;

		/* the logical form isn't cached, so compute its log probability */
		unsigned int left, right;
		unsigned int* excluded[2];
		unsigned int excluded_counts[2];
		excluded[0] = example.excluded;
		excluded_counts[0] = example.excluded_count;
		if (example.left_child == NULL) {
			left = LABEL_EMPTY;
			excluded_counts[1] = 0;
		} else {
			left = example.left_child->label;
			if (left == LABEL_WILDCARD_TREE) left = LABEL_WILDCARD;
			excluded[1] = example.left_child->excluded;
			excluded_counts[1] = example.left_child->excluded_count;
		}
		if (example.right_child == NULL) {
			right = LABEL_EMPTY;
		} else {
			right = example.right_child->label;
			if (right == LABEL_WILDCARD_TREE) right = LABEL_WILDCARD;
		}

		unsigned int path[] = { label, left };
		if (left != LABEL_WILDCARD) {
			unsigned int index = left_root_probabilities.index_of(left);
			array<unsigned int>* left_root = (index < left_root_probabilities.size) ? left_root_probabilities.values[index] : unseen_left_root_probabilities;
			score = max_left_posterior(left, path, excluded, excluded_counts, left_root);
		} else {
			double left_score = max_left_posterior(LABEL_WILDCARD, path, excluded, excluded_counts, unseen_left_root_probabilities);
			auto do_subtract = [&](unsigned int i) {
				array<unsigned int>* left_root = left_root_probabilities.get(left_root_probabilities.keys[i]);
				left_score = max(left_score, max_left_posterior(left_root_probabilities.keys[i], path, excluded, excluded_counts, left_root));
			};
			set_subtract(do_subtract,
					left_root_probabilities.keys, left_root_probabilities.size,
					example.left_child->excluded, example.left_child->excluded_count);
			score = left_score;
		}

		if (right != LABEL_WILDCARD) {
			unsigned int index = right_root_probabilities.index_of(right);
			array<unsigned int>* right_root = (index < right_root_probabilities.size) ? right_root_probabilities.values[index] : unseen_right_root_probabilities;
			score += max_right_posterior(right, path, excluded, excluded_counts, right_root);
		} else {
			double right_score = max_right_posterior(LABEL_WILDCARD, path, excluded, excluded_counts, unseen_right_root_probabilities);
			auto do_subtract = [&](unsigned int i) {
				array<unsigned int>* right_root = right_root_probabilities.get(right_root_probabilities.keys[i]);
				right_score = max(right_score, max_right_posterior(right_root_probabilities.keys[i], path, excluded, excluded_counts, right_root));
			};
			set_subtract(do_subtract,
					right_root_probabilities.keys, right_root_probabilities.size,
					example.right_child->excluded, example.right_child->excluded_count);
			score += right_score;
		}

		/* recurse into the child nodes */
		if (example.left_child != NULL && example.left_child->label != LABEL_WILDCARD_TREE)
			score += log_probability(*example.left_child, left);
		if (example.right_child != NULL && example.right_child->label != LABEL_WILDCARD_TREE)
			score += log_probability(*example.right_child, right);

		/* add the result into the cache */
		lock.lock();
		double& cached_score = probability_cache.get(example, contains, index);
		if (!contains) {
			probability_cache.table.keys[index] = example;
			probability_cache.table.size++;
			cached_score = score;
		}
		lock.unlock();
		return score;
	}
};


/**
 * A useful data structure to split sets of tree_semantics
 * trees for a branch and bound search algorithm (such as
 * for parsing).
 */

/* forward declarations */

bool deep_copy(const tree_semantics& src, tree_semantics& dst);


inline bool deep_copy(const tree_semantics& src, tree_semantics*& dst)
{
	dst = (tree_semantics*) malloc(sizeof(tree_semantics));
	if (dst == NULL) {
		fprintf(stderr, "deep_copy ERROR: Out of memory.\n");
		return false;
	}
	if (!deep_copy(src, *dst)) {
		free(dst);
		return false;
	}
	return true;
}

bool deep_copy(const tree_semantics& src, tree_semantics& dst)
{
	dst.label = src.label;
	dst.reference_count = 1;
	if (src.excluded_count > 0) {
		dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * src.excluded_count);
		if (dst.excluded == NULL) {
			fprintf(stderr, "deep_copy ERROR: Insufficient memory for excluded array.\n");
			return false;
		}
		memcpy(dst.excluded, src.excluded, sizeof(unsigned int) * src.excluded_count);
	}
	dst.excluded_count = src.excluded_count;

	if (src.left_child == NULL) {
		dst.left_child = NULL;
	} else if (src.left_child == &WILDCARD_TREE) {
		dst.left_child = &WILDCARD_TREE;
		WILDCARD_TREE.reference_count++;
	} else if (!deep_copy(*src.left_child, dst.left_child)) {
		if (dst.excluded_count > 0)
			free(dst.excluded);
		return false;
	}

	if (src.right_child == NULL) {
		dst.right_child = NULL;
	} else if (src.right_child == &WILDCARD_TREE) {
		dst.right_child = &WILDCARD_TREE;
		WILDCARD_TREE.reference_count++;
	} else if (!deep_copy(*src.right_child, dst.right_child)) {
		if (dst.excluded_count > 0)
			free(dst.excluded);
		if (dst.left_child != NULL) {
			free(*dst.left_child);
			free(dst.left_child);
		}
		return false;
	}
	return true;
}

bool split(tree_semantics& root,
		tree_semantics& parent,
		tree_semantics*& node,
		const unsigned int* labels,
		unsigned int label_count,
		array<tree_semantics*>& ambiguous,
		tree_semantics*& unambiguous)
{
	if (!ambiguous.ensure_capacity(ambiguous.length + label_count)) {
		fprintf(stderr, "split ERROR: Unable to expand output array.\n");
		return false;
	}

	node->left_child = &WILDCARD_TREE;
	node->right_child = &WILDCARD_TREE;

	auto do_subtract = [&](unsigned int i) {
		if (labels[i] == LABEL_EMPTY) {
			tree_semantics* old_node = node;
			node = NULL;
			if (!check_arity(parent.label, parent)) {
				node = old_node;
				return;
			}
			if (!deep_copy(root, unambiguous))
				exit(EXIT_FAILURE);
			node = old_node;
		} else {
			node->label = labels[i];
			if (!check_arity(parent.label, parent))
				return;
			if (!deep_copy(root, ambiguous[ambiguous.length]))
				exit(EXIT_FAILURE);
			ambiguous.length++;
		}
	};
	set_subtract(do_subtract, labels, label_count, node->excluded, node->excluded_count);

	node->label = LABEL_WILDCARD_TREE;
	node->left_child = NULL; node->right_child = NULL;
	if (!node->exclude(labels, label_count))
		return false;
	if (!check_arity(parent.label, parent))
		return true;
	if (!deep_copy(root, ambiguous[ambiguous.length]))
		return false;
	ambiguous.length++;
	return true;
}

bool split(tree_semantics* set,
		array<tree_semantics*>& ambiguous,
		array<tree_semantics*>& unambiguous,
		const tree_semantics_prior& prior)
{
	/* first find the next ambiguous node in prefix order */
	tree_semantics* unambiguous_tree = NULL;
	array<pair<tree_semantics*, tree_semantics*>> stack(16);
	stack.data[0] = {set, NULL};
	stack.length++;
	while (stack.length > 0) {
		pair<tree_semantics*, tree_semantics*> element = stack.pop();
		tree_semantics* node = element.key;
		tree_semantics* parent = element.value;
		if (node->label == LABEL_WILDCARD_TREE && node->excluded_count < prior.all_labels.value)
		{
			/* this node can be expanded */
			tree_semantics*& child_ptr = (node == parent->left_child) ? parent->left_child : parent->right_child;
			if (child_ptr == &WILDCARD_TREE) {
				free(*child_ptr); if (child_ptr->reference_count == 0) free(child_ptr);
				child_ptr = (tree_semantics*) malloc(sizeof(tree_semantics));
				if (child_ptr == NULL) {
					fprintf(stderr, "split ERROR: Out of memory.\n");
					return false;
				}
				child_ptr->reference_count = 1;
				child_ptr->excluded_count = 0;
			}

			if (node->excluded_count == 0) {
				bool contains;
				auto& labels = prior.left_observations.get(parent->label, contains);
				if (contains) {
					if (!split(*set, *parent, child_ptr, labels.key, labels.value, ambiguous, unambiguous_tree))
						return false;
				} else {
					if (!split(*set, *parent, child_ptr, prior.all_labels.key, prior.all_labels.value, ambiguous, unambiguous_tree))
						return false;
				}
				break;
			} else if (node->excluded_count < prior.all_labels.value) {
				if (!split(*set, *parent, child_ptr, prior.all_labels.key, prior.all_labels.value, ambiguous, unambiguous_tree))
					return false;
				break;
			}
		}

		/* traverse tree nodes in prefix order */
		if (node->right_child != NULL && !stack.add({node->right_child, node}))
			return false;
		if (node->left_child != NULL && !stack.add({node->left_child, node}))
			return false;
	}

	if (unambiguous_tree == NULL)
		return true;
	if (stack.length > 0) {
		return ambiguous.add(unambiguous_tree);
	} else {
		return unambiguous.add(unambiguous_tree);
	}
}

#endif /* TREE_SEMANTICS_HDP_H_ */
