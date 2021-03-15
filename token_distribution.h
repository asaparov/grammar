/**
 * token_distribution.h
 *
 *  Created on: Jan 29, 2017
 *      Author: asaparov
 */

#ifndef TOKEN_DISTRIBUTION_H_
#define TOKEN_DISTRIBUTION_H_

#include <core/map.h>

using namespace core;

template<typename V>
struct token_distribution
{
	typedef V value_type;

	hash_map<unsigned int, pair<V, V>> probabilities;
	uint64_t atom_count;

	V prob;
	V dense_prob;
	V log_prob;

	token_distribution(uint64_t atom_count) :
		probabilities(16), atom_count(atom_count), prob(1.0 / atom_count), dense_prob(0.0), log_prob(-log(atom_count)) { }

	token_distribution(const token_distribution<V>& src) : probabilities(src.probabilities.table.capacity) {
		initialize(src);
	}

	bool set(unsigned int key, const V& probability) {
		if (!probabilities.check_size())
			return false;

		bool contains; unsigned int index;
		pair<V, V>& value = probabilities.get(key, contains, index);
		if (!contains) {
			probabilities.table.keys[index] = key;
			probabilities.table.size++;
			value.key = probability;
			value.value = log(probability);
		} else dense_prob -= value.key;

		dense_prob += probability;
		update_probabilities();
		return true;
	}

	inline V probability(unsigned int observation) const {
		bool contains;
		const pair<V, V>& entry = probabilities.get(observation, contains);
		if (contains) return entry.key;
		else return prob;
	}

	template<typename SequenceType>
	inline V probability(const SequenceType& sequence) const {
		if (sequence.length != 1) return 0;
		return probability(sequence[0]);
	}

	inline V log_probability(unsigned int observation) const {
		bool contains;
		const pair<V, V>& entry = probabilities.get(observation, contains);
		if (contains) return entry.value;
		else return log_prob;
	}

	template<typename SequenceType>
	inline V log_probability(const SequenceType& sequence) const {
		if (sequence.length != 1) return -std::numeric_limits<double>::infinity();
		return log_probability(sequence[0]);
	}

	inline void update_probabilities() {
		if (probabilities.table.size >= atom_count) {
			if (probabilities.table.size > atom_count || dense_prob == 0.0)
				fprintf(stderr, "token_distribution.update_probabilities WARNING: "
						"Hashtable contains at least as many elements as atom_count.\n");
			prob = 0.0;
			log_prob = -std::numeric_limits<V>::infinity();
		} else {
			prob = (1.0 - dense_prob) / (atom_count - probabilities.table.size);
			log_prob = log(prob);
		}
	}

	static inline bool copy(const token_distribution<V>& src, token_distribution<V>& dst) {
		return init(dst, src);
	}

	static inline void free(token_distribution<V>& distribution) {
		core::free(distribution.probabilities);
	}

private:
	inline void initialize(const token_distribution<V>& src) {
		atom_count = src.atom_count;
		dense_prob = src.dense_prob;
		log_prob = src.log_prob;
		prob = src.prob;
		memcpy(probabilities.values, src.probabilities.values,
				sizeof(pair<V, V>) * src.probabilities.table.capacity);
		memcpy(probabilities.table.keys, src.probabilities.table.keys,
				sizeof(unsigned int) * src.probabilities.table.capacity);
		probabilities.table.size = src.probabilities.table.size;
	}

	template<typename A>
	friend bool init(token_distribution<A>&, const token_distribution<A>&);
};

template<typename V>
inline bool init(token_distribution<V>& distribution, uint64_t atom_count)
{
	distribution.atom_count = atom_count;
	distribution.prob = 1.0 / atom_count;
	distribution.dense_prob = 0.0;
	distribution.log_prob = -log(atom_count);
	return hash_map_init(distribution.probabilities, 16);
}

template<typename V>
inline bool init(token_distribution<V>& distribution, const token_distribution<V>& src)
{
	if (!hash_map_init(distribution.probabilities, src.probabilities.table.capacity))
		return false;
	distribution.initialize(src);
	return true;
}

template<typename V, typename Stream>
bool read(token_distribution<V>& distribution, Stream& stream)
{
	if (!read(distribution.atom_count, stream)
	 || !read(distribution.probabilities, stream))
		return false;
	distribution.dense_prob = 0.0;
	for (const auto& entry : distribution.probabilities)
		distribution.dense_prob += entry.value.key;
	distribution.update_probabilities();
	return true;
}

template<typename V, typename Stream>
inline bool write(const token_distribution<V>& distribution, Stream& stream)
{
	return write(distribution.atom_count, stream)
		&& write(distribution.probabilities, stream);
}

template<typename V>
inline bool sample(const token_distribution<V>& distribution, unsigned int& output)
{
	V random = sample_uniform<V>();
	if (random < distribution.dense_prob
	 || distribution.probabilities.table.size >= distribution.atom_count)
	{
		V aggregator = 0.0;
		unsigned int last = 0;
		for (const auto& entry : distribution.probabilities) {
			last = entry.key;
			aggregator += entry.value.key;
			if (random < aggregator) {
				output = entry.key;
				return true;
			}
		}
		output = last;
	} else {
		/* we sample an element not in the hash_map, and we
		   assume the atoms are in the set {1, ..., atom_count} */
		output = sample_uniform(distribution.atom_count) + 1;
		while (distribution.probabilities.table.contains(output))
			output = sample_uniform(distribution.atom_count) + 1;
	}
	return true;
}

template<typename V>
inline bool sample(const token_distribution<V>& distribution, sequence& output)
{
	output.tokens = (unsigned int*) malloc(sizeof(unsigned int));
	if (output.tokens == NULL) {
		fprintf(stderr, "sample ERROR: Insufficient memory for token sequence.\n");
		return false;
	}
	output.length = 1;
	return sample(distribution, output.tokens[0]);
}

#endif /* TOKEN_DISTRIBUTION_H_ */
