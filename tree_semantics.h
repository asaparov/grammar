/**
 * tree_semantics.h
 *
 *  Created on: Jul 21, 2015
 *      Author: asaparov
 */

#ifndef TREE_SEMANTICS_H_
#define TREE_SEMANTICS_H_

#include "parser.h"

#include <atomic>
#include <core/map.h>
#include <limits.h>
#include <math.h>

using namespace core;

#define LABEL_EITHER (UINT_MAX - 3)
#define LABEL_EMPTY (UINT_MAX - 2)
#define LABEL_WILDCARD_TREE (UINT_MAX - 1)
#define LABEL_WILDCARD (UINT_MAX)

#define CHECK_ARITY /* comment this to disable arity checking */
//#define INTERSECTION_CACHE /* comment this to disable the intersection cache */
//#define PRECOMPUTE_HASH /* comment this to disable precomputation of hash values */

/* TODO: these are for profiling; delete them */
/*#include <core/timer.h>
double profiler_intersect_node = 0.0;
double profiler_intersect_first_null = 0.0;
double profiler_intersect_second_null = 0.0;
double profiler_intersect_first_wildcard_tree = 0.0;
double profiler_intersect_second_wildcard_tree = 0.0;
double profiler_intersect_first_wildcard = 0.0;
double profiler_intersect_second_wildcard = 0.0;
double profiler_intersect_first_either = 0.0;
double profiler_intersect_second_either = 0.0;
double profiler_intersect_hash = 0.0;
double profiler_tree_semantics_equality = 0.0;*/
/* TODO: these are for debugging; delete them */
bool semantics_debug_flag = false;
unsigned int semantics_debug = 0;


/* forward declarations */

template<typename V> struct tree_semantics_trie;


#if defined(CHECK_ARITY)

enum arity {
	TREE_SEMANTICS_ARITY_ZERO,
	TREE_SEMANTICS_ARITY_UNARY,
	TREE_SEMANTICS_ARITY_BINARY,
	TREE_SEMANTICS_ARITY_EITHER
};

array<arity> arity_table = array<arity>(16);

inline bool min_arity_zero(unsigned int label) {
	if (label == LABEL_WILDCARD || label >= arity_table.length)
		return true;
	return (arity_table[label] == TREE_SEMANTICS_ARITY_EITHER || arity_table[label] == TREE_SEMANTICS_ARITY_ZERO);
}

inline bool arity_one(unsigned int label) {
	if (label == LABEL_WILDCARD || label >= arity_table.length)
		return true;
	return (arity_table[label] != TREE_SEMANTICS_ARITY_ZERO);
}

inline bool min_arity_two(unsigned int label) {
	if (label == LABEL_WILDCARD || label >= arity_table.length)
		return false;
	return arity_table[label] == TREE_SEMANTICS_ARITY_BINARY;
}

inline bool max_arity_two(unsigned int label) {
	if (label == LABEL_WILDCARD || label >= arity_table.length)
		return true;
	return (arity_table[label] == TREE_SEMANTICS_ARITY_EITHER || arity_table[label] == TREE_SEMANTICS_ARITY_BINARY);
}

#else /* CHECK_ARITY */

constexpr bool min_arity_zero(unsigned int label) { return true; }
constexpr bool arity_one(unsigned int label) { return true; }
constexpr bool min_arity_two(unsigned int label) { return false; }
constexpr bool max_arity_two(unsigned int label) { return true; }

#endif /* CHECK_ARITY */


struct tree_semantics {
	unsigned int label;
	tree_semantics* left_child;
	tree_semantics* right_child;

	unsigned int* excluded;
	unsigned int excluded_count;

	mutable std::atomic_uint reference_count;

#if defined(PRECOMPUTE_HASH)
	unsigned int hash_value;
#endif

	template<typename V> using trie = tree_semantics_trie<V>;

	tree_semantics() : left_child(NULL), right_child(NULL), excluded_count(0), reference_count(1) { }

	explicit tree_semantics(unsigned int label) :
		label(label), left_child(NULL), right_child(NULL), excluded_count(0), reference_count(1)
	{
		recompute_hash();
	}

	tree_semantics(const tree_semantics& src) : reference_count(1) {
		if (!initialize(src))
			exit(EXIT_FAILURE);
	}

	~tree_semantics() { free(); }

	inline void operator = (const tree_semantics& src) {
		reference_count = 1;
		if (!initialize(src))
			exit(EXIT_FAILURE);
	}

	/* for debugging */
	inline bool is_valid(hash_map<const tree_semantics*, unsigned int>& reference_counts) const
	{
		bool contains; unsigned int index;
		if (!reference_counts.check_size()) return false;
		unsigned int& count = reference_counts.get(this, contains, index);
		if (!contains) {
			reference_counts.table.keys[index] = this;
			reference_counts.values[index] = 1;
			reference_counts.table.size++;
		} else count++;

		if (reference_count == 0) return false;
		if (left_child != NULL && !left_child->is_valid(reference_counts)) return false;
		if (right_child != NULL && !right_child->is_valid(reference_counts)) return false;
		if (excluded_count > 0 && (label == LABEL_WILDCARD || label == LABEL_WILDCARD_TREE))
			return false;
		return true;
	}

	inline bool check_reference_counts(const hash_map<const tree_semantics*, unsigned int>& reference_counts) const {
		bool contains;
		unsigned int expected = reference_counts.get(this, contains);
		if (!contains) return false;

		if (expected != reference_count) {
			fprintf(stderr, "tree_semantics.check_reference_counts ERROR:"
				" Reference counter is invalid. Expected %u but counter "
				"is currently %u.\n", expected, reference_count.load());
			return false;
		}

		if (left_child != NULL && !left_child->check_reference_counts(reference_counts))
			return false;
		if (right_child != NULL && !right_child->check_reference_counts(reference_counts))
			return false;
		return true;
	}

	inline bool exclude(unsigned int item)
	{
		if (excluded_count == 0) excluded = NULL;
		unsigned int* new_excluded = (unsigned int*) realloc(excluded, sizeof(double) * (excluded_count + 1));
		if (new_excluded == NULL) {
			fprintf(stderr, "tree_semantics.exclude ERROR: Out of memory.\n");
			return false;
		}
		excluded = new_excluded;
		unsigned int index = strict_linear_search(excluded, item, 0, excluded_count);
		if (index > 0 && excluded[index - 1] == item)
			return true;
		shift_right(excluded, excluded_count, index);
		excluded[index] = item;
		excluded_count++;
		return true;
	}

	inline bool exclude(const unsigned int* items, unsigned int item_count)
	{
		unsigned int* excluded_union = (unsigned int*) malloc(
			sizeof(unsigned int) * (excluded_count + item_count));
		if (excluded_union == NULL) {
			fprintf(stderr, "tree_semantics.exclude ERROR: Out of memory.\n");
			return false;
		}

		unsigned int excluded_union_count = 0;
		set_union(excluded_union, excluded_union_count, excluded, excluded_count, items, item_count);
		if (excluded_union_count == 0) {
			core::free(excluded_union);
			return true;
		} else if (excluded_count > 0)
			core::free(excluded);
		excluded = excluded_union;
		excluded_count = excluded_union_count;
		return true;
	}

	enum feature {
		FEATURE_NULL = 0,
		FEATURE_LABEL = 1,
		FEATURE_LABEL_LEFT = 2,
		FEATURE_LABEL_RIGHT = 3
	};

	enum function_type {
		FUNCTION_EMPTY = 0,
		FUNCTION_IDENTITY = 1,
		FUNCTION_LEFT = 2,
		FUNCTION_RIGHT = 3
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
	static inline bool print(const function& func, Stream& out) {
		switch (func.type) {
		case tree_semantics::FUNCTION_IDENTITY:
			return core::print("identity", out);
		case tree_semantics::FUNCTION_LEFT:
			return core::print("left", out);
		case tree_semantics::FUNCTION_RIGHT:
			return core::print("right", out);
		default:
			fprintf(stderr, "print ERROR: Unrecognized tree_semantics::function type.\n");
			return false;
		}
	}

	inline void recompute_hash() {
#if defined(PRECOMPUTE_HASH)
		hash_value = compute_hash(*this);
#endif
	}

	static inline unsigned int hash(const tree_semantics& logical_form) {
#if defined(PRECOMPUTE_HASH)
		return logical_form.hash_value;
#else
		return compute_hash(logical_form);
#endif
	}

	static inline unsigned int compute_hash(const tree_semantics& logical_form) {
		unsigned int hash_value = default_hash(logical_form.label);
		if (logical_form.left_child != NULL)
			hash_value ^= hash(*logical_form.left_child);
		if (logical_form.right_child != NULL)
			hash_value ^= hash(*logical_form.right_child);
		if (logical_form.excluded_count > 0)
			hash_value ^= default_hash(logical_form.excluded, logical_form.excluded_count);
		return hash_value;
	}

	static inline bool is_empty(const tree_semantics& logical_form) {
		return logical_form.label == 0;
	}

	static inline void move(const tree_semantics& src, tree_semantics& dst) {
		dst.label = src.label;
		dst.left_child = src.left_child;
		dst.right_child = src.right_child;
		dst.excluded_count = src.excluded_count;
		dst.excluded = src.excluded;
		dst.reference_count = src.reference_count.load();
#if defined(PRECOMPUTE_HASH)
		dst.hash_value = src.hash_value;
#endif
	}

	static inline void swap(tree_semantics& first, tree_semantics& second) {
		core::swap(first.label, second.label);
		core::swap(first.left_child, second.left_child);
		core::swap(first.right_child, second.right_child);
		core::swap(first.excluded, second.excluded);
		core::swap(first.excluded_count, second.excluded_count);
		first.reference_count = second.reference_count.exchange(first.reference_count);
#if defined(PRECOMPUTE_HASH)
		core::swap(first.hash_value, second.hash_value);
#endif
	}

	static inline void free(tree_semantics& logical_form) {
		logical_form.free();
	}

	static constexpr function default_function() {
		return FUNCTION_EMPTY;
	}

	static constexpr bool is_feature_pruneable(feature f) {
		return true;
	}

	static const function functions[];
	static const pair<function, function> transformations[];
	static const double log_function_count;
	static const double log_transformation_count;

private:
	inline bool initialize(const tree_semantics& src) {
		label = src.label;
		left_child = src.left_child;
		right_child = src.right_child;
		excluded_count = src.excluded_count;
		if (excluded_count > 0) {
			excluded = (unsigned int*) malloc(sizeof(unsigned int) * excluded_count);
			if (excluded == NULL) {
				fprintf(stderr, "tree_semantics.initialize ERROR: Out of memory.\n");
				return false;
			}
			memcpy(excluded, src.excluded, sizeof(unsigned int) * excluded_count);
		}
		if (left_child != NULL)
			left_child->reference_count++;
		if (right_child != NULL)
			right_child->reference_count++;
#if defined(PRECOMPUTE_HASH)
		hash_value = src.hash_value;
#endif
		return true;
	}

	inline void free() {
		reference_count--;
		if (reference_count == 0) {
			if (excluded_count > 0)
				core::free(excluded);
			if (left_child != NULL) {
				free(*left_child);
				if (left_child->reference_count == 0)
					core::free(left_child);
			}
			if (right_child != NULL) {
				free(*right_child);
				if (right_child->reference_count == 0)
					core::free(right_child);
			}
		}
	}
};

const tree_semantics::function tree_semantics::functions[] = { FUNCTION_IDENTITY, FUNCTION_LEFT, FUNCTION_RIGHT };
const pair<tree_semantics::function, tree_semantics::function> tree_semantics::transformations[] = {
	{FUNCTION_IDENTITY, FUNCTION_LEFT}, {FUNCTION_LEFT, FUNCTION_IDENTITY},
	{FUNCTION_IDENTITY, FUNCTION_RIGHT}, {FUNCTION_LEFT, FUNCTION_RIGHT}
	//{FUNCTION_IDENTITY, FUNCTION_LEFT}, {FUNCTION_LEFT, FUNCTION_IDENTITY}
};
const double tree_semantics::log_function_count = log(array_length(tree_semantics::functions));
const double tree_semantics::log_transformation_count = log(array_length(tree_semantics::transformations));


tree_semantics WILDCARD_TREE = tree_semantics(LABEL_WILDCARD_TREE);
tree_semantics EMPTY_TREE = tree_semantics(LABEL_EMPTY);

static inline void initialize_any(tree_semantics& logical_form) {
	logical_form.label = LABEL_WILDCARD_TREE;
	logical_form.excluded_count = 0;
	logical_form.reference_count = 1;
	logical_form.left_child = NULL;
	logical_form.right_child = NULL;
#if defined(PRECOMPUTE_HASH)
	logical_form.hash_value = WILDCARD_TREE.hash_value;
#endif
}

static inline void initialize_empty(tree_semantics& logical_form) {
	logical_form.label = LABEL_EMPTY;
	logical_form.excluded_count = 0;
	logical_form.reference_count = 1;
	logical_form.left_child = NULL;
	logical_form.right_child = NULL;
#if defined(PRECOMPUTE_HASH)
	logical_form.hash_value = EMPTY_TREE.hash_value;
#endif
}


#if defined(INTERSECTION_CACHE)

struct intersection_cache {
	hash_map<pair<tree_semantics, tree_semantics>, tree_semantics*> map;

	intersection_cache() : map(16384) { }

	~intersection_cache() {
		for (auto entry : map) {
			free(entry.key.key);
			free(entry.key.value);
			if (entry.value != NULL) {
				free(*entry.value);
				if (entry.value->reference_count == 0)
					free(entry.value);
			}
		}
	}
};

intersection_cache intersections;

#endif


inline bool is_excluded(const unsigned int* excluded, unsigned int excluded_count, unsigned int item) {
	return index_of(item, excluded, excluded_count) < excluded_count;
}

inline bool is_excluded(const tree_semantics& logical_form, unsigned int item) {
	return is_excluded(logical_form.excluded, logical_form.excluded_count, item);
}

template<typename Stream, typename Printer>
inline bool print(const tree_semantics& tree, Stream& out, Printer& printer) {
	bool success = true;
	if (tree.left_child == NULL) {
		success &= print(tree.label, out, printer);
		if (tree.right_child != NULL) {
			fprintf(stderr, "print WARNING: Unary node is right-leaning.\n");
			success &= print(*tree.right_child, out, printer);
		}
	} else {
		success &= print(tree.label, out, printer);
		if (tree.left_child != NULL) {
			success &= print('(', out) && print(*tree.left_child, out, printer);
			if (tree.right_child != NULL)
				success &= print(',', out) && print(*tree.right_child, out, printer);
			success &= print(')', out);
		}
	}
	return success;
}

template<typename Stream>
inline bool read(tree_semantics::function& function, Stream& stream) {
	unsigned char c;
	if (!read(c, stream)) return false;
	function.type = static_cast<tree_semantics::function_type>(c);
	return true;
}

template<typename Stream>
inline bool write(const tree_semantics::function& function, Stream& stream) {
	return write((unsigned char) function.type, stream);
}

template<typename Stream>
inline bool read(tree_semantics::feature& feature, Stream& stream) {
	unsigned char c;
	if (!read(c, stream)) return false;
	feature = static_cast<tree_semantics::feature>(c);
	return true;
}

template<typename Stream>
inline bool write(const tree_semantics::feature& feature, Stream& stream) {
	return write((unsigned char) feature, stream);
}

#if defined(CHECK_ARITY)
inline bool check_arity(unsigned int label, const tree_semantics& logical_form)
{
	if (label >= arity_table.length) {
		return true;
	} else if (arity_table[label] == TREE_SEMANTICS_ARITY_ZERO) {
		if (logical_form.left_child != NULL
		 && (logical_form.left_child->label != LABEL_WILDCARD_TREE || is_excluded(*logical_form.left_child, LABEL_EMPTY)))
			return false;
		if (logical_form.right_child != NULL
		 && (logical_form.right_child->label != LABEL_WILDCARD_TREE || is_excluded(*logical_form.right_child, LABEL_EMPTY)))
			return false;
		return true;
	} else if (arity_table[label] == TREE_SEMANTICS_ARITY_UNARY) {
		if (logical_form.left_child == NULL)
			return false;
		if (logical_form.right_child != NULL
		 && (logical_form.right_child->label != LABEL_WILDCARD_TREE || is_excluded(*logical_form.right_child, LABEL_EMPTY)))
			return false;
		return true;
	} else if (arity_table[label] == TREE_SEMANTICS_ARITY_BINARY) {
		if (logical_form.left_child == NULL)
			return false;
		if (logical_form.right_child == NULL)
			return false;
		return true;
	} else {
		return true;
	}
}
#else
constexpr bool check_arity(unsigned int label, const tree_semantics& logical_form) { return true; }
#endif

/* forward declarations */

bool operator != (const tree_semantics& first, const tree_semantics& second);

template<bool FirstReferenceable, bool SecondReferenceable>
bool intersect(tree_semantics*& dst, const tree_semantics* first, const tree_semantics* second);

void set_union(tree_semantics*& dst, const tree_semantics* first, const tree_semantics* second);

bool operator == (const tree_semantics& first, const tree_semantics& second)
{
	if (first.label != second.label)
		return false;
#if defined(PRECOMPUTE_HASH)
	if (first.hash_value != second.hash_value)
		return false;
#endif

	if (first.excluded_count != second.excluded_count)
		return false;
	/* we assume the excluded array is sorted */
	for (unsigned int i = 0; i < first.excluded_count; i++)
		if (first.excluded[i] != second.excluded[i])
			return false;

	/* compare child nodes */
	if (first.left_child == NULL) {
		if (second.left_child != NULL)
			return false;
	} else if (second.left_child == NULL) {
		return false;
	} else if (first.left_child != second.left_child
			&& !(*first.left_child == *second.left_child)) {
		return false;
	}

	if (first.right_child == NULL) {
		if (second.right_child != NULL)
			return false;
	} else if (second.right_child == NULL) {
		return false;
	} else if (first.right_child != second.right_child
			&& !(*first.right_child == *second.right_child)) {
		return false;
	}
	return true;
}

inline bool operator != (const tree_semantics& first, const tree_semantics& second) {
	return !(first == second);
}

constexpr bool operator == (const tree_semantics::function& first, const tree_semantics::function& second) {
	return first.type == second.type;
}

constexpr bool operator != (const tree_semantics::function& first, const tree_semantics::function& second) {
	return first.type != second.type;
}

constexpr bool operator < (const tree_semantics::function& first, const tree_semantics::function& second) {
	return first.type < second.type;
}

inline void new_tree_without_excluded(
	tree_semantics& dst, unsigned int label,
	tree_semantics* left_child, tree_semantics* right_child)
{
	dst.label = label;
	dst.reference_count = 1;
	dst.left_child = left_child;
	dst.right_child = right_child;
	if (left_child != NULL) left_child->reference_count++;
	if (right_child != NULL) right_child->reference_count++;
}

inline bool new_tree(tree_semantics& dst, unsigned int label,
	tree_semantics* left_child, tree_semantics* right_child,
	const unsigned int* excluded, unsigned int excluded_count)
{
	new_tree_without_excluded(dst, label, left_child, right_child);
	dst.excluded_count = excluded_count;
	if (excluded_count > 0) {
		dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * excluded_count);
		if (dst.excluded == NULL) {
			fprintf(stderr, "new_tree ERROR: Insufficient memory for excluded set.\n");
			dst.excluded_count = 0;
			free(dst);
			return false;
		}
		memcpy(dst.excluded, excluded, sizeof(unsigned int) * excluded_count);
	}
	dst.recompute_hash();
	return true;
}

inline tree_semantics* new_empty_tree(unsigned int label)
{
	tree_semantics* logical_form = (tree_semantics*) malloc(sizeof(tree_semantics));
	if (logical_form == NULL) {
		fprintf(stderr, "new_tree ERROR: Out of memory.\n");
		return NULL;
	}
	logical_form->label = label;
	logical_form->reference_count = 1;
	return logical_form;
}

inline tree_semantics* new_tree(unsigned int label,
	tree_semantics* left_child, tree_semantics* right_child,
	const unsigned int* excluded, unsigned int excluded_count)
{
	tree_semantics* logical_form = (tree_semantics*) malloc(sizeof(tree_semantics));
	if (logical_form == NULL) {
		fprintf(stderr, "new_tree ERROR: Out of memory.\n");
		return NULL;
	} else if (!new_tree(*logical_form, label, left_child, right_child, excluded, excluded_count)) {
		free(logical_form);
		return NULL;
	}
	return logical_form;
}

inline tree_semantics* new_tree_without_excluded(
		unsigned int label, tree_semantics* left_child, tree_semantics* right_child)
{
	tree_semantics* logical_form = (tree_semantics*) malloc(sizeof(tree_semantics));
	if (logical_form == NULL) {
		fprintf(stderr, "new_tree ERROR: Out of memory.\n");
		return NULL;
	}
	new_tree_without_excluded(*logical_form, label, left_child, right_child);
	return logical_form;
}

inline tree_semantics* copy(const tree_semantics& src) {
	return new_tree(src.label, src.left_child, src.right_child, src.excluded, src.excluded_count);
}

inline tree_semantics* copy_without_excluded(const tree_semantics& src) {
	return new_tree(src.label, src.left_child, src.right_child, NULL, 0);
}

const tree_semantics* apply(tree_semantics::function function, const tree_semantics& src)
{
	switch (function.type) {
	case tree_semantics::FUNCTION_IDENTITY:
		return &src;
	case tree_semantics::FUNCTION_LEFT:
		return src.left_child;
	case tree_semantics::FUNCTION_RIGHT:
		return src.right_child;
	default:
		fprintf(stderr, "apply ERROR: Unrecognized transformation function.\n");
		exit(EXIT_FAILURE);
	}
}

bool apply(tree_semantics::function function, const tree_semantics& src, tree_semantics& dst)
{
	switch (function.type) {
	case tree_semantics::FUNCTION_IDENTITY:
		dst = src;
		break;
	case tree_semantics::FUNCTION_LEFT:
		if (src.label == LABEL_WILDCARD_TREE) {
			dst = WILDCARD_TREE;
			return true;
		} else if (src.left_child == NULL) return false;
		dst = *src.left_child;
		break;
	case tree_semantics::FUNCTION_RIGHT:
		if (src.label == LABEL_WILDCARD_TREE) {
			dst = WILDCARD_TREE;
			return true;
		} else if (src.right_child == NULL) return false;
		dst = *src.right_child;
		break;
	default:
		fprintf(stderr, "apply ERROR: Unrecognized transformation function.\n");
		return false;
	}
	return true;
}

bool intersect_excluded(tree_semantics& intersection,
		const tree_semantics& first, const tree_semantics& second)
{
	intersection.excluded_count = 0;
	unsigned int excluded_count = first.excluded_count + second.excluded_count;
	if (excluded_count > 0) {
		intersection.excluded = (unsigned int*) malloc(sizeof(unsigned int) * excluded_count);
		if (intersection.excluded == NULL) {
			fprintf(stderr, "intersect_excluded ERROR: Unable to compute union of excluded sets.\n");
			return false;
		}
		set_union(intersection.excluded, intersection.excluded_count,
				first.excluded, first.excluded_count, second.excluded, second.excluded_count);
	}
	return true;
}

inline bool intersect_children(tree_semantics& intersection,
		const tree_semantics& first, const tree_semantics& second)
{
	/* intersect the children */
	intersection.left_child = NULL;
	intersection.right_child = NULL;
	if (!intersect<true, true>(intersection.left_child, first.left_child, second.left_child)
	 || !intersect<true, true>(intersection.right_child, first.right_child, second.right_child))
	{
		free(intersection);
		return false;
	}
	return true;
}

template<bool IntersectDescendants>
inline bool intersect_node(tree_semantics& dst, const tree_semantics* first, const tree_semantics* second)
{
//timer stopwatch_function;
#if !defined(NDEBUG)
	if ((first != NULL && first->label == LABEL_EITHER && first->excluded_count < 2)
	 || (second != NULL && second->label == LABEL_EITHER && second->excluded_count < 2))
		fprintf(stderr, "intersect_node WARNING: Invalid union-type tree_semantics structures.\n");
#endif

	/* intersect the labels */
	if (first == NULL || first->label == LABEL_EMPTY) {
//timer stopwatch;
		if (second == NULL || second->label == LABEL_EMPTY) {
			/* don't need to check exclusions */
		} else if (second->label == LABEL_WILDCARD || second->label == LABEL_WILDCARD_TREE) {
			if (is_excluded(*second, LABEL_EMPTY)) {
//profiler_intersect_first_null += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
		} else if (second->label == LABEL_EITHER) {
			if (!is_excluded(*second, LABEL_EMPTY))
				return false;
		} else {
			return false;
		}
		dst.label = LABEL_EMPTY; dst.reference_count = 1; dst.excluded_count = 0;
		dst.left_child = NULL; dst.right_child = NULL;
		return true;
//profiler_intersect_first_null += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
	} else if (second == NULL || second->label == LABEL_EMPTY) {
//timer stopwatch;
		if (first->label == LABEL_WILDCARD || first->label == LABEL_WILDCARD_TREE) {
			if (is_excluded(*first, LABEL_EMPTY)) {
	//profiler_intersect_second_null += stopwatch.nanoseconds();
	//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
		} else if (first->label == LABEL_EITHER) {
			if (!is_excluded(*first, LABEL_EMPTY))
				return false;
		} else {
			return false;
		}
		dst.label = LABEL_EMPTY; dst.reference_count = 1; dst.excluded_count = 0;
		dst.left_child = NULL; dst.right_child = NULL;
//profiler_intersect_second_null += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
		return true;
	} else if (first->label == LABEL_WILDCARD_TREE) {
//timer stopwatch;
		if (second->label == LABEL_WILDCARD || second->label == LABEL_WILDCARD_TREE) {
			if (IntersectDescendants) {
				dst = *second;
				if (!dst.exclude(first->excluded, first->excluded_count))
					exit(EXIT_FAILURE);
			} else {
				dst.label = second->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
				if (first->excluded_count + second->excluded_count > 0) {
					dst.excluded = (unsigned int*) malloc(
							sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
					set_union(dst.excluded, dst.excluded_count,
							first->excluded, first->excluded_count,
							second->excluded, second->excluded_count);
				}
			}
		} else if (second->label == LABEL_EITHER) {
			if (IntersectDescendants) {
				dst = *second;
				set_subtract(dst.excluded, dst.excluded_count, first->excluded, first->excluded_count);
			} else {
				dst.label = second->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
				dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * second->excluded_count);
				set_subtract(dst.excluded, dst.excluded_count,
						second->excluded, second->excluded_count,
						first->excluded, first->excluded_count);
			}

			if (dst.excluded_count == 0) {
				free(dst.excluded); free(dst);
//profiler_intersect_first_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			} else if (dst.excluded_count == 1) {
				dst.label = dst.excluded[0];
				free(dst.excluded);
				dst.excluded_count = 0;
			}
		} else {
			if (is_excluded(*first, second->label)) {
//profiler_intersect_first_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
			if (IntersectDescendants) {
				dst = *second;
			} else {
				dst.label = second->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
			}
		}
//profiler_intersect_first_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
		return true;
	} else if (second->label == LABEL_WILDCARD_TREE) {
//timer stopwatch;
		if (first->label == LABEL_WILDCARD) {
			if (IntersectDescendants) {
				dst = *first;
				if (!dst.exclude(second->excluded, second->excluded_count))
					exit(EXIT_FAILURE);
			} else {
				dst.label = first->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
				if (first->excluded_count + second->excluded_count > 0) {
					dst.excluded = (unsigned int*) malloc(
							sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
					set_union(dst.excluded, dst.excluded_count,
							first->excluded, first->excluded_count,
							second->excluded, second->excluded_count);
				}
			}
		} else if (first->label == LABEL_EITHER) {
			if (IntersectDescendants) {
				dst = *first;
				set_subtract(dst.excluded, dst.excluded_count, second->excluded, second->excluded_count);
			} else {
				dst.label = first->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
				dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * first->excluded_count);
				set_subtract(dst.excluded, dst.excluded_count,
						first->excluded, first->excluded_count,
						second->excluded, second->excluded_count);
			}

			if (dst.excluded_count == 0) {
				free(dst.excluded); free(dst);
//profiler_intersect_second_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			} else if (dst.excluded_count == 1) {
				dst.label = dst.excluded[0];
				free(dst.excluded);
				dst.excluded_count = 0;
			}
		} else {
			if (is_excluded(*second, first->label)) {
//profiler_intersect_second_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
			if (IntersectDescendants) {
				dst = *first;
			} else {
				dst.label = first->label;
				dst.reference_count = 1;
				dst.excluded_count = 0;
			}
		}
//profiler_intersect_second_wildcard_tree += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
		return true;
	} else if (first->label == LABEL_WILDCARD) {
//timer stopwatch;
		if (second->label == LABEL_WILDCARD) {
			dst.label = LABEL_WILDCARD;
			if (!intersect_excluded(dst, *first, *second))
				exit(EXIT_FAILURE);
		} else if (second->label == LABEL_EITHER) {
			dst.label = LABEL_EITHER;
			dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * second->excluded_count);
			dst.excluded_count = 0;
			set_subtract(dst.excluded, dst.excluded_count,
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count);
			if (dst.excluded_count == 0) {
				free(dst.excluded);
//profiler_intersect_first_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			} else if (dst.excluded_count == 1) {
				dst.label = dst.excluded[0];
				free(dst.excluded);
				dst.excluded_count = 0;
			}
		} else {
			if (is_excluded(*first, second->label)) {
//profiler_intersect_first_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
			dst.label = second->label;
			dst.excluded_count = 0;
		}
//profiler_intersect_first_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
	} else if (second->label == LABEL_WILDCARD) {
//timer stopwatch;
		if (first->label == LABEL_EITHER) {
			dst.label = LABEL_EITHER;
			dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * first->excluded_count);
			dst.excluded_count = 0;
			set_subtract(dst.excluded, dst.excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
			if (dst.excluded_count == 0) {
				free(dst.excluded);
//profiler_intersect_second_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			} else if (dst.excluded_count == 1) {
				dst.label = dst.excluded[0];
				free(dst.excluded);
				dst.excluded_count = 0;
			}
		} else {
			if (is_excluded(*second, first->label)) {
//profiler_intersect_second_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
			dst.label = first->label;
			dst.excluded_count = 0;
		}
//profiler_intersect_second_wildcard += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
	} else if (first->label == LABEL_EITHER) {
//timer stopwatch;
		if (second->label == LABEL_EITHER) {
			dst.label = LABEL_EITHER;
			dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * max(first->excluded_count, second->excluded_count));
			dst.excluded_count = 0;
			set_intersect(dst.excluded, dst.excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
			if (dst.excluded_count == 0) {
				free(dst.excluded);
//profiler_intersect_first_either += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			} else if (dst.excluded_count == 1) {
				dst.label = dst.excluded[0];
				free(dst.excluded);
				dst.excluded_count = 0;
			}
		} else {
			if (!is_excluded(*first, second->label)) {
//profiler_intersect_first_either += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
				return false;
			}
			dst.label = second->label;
			dst.excluded_count = 0;
		}
//profiler_intersect_first_either += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
	} else if (second->label == LABEL_EITHER) {
//timer stopwatch;
		if (!is_excluded(*second, first->label)) {
//profiler_intersect_second_either += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
			return false;
		}
		dst.label = first->label;
		dst.excluded_count = 0;
//profiler_intersect_second_either += stopwatch.nanoseconds();
//profiler_intersect_node += stopwatch_function.nanoseconds();
	} else if (first->label != second->label) {
//profiler_intersect_node += stopwatch_function.nanoseconds();
		return false;
	} else {
		dst.label = first->label;
		dst.excluded_count = 0;
	}

	dst.reference_count = 1;
//profiler_intersect_node += stopwatch_function.nanoseconds();
	return (!IntersectDescendants || intersect_children(dst, *first, *second));
}

inline bool intersect(tree_semantics& dst, const tree_semantics* first, const tree_semantics* second)
{
	tree_semantics* intersection;
	if (!intersect<false, false>(intersection, first, second) || intersection == NULL)
		return false;
	dst = *intersection;
	free(*intersection);
	if (intersection->reference_count == 0)
		free(intersection);
	return true;
}

template<bool FirstReferenceable, bool SecondReferenceable>
bool intersect(tree_semantics*& dst, const tree_semantics* first, const tree_semantics* second)
{
	/* some optimizations */
	if (first == &WILDCARD_TREE) {
		if (SecondReferenceable) {
			dst = (tree_semantics*) second;
			if (dst != NULL)
				dst->reference_count++;
			return true;
		} else {
			if (second != NULL)
				dst = copy(*second);
			else dst = NULL;
			return true;
		}
	} else if (second == &WILDCARD_TREE) {
		if (FirstReferenceable) {
			dst = (tree_semantics*) first;
			if (dst != NULL)
				dst->reference_count++;
			return true;
		} else {
			if (first != NULL)
				dst = copy(*first);
			else dst = NULL;
			return true;
		}
	}

#if defined(INTERSECTION_CACHE)
	bool contains; unsigned int index;
	auto both = pair<tree_semantics, tree_semantics>(
			(first == NULL) ? EMPTY_TREE : *first,
			(second == NULL) ? EMPTY_TREE : *second);
//timer stopwatch;
	dst = intersections.map.get(both, contains, index);
//profiler_intersect_hash += stopwatch.nanoseconds();
	if (contains) {
		if (dst == NULL) return false;
		else if (dst->label == LABEL_EMPTY)
			dst = NULL;
		else dst->reference_count++;
		return true;
	}
#endif

	dst = (tree_semantics*) malloc(sizeof(tree_semantics));
	if (dst == NULL) {
		fprintf(stderr, "intersect ERROR: Out of memory.\n");
		exit(EXIT_FAILURE);
	}

	if (!intersect_node<true>(*dst, first, second)) {
		free(dst); dst = NULL;
#if defined(INTERSECTION_CACHE)
		if (!intersections.map.check_size()) exit(EXIT_FAILURE);
		intersections.map.get(both, contains, index);
		intersections.map.table.keys[index] = both;
		intersections.map.values[index] = NULL;
		intersections.map.table.size++;
#endif
		return false;
	} else if (dst->label == LABEL_WILDCARD_TREE && dst->excluded_count == 0) {
		free(dst);
		dst = &WILDCARD_TREE;
		dst->reference_count++;
	} else if (dst->label == LABEL_EMPTY) {
		free(dst);
		dst = NULL;
	}

#if defined(INTERSECTION_CACHE)
	if (!intersections.map.check_size()) exit(EXIT_FAILURE);
	intersections.map.get(both, contains, index);
	intersections.map.table.keys[index] = both;
	intersections.map.table.size++;
	if (dst == NULL) {
		intersections.map.values[index] = &EMPTY_TREE;
		EMPTY_TREE.reference_count++;
	} else {
		intersections.map.values[index] = dst;
		dst->reference_count++;
	}
#endif
#if defined(PRECOMPUTE_HASH)
	if (dst != NULL)
		dst->recompute_hash();
#endif
	return true;
}

template<bool SecondReferenceable>
inline bool invert_function_left(tree_semantics*& dst,
	const tree_semantics& first, const tree_semantics& second)
{
	if (first.left_child == NULL) {
		if (first.label == LABEL_WILDCARD_TREE) {
			if (second.label == LABEL_EMPTY) {
				/* we disallow the left/right functions from returning empty nodes */
				return false;
			}
			tree_semantics* new_second = copy(second);
			if (new_second == NULL) exit(EXIT_FAILURE);
			if (new_second->label == LABEL_WILDCARD || new_second->label == LABEL_WILDCARD_TREE) {
				if (!new_second->exclude(LABEL_EMPTY)) exit(EXIT_FAILURE);
			} else if (new_second->label == LABEL_EMPTY) {
				unsigned int empty = LABEL_EMPTY;
				set_subtract(new_second->excluded, new_second->excluded_count, &empty, 1);
			}
			dst = new_tree(LABEL_WILDCARD, new_second, &WILDCARD_TREE, first.excluded, first.excluded_count);
			if (new_second != NULL)
				free(*new_second);
		} else return false;
	} else {
#if !defined(NDEBUG)
		/* wildcard trees must have null children */
		if (first.label == LABEL_WILDCARD_TREE)
			fprintf(stderr, "invert_function_left WARNING: Wildcard tree has non-empty children.\n");
#endif

		tree_semantics* inverse = (tree_semantics*) malloc(sizeof(tree_semantics));
		if (inverse == NULL) {
			fprintf(stderr, "invert_function_left ERROR: Out of memory.\n");
			exit(EXIT_FAILURE);
		}

		inverse->label = first.label;
		inverse->reference_count = 1;
		inverse->right_child = first.right_child;
		if (!intersect<true, SecondReferenceable>(
				inverse->left_child, first.left_child, &second) || inverse->left_child == NULL)
		{
			free(inverse);
			return false;
		}
		if (first.right_child != NULL)
			inverse->right_child->reference_count++;
		if (inverse->label != LABEL_EITHER && inverse->label != LABEL_WILDCARD && !check_arity(inverse->label, *inverse)) {
			inverse->excluded_count = 0;
			free(*inverse); free(inverse);
			return false;
		}

		/* we disallow the left/right functions from returning empty nodes */
		if (inverse->left_child->label == LABEL_WILDCARD || inverse->left_child->label == LABEL_WILDCARD_TREE) {
			if (!inverse->left_child->exclude(LABEL_EMPTY)) exit(EXIT_FAILURE);
		} else if (inverse->left_child->label == LABEL_EITHER) {
			unsigned int empty = LABEL_EMPTY;
			set_subtract(inverse->left_child->excluded, inverse->left_child->excluded_count, &empty, 1);
		}

		inverse->excluded_count = first.excluded_count;
		if (first.excluded_count > 0) {
			inverse->excluded = (unsigned int*) malloc(sizeof(unsigned int) * first.excluded_count);
			if (inverse->excluded == NULL) {
				fprintf(stderr, "invert_function_left ERROR: Insufficient memory for excluded set.\n");
				inverse->excluded_count = 0;
				free(*inverse); free(inverse);
				return false;
			}
			memcpy(inverse->excluded, first.excluded, sizeof(unsigned int) * first.excluded_count);
		}
		inverse->recompute_hash();
		dst = inverse;
	}
	return true;
}

template<bool SecondReferenceable>
inline bool invert_function_right(tree_semantics*& dst,
	const tree_semantics& first, const tree_semantics& second)
{
	if (first.right_child == NULL) {
		if (first.label == LABEL_WILDCARD_TREE) {
			if (second.label == LABEL_EMPTY) {
				/* we disallow the left/right functions from returning empty nodes */
				return false;
			}
			tree_semantics* new_second = copy(second);
			if (new_second == NULL) exit(EXIT_FAILURE);
			if (new_second->label == LABEL_WILDCARD || new_second->label == LABEL_WILDCARD_TREE) {
				if (!new_second->exclude(LABEL_EMPTY)) exit(EXIT_FAILURE);
			} else if (new_second->label == LABEL_EMPTY) {
				unsigned int empty = LABEL_EMPTY;
				set_subtract(new_second->excluded, new_second->excluded_count, &empty, 1);
			}
			dst = new_tree(LABEL_WILDCARD, &WILDCARD_TREE, new_second, first.excluded, first.excluded_count);
			if (new_second != NULL)
				free(*new_second);
		} else return false;
	} else {
#if !defined(NDEBUG)
		/* wildcard trees must have null children */
		if (first.label == LABEL_WILDCARD_TREE)
			fprintf(stderr, "invert_function_right WARNING: Wildcard tree has non-empty children.\n");
#endif

		tree_semantics* inverse = (tree_semantics*) malloc(sizeof(tree_semantics));
		if (inverse == NULL) {
			fprintf(stderr, "invert_function_right ERROR: Out of memory.\n");
			exit(EXIT_FAILURE);
		}

		inverse->label = first.label;
		inverse->reference_count = 1;
		inverse->left_child = first.left_child;
		if (!intersect<true, SecondReferenceable>(
				inverse->right_child, first.right_child, &second) || inverse->right_child == NULL)
		{
			free(inverse);
			return false;
		}
		if (inverse->left_child != NULL)
			inverse->left_child->reference_count++;
		if (inverse->label != LABEL_WILDCARD && !check_arity(inverse->label, *inverse)) {
			inverse->excluded_count = 0;
			free(*inverse); free(inverse);
			return false;
		}

		/* we disallow the left/right functions from returning empty nodes */
		if (inverse->right_child->label == LABEL_WILDCARD || inverse->right_child->label == LABEL_WILDCARD_TREE) {
			if (!inverse->right_child->exclude(LABEL_EMPTY)) exit(EXIT_FAILURE);
		} else if (inverse->right_child->label == LABEL_EITHER) {
			unsigned int empty = LABEL_EMPTY;
			set_subtract(inverse->right_child->excluded, inverse->right_child->excluded_count, &empty, 1);
		}

		inverse->excluded_count = first.excluded_count;
		if (first.excluded_count > 0) {
			inverse->excluded = (unsigned int*) malloc(sizeof(unsigned int) * first.excluded_count);
			if (inverse->excluded == NULL) {
				fprintf(stderr, "invert_function_left ERROR: Insufficient memory for excluded set.\n");
				inverse->excluded_count = 0;
				free(*inverse); free(inverse);
				return false;
			}
			memcpy(inverse->excluded, first.excluded, sizeof(unsigned int) * first.excluded_count);
		}
		inverse->recompute_hash();
		dst = inverse;
	}
	return true;
}

template<bool FirstReferenceable = true, bool SecondReferenceable = false>
bool invert(
	tree_semantics*& inverse,
	unsigned int& inverse_count,
	tree_semantics::function function,
	const tree_semantics& first,
	const tree_semantics& second)
{
	bool result;
	inverse_count = 1;
	switch (function.type) {
	case tree_semantics::FUNCTION_IDENTITY:
		result = intersect<FirstReferenceable, SecondReferenceable>(
				inverse, &first, &second);
		return (result && inverse != NULL);
	case tree_semantics::FUNCTION_LEFT:
		return invert_function_left<SecondReferenceable>(inverse, first, second);
	case tree_semantics::FUNCTION_RIGHT:
		return invert_function_right<SecondReferenceable>(inverse, first, second);
	default:
		fprintf(stderr, "invert ERROR: Invalid transformation function.\n");
		exit(EXIT_FAILURE);
	}
}

inline bool any_number(const tree_semantics& src) {
	fprintf(stderr, "any_number ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool get_number(const tree_semantics& src, int64_t& value) {
	fprintf(stderr, "get_number ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool set_number(tree_semantics& exp, const tree_semantics& set, int64_t value) {
	fprintf(stderr, "set_number ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool any_string(const tree_semantics& src) {
	fprintf(stderr, "any_string ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool get_string(const tree_semantics& src, string& value) {
	fprintf(stderr, "get_string ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool set_string(tree_semantics& exp, const tree_semantics& set, const string& value) {
	fprintf(stderr, "set_string ERROR: This is unimplemented for tree_semantics.\n");
	return false;
}

inline bool get_label(
	const tree_semantics& src, unsigned int& label,
	unsigned int*& excluded, unsigned int& excluded_count)
{
	excluded_count = src.excluded_count;
	if (src.excluded_count != 0) {
		excluded = (unsigned int*) malloc(sizeof(unsigned int) * src.excluded_count);
		if (excluded == nullptr) {
			fprintf(stderr, "get_label ERROR: Out of memory.\n");
			return false;
		}
		memcpy(excluded, src.excluded, sizeof(unsigned int) * src.excluded_count);
	}
	if (src.label == LABEL_WILDCARD_TREE)
		label = LABEL_WILDCARD;
	else label = src.label;
	return true;
}

bool get_feature(
	tree_semantics::feature feature,
	const tree_semantics& src,
	unsigned int& value,
	unsigned int*& excluded,
	unsigned int& excluded_count)
{
	switch (feature) {
	case tree_semantics::FEATURE_LABEL:
		return get_label(src, value, excluded, excluded_count);
	case tree_semantics::FEATURE_LABEL_LEFT:
		if (src.label == LABEL_WILDCARD_TREE)
			value = LABEL_WILDCARD;
		else if (src.left_child == NULL)
			value = LABEL_EMPTY;
		else if (!get_label(*src.left_child, value, excluded, excluded_count)) return false;
		return true;
	case tree_semantics::FEATURE_LABEL_RIGHT:
		if (src.label == LABEL_WILDCARD_TREE)
			value = LABEL_WILDCARD;
		else if (src.right_child == NULL)
			value = LABEL_EMPTY;
		else if (!get_label(*src.right_child, value, excluded, excluded_count)) return false;
		return true;
	default:
		fprintf(stderr, "get_feature ERROR: Unrecognized feature.\n");
		return false;
	}
}

inline bool set_label(
	tree_semantics& logical_form, unsigned int feature_value,
	const unsigned int* excluded, unsigned int excluded_count)
{
	if (logical_form.label == LABEL_WILDCARD || logical_form.label == LABEL_WILDCARD_TREE) {
		if (is_excluded(excluded, excluded_count, feature_value))
			return false;
		else {
			if (logical_form.label == LABEL_WILDCARD_TREE) {
				logical_form.left_child = &WILDCARD_TREE;
				logical_form.right_child = &WILDCARD_TREE;
				logical_form.left_child->reference_count++;
				logical_form.right_child->reference_count++;
			} else if (!check_arity(feature_value, logical_form))
				return false;

			logical_form.label = feature_value;
			if (logical_form.excluded_count > 0) {
				free(logical_form.excluded);
				logical_form.excluded_count = 0;
			}
			return true;
		}
	} else return (logical_form.label == feature_value);
}

inline bool set_label(tree_semantics& logical_form, unsigned int feature_value) {
	return set_label(logical_form, feature_value, logical_form.excluded, logical_form.excluded_count);
}

inline bool set_feature(
	tree_semantics::feature feature,
	tree_semantics& logical_form,
	unsigned int feature_value)
{
	tree_semantics* new_child;
	switch (feature) {
	case tree_semantics::FEATURE_LABEL:
		return set_label(logical_form, feature_value);
	case tree_semantics::FEATURE_LABEL_LEFT:
		if (logical_form.label == LABEL_WILDCARD_TREE) {
			if (feature_value != LABEL_EMPTY)
				logical_form.left_child = new_tree(feature_value, &WILDCARD_TREE, &WILDCARD_TREE, NULL, 0);
			else logical_form.left_child = NULL;
			logical_form.right_child = &WILDCARD_TREE;
			logical_form.right_child->reference_count++;
			logical_form.label = LABEL_WILDCARD;
			return true;
		} else if (logical_form.left_child == NULL) {
			return feature_value == LABEL_EMPTY;
		} else {
			if (feature_value == LABEL_EMPTY) {
				if (is_excluded(*logical_form.left_child, feature_value))
					return false;
				new_child = NULL;
				if (!min_arity_zero(logical_form.label))
					return false;
			} else {
				new_child = copy_without_excluded(*logical_form.left_child);
				if (!set_label(*new_child, feature_value,
					logical_form.left_child->excluded, logical_form.left_child->excluded_count))
				{
					free(*new_child); free(new_child);
					return false;
				} else if (!arity_one(logical_form.label)) {
					free(*new_child); free(new_child);
					return false;
				}
			}
			free(*logical_form.left_child);
			if (logical_form.left_child->reference_count == 0)
				free(logical_form.left_child);
			logical_form.left_child = new_child;
			return true;
		}
	case tree_semantics::FEATURE_LABEL_RIGHT:
		if (logical_form.label == LABEL_WILDCARD_TREE) {
			logical_form.left_child = &WILDCARD_TREE;
			logical_form.left_child->reference_count++;
			if (feature_value != LABEL_EMPTY)
				logical_form.right_child = new_tree(feature_value, &WILDCARD_TREE, &WILDCARD_TREE, NULL, 0);
			else logical_form.right_child = NULL;
			logical_form.label = LABEL_WILDCARD;
			return true;
		} else if (logical_form.right_child == NULL) {
			return feature_value == LABEL_EMPTY;
		} else {
			if (feature_value == LABEL_EMPTY) {
				if (is_excluded(*logical_form.right_child, feature_value))
					return false;
				new_child = NULL;
				if (min_arity_two(logical_form.label))
					return false;
			} else {
				new_child = copy_without_excluded(*logical_form.right_child);
				if (!set_label(*new_child, feature_value,
					logical_form.right_child->excluded, logical_form.right_child->excluded_count))
				{
					free(*new_child); free(new_child);
					return false;
				} else if (!max_arity_two(logical_form.label)) {
					free(*new_child); free(new_child);
					return false;
				}
			}
			free(*logical_form.right_child);
			if (logical_form.right_child->reference_count == 0)
				free(logical_form.right_child);
			logical_form.right_child = new_child;
			return true;
		}
	default:
		fprintf(stderr, "set_feature ERROR: Unrecognized feature.\n");
		exit(EXIT_FAILURE);
	}
}

inline bool exclude_features(
	tree_semantics::feature feature,
	tree_semantics& logical_form,
	const unsigned int* excluded,
	unsigned int excluded_count)
{
	tree_semantics* new_child;
	switch (feature) {
	case tree_semantics::FEATURE_LABEL:
		if (logical_form.label != LABEL_WILDCARD && logical_form.label != LABEL_WILDCARD_TREE) {
			return !is_excluded(excluded, excluded_count, logical_form.label);
		} else {
			return logical_form.exclude(excluded, excluded_count);
		}
	case tree_semantics::FEATURE_LABEL_LEFT:
		if (logical_form.label == LABEL_WILDCARD_TREE) {
			logical_form.left_child = new_tree(
				LABEL_WILDCARD, &WILDCARD_TREE, &WILDCARD_TREE, excluded, excluded_count);
			logical_form.right_child = &WILDCARD_TREE;
			logical_form.right_child->reference_count++;
			logical_form.label = LABEL_WILDCARD;
			return true;
		} else if (logical_form.left_child == NULL) {
			return true;
		} else {
			if (is_excluded(excluded, excluded_count, logical_form.left_child->label))
				return false;
			new_child = copy_without_excluded(*logical_form.left_child);
			new_child->excluded = (unsigned int*) malloc(
				sizeof(unsigned int) * (logical_form.left_child->excluded_count + excluded_count));
			set_union(new_child->excluded, new_child->excluded_count, excluded, excluded_count,
				logical_form.left_child->excluded, logical_form.left_child->excluded_count);
			if (new_child->excluded_count == 0)
				free(new_child->excluded);
			free(*logical_form.left_child);
			if (logical_form.left_child->reference_count == 0)
				free(logical_form.left_child);
			logical_form.left_child = new_child;
			return true;
		}
	case tree_semantics::FEATURE_LABEL_RIGHT:
		if (logical_form.label == LABEL_WILDCARD_TREE) {
			logical_form.left_child = &WILDCARD_TREE;
			logical_form.left_child->reference_count++;
			logical_form.right_child = new_tree(
				LABEL_WILDCARD, &WILDCARD_TREE, &WILDCARD_TREE, excluded, excluded_count);
			logical_form.label = LABEL_WILDCARD;
			return true;
		} else if (logical_form.right_child == NULL) {
			return true;
		} else {
			if (is_excluded(excluded, excluded_count, logical_form.right_child->label))
				return false;
			new_child = copy_without_excluded(*logical_form.right_child);
			new_child->excluded = (unsigned int*) malloc(
				sizeof(unsigned int) * (logical_form.right_child->excluded_count + excluded_count));
			set_union(new_child->excluded, new_child->excluded_count, excluded, excluded_count,
				logical_form.right_child->excluded, logical_form.right_child->excluded_count);
			if (new_child->excluded_count == 0)
				free(new_child->excluded);
			free(*logical_form.right_child);
			if (logical_form.right_child->reference_count == 0)
				free(logical_form.right_child);
			logical_form.right_child = new_child;
			return true;
		}
	default:
		fprintf(stderr, "exclude_features ERROR: Unrecognized feature.\n");
		exit(EXIT_FAILURE);
	}
}

static inline unsigned char get_selected(const tree_semantics::function& function) {
	switch (function.type) {
	case tree_semantics::FUNCTION_LEFT:
		return 1;
	case tree_semantics::FUNCTION_RIGHT:
		return 2;
	case tree_semantics::FUNCTION_IDENTITY:
		return 3;

	case tree_semantics::FUNCTION_EMPTY:
		break;
	}
	fprintf(stderr, "get_selected ERROR: Unrecognized function.\n");
	exit(EXIT_FAILURE);
}

void is_separable(
		const transformation<tree_semantics>* const transformations,
		unsigned int rule_length, bool* separable)
{
	unsigned char selected = 0; /* 0 is none, 1 is left, 2 is right, 3 is both */
	for (unsigned int i = 0; i < rule_length; i++) {
		if (transformations[i].function_count != 1) {
			/* we current don't support transformations with more than one function */
			separable[i] = false;
			continue;
		}

		unsigned int next = get_selected(transformations[i].functions[0]);
		if ((next & selected) == 0)
			separable[i] = true;
		else separable[i] = false;

		selected |= get_selected(transformations[i].functions[0]);
	}
}

template<bool First, typename EmitRootFunction, typename PartOfSpeechType>
inline bool morphology_parse(
		const dummy_morphology_parser& morph, const sequence& words, PartOfSpeechType pos,
		const tree_semantics& logical_form, EmitRootFunction emit_root)
{
	return emit_root(words, logical_form);
}

template<typename PartOfSpeechType>
constexpr bool morphology_is_valid(
		const dummy_morphology_parser& morph,
		const sequence& terminal, PartOfSpeechType pos,
		const tree_semantics& logical_form)
{
	return true;
}


/**
 * Some routines for initializing syntax trees.
 */

#include <grammar/grammar.h>

#include <core/random.h>
#include <core/utility.h>

template<typename Distribution>
bool sample_preterminal(
	const grammar<tree_semantics, Distribution>& G,
	const sequence& terminal, unsigned int& sample)
{
	array<unsigned int> preterminals = array<unsigned int>(G.nonterminals.length);
	for (unsigned int i = 0; i < G.nonterminals.length; i++) {
		if (!G.nonterminals[i].rule_distribution.has_terminal_rules())
			continue;
		auto& terminal_prior = G.nonterminals[i].rule_distribution.h.pi.terminal_prior;
		if (terminal_prior.probability(terminal) > 0.0)
			preterminals.add(G.nonterminals[i].id);
	}
	if (preterminals.length == 0)
		return false;
	sample = sample_uniform(preterminals);
	return true;
}

template<typename Distribution>
bool sample_nonterminal(const grammar<tree_semantics, Distribution>& G, unsigned int& sample) {
	array<unsigned int> nonterminals = array<unsigned int>(G.nonterminals.length);
	for (unsigned int i = 0; i < G.nonterminals.length; i++) {
		if (!G.nonterminals[i].rule_distribution.has_terminal_rules())
			nonterminals.add(G.nonterminals[i].id);
	}
	if (nonterminals.length == 0)
		return false;
	sample = sample_uniform(nonterminals);
	return true;
}

inline bool is_applicable(const tree_semantics& logical_form, const tree_semantics::function& func) {
	switch (func.type) {
	case tree_semantics::FUNCTION_LEFT:
		return logical_form.left_child != NULL;
	case tree_semantics::FUNCTION_RIGHT:
		return logical_form.right_child != NULL;
	default:
		return true;
	}
}

bool random_transformation(const tree_semantics& logical_form,
	tree_semantics::function& first, tree_semantics::function& second)
{
	array<unsigned int> available = array<unsigned int>(array_length(tree_semantics::transformations));
	for (unsigned int i = 0; i < array_length(tree_semantics::transformations); i++) {
		if (is_applicable(logical_form, tree_semantics::transformations[i].key)
		 && is_applicable(logical_form, tree_semantics::transformations[i].value))
			available.add(i);
	}
	if (available.length == 0) return false;
	unsigned int selected = sample_uniform(available);
	first = tree_semantics::transformations[selected].key;
	second = tree_semantics::transformations[selected].value;
	return true;
}

template<typename Distribution>
bool initialize_tree(
	const grammar<tree_semantics, Distribution>& G,
	syntax_node<tree_semantics>*& tree,
	const sequence& sentence,
	const tree_semantics& logical_form,
	unsigned int nonterminal = 1)
{
	tree = (syntax_node<tree_semantics>*) malloc(sizeof(syntax_node<tree_semantics>));
	if (tree == NULL) {
		exit(EXIT_FAILURE);
	} if (G.nonterminals[nonterminal - 1].rule_distribution.has_terminal_rules()) {
		/* this is a terminal */
		if (!init(*tree, sentence)) exit(EXIT_FAILURE);
		return true;
	}

	/* pick a random split point from {1, ..., n - 1} */
	unsigned int k = sample_uniform(sentence.length - 1) + 1;

	rule<tree_semantics>& branch = *((rule<tree_semantics>*) alloca(sizeof(rule<tree_semantics>)));
	branch.type = rule_type::NONTERMINAL;
	branch.nt.length = 2;
	branch.nt.transformations = (transformation<tree_semantics>*) malloc(sizeof(transformation<tree_semantics>) * branch.nt.length);
	branch.nt.nonterminals = (unsigned int*) malloc(sizeof(unsigned int) * branch.nt.length);
	branch.nt.transformations[0].function_count = 1;
	branch.nt.transformations[0].functions = (tree_semantics::function*) malloc(sizeof(tree_semantics::function) * branch.nt.transformations[0].function_count);
	branch.nt.transformations[1].function_count = 1;
	branch.nt.transformations[1].functions = (tree_semantics::function*) malloc(sizeof(tree_semantics::function) * branch.nt.transformations[1].function_count);
	if (!random_transformation(logical_form, branch.nt.transformations[0].functions[0], branch.nt.transformations[1].functions[0])) {
		free(tree); tree = NULL;
		free(branch); return false;
	}

	if (k == 1) {
		if (!sample_preterminal(G, {sentence.tokens, k}, branch.nt.nonterminals[0])) {
			free(tree); tree = NULL;
			free(branch); return false;
		}
	} else {
		if (!sample_nonterminal(G, branch.nt.nonterminals[0])) {
			free(tree); tree = NULL;
			free(branch); return false;
		}
	}

	if (sentence.length - k == 1) {
		if (!sample_preterminal(G, {sentence.tokens + k, sentence.length - k}, branch.nt.nonterminals[1])) {
			free(tree); tree = NULL;
			free(branch); return false;
		}
	} else {
		if (!sample_nonterminal(G, branch.nt.nonterminals[1])) {
			free(tree); tree = NULL;
			free(branch); return false;
		}
	}

	const tree_semantics* left = apply(branch.nt.transformations[0].functions[0], logical_form);
	const tree_semantics* right = apply(branch.nt.transformations[1].functions[0], logical_form);
	if (!init(*tree, branch)) exit(EXIT_FAILURE);
	if (!initialize_tree(G, tree->children[0], { sentence.tokens, k }, *left, branch.nt.nonterminals[0])) {
		free(*tree); free(tree);
		tree = NULL; free(branch);
		return false;
	} else if (!initialize_tree(G, tree->children[1],
			{ sentence.tokens + k, sentence.length - k }, *right, branch.nt.nonterminals[1]))
	{
		free(*tree); free(tree);
		tree = NULL; free(branch);
		return false;
	}
	free(branch);
	return true;
}

inline bool is_node_wildcard(const tree_semantics& node) {
	return node.label == LABEL_WILDCARD_TREE && !is_excluded(node, LABEL_EMPTY);
}

/**
 * For grammars that don't have semantic features of child
 * nodes, parsing will result in WILDCARD_TREE leaves, so
 * this function just removes them.
 */
inline bool remove_wildcard_leaves(const tree_semantics& src, tree_semantics& dst)
{
	dst.label = src.label;
	dst.excluded_count = src.excluded_count;
	if (dst.excluded_count > 0) {
		dst.excluded = (unsigned int*) malloc(sizeof(unsigned int) * dst.excluded_count);
		if (dst.excluded == NULL) {
			fprintf(stderr, "remove_wildcard_leaves ERROR: Out of memory.\n");
			return false;
		}
		memcpy(dst.excluded, src.excluded, sizeof(unsigned int) * dst.excluded_count);
	}
	dst.reference_count = 1;

	if (src.left_child != NULL) {
		if (is_node_wildcard(*src.left_child)) {
			dst.left_child = NULL;
		} else {
			dst.left_child = (tree_semantics*) malloc(sizeof(tree_semantics));
			if (!remove_wildcard_leaves(*src.left_child, *dst.left_child)) {
				free(dst.left_child);
				return false;
			}
		}
	} else {
		dst.left_child = NULL;
	}
	if (src.right_child != NULL) {
		if (is_node_wildcard(*src.right_child)) {
			dst.right_child = NULL;
		} else {
			dst.right_child = (tree_semantics*) malloc(sizeof(tree_semantics));
			if (!remove_wildcard_leaves(*src.right_child, *dst.right_child)) {
				free(dst.right_child);
				return false;
			}
		}
	} else {
		dst.right_child = NULL;
	}
	dst.recompute_hash();
	return true;
}

inline bool is_node_ambiguous(const tree_semantics& tree) {
	if (tree.label == LABEL_WILDCARD_TREE)
		return is_excluded(tree, LABEL_EMPTY);
	if (tree.label != LABEL_WILDCARD)
		return false;
	if (tree.left_child != NULL || tree.right_child != NULL)
		return true;
	return is_excluded(tree, LABEL_EMPTY);
}

bool is_ambiguous(const tree_semantics& tree) {
	if (is_node_ambiguous(tree))
		return true;

	if (tree.left_child != NULL && is_ambiguous(*tree.left_child))
		return true;
	if (tree.right_child != NULL && is_ambiguous(*tree.right_child))
		return true;
	//return false;

	/* disallow right-leaning trees */
	return (tree.left_child != NULL && tree.left_child->label == LABEL_WILDCARD_TREE
		 && tree.right_child != NULL && tree.right_child->label != LABEL_WILDCARD_TREE);
}


/**
 * Functionality for checking arity.
 */

#if defined(CHECK_ARITY)

inline arity to_arity(unsigned int arity) {
	if (arity == 0) return TREE_SEMANTICS_ARITY_ZERO;
	else if (arity == 1) return TREE_SEMANTICS_ARITY_UNARY;
	else if (arity == 2) return TREE_SEMANTICS_ARITY_BINARY;
	else {
		fprintf(stderr, "to_arity ERROR: Invalid arity.\n");
		exit(EXIT_FAILURE);
	}
}

bool add_arity(unsigned int label, arity n, const string** name_map)
{
	if (!arity_table.ensure_capacity(label + 1))
		return false;
	for (unsigned int i = (unsigned int) arity_table.length; i < label + 1; i++)
		arity_table[i] = TREE_SEMANTICS_ARITY_EITHER;
	arity_table.length = max(arity_table.length, (size_t) label + 1);

	if (arity_table[label] != n && arity_table[label] != TREE_SEMANTICS_ARITY_EITHER) {
		FILE* out = stderr;
		print("add_arity WARNING: Symbol ", out);
		if (name_map == NULL) print(label, out);
		else {
			print('\'', out); print(*name_map[label], out); print('\'', out);
		}
		print(" has multiple arities.\n", out);
		arity_table[label] = TREE_SEMANTICS_ARITY_EITHER;
	} else arity_table[label] = n;
	return true;
}

bool populate_arity_table(const tree_semantics& logical_form, const string** name_map)
{
	unsigned int arity = 0;
	if (logical_form.left_child != NULL) arity++;
	if (logical_form.right_child != NULL) arity++;

	if (!add_arity(logical_form.label, to_arity(arity), name_map))
		return false;

	if (logical_form.left_child != NULL
	 && !populate_arity_table(*logical_form.left_child, name_map))
		return false;
	if (logical_form.right_child != NULL
	 && !populate_arity_table(*logical_form.right_child, name_map))
		return false;
	return true;
}

inline bool populate_arity_table(
	const tree_semantics* logical_forms,
	unsigned int count, const string** name_map)
{
	for (unsigned int i = 0; i < count; i++)
		if (!populate_arity_table(logical_forms[i], name_map)) return false;
	return true;
}

unsigned int min_arity(const tree_semantics& logical_form) {
	bool right_nonempty =
		(logical_form.right_child != NULL &&
		 logical_form.right_child->label != LABEL_WILDCARD_TREE);

	if (logical_form.left_child == NULL) {
		if (right_nonempty) {
			fprintf(stderr, "min_arity ERROR: Node is right-leaning.\n");
			return 1;
		} else return 0;
	} else if (logical_form.left_child->label == LABEL_WILDCARD_TREE) {
		if (right_nonempty) {
			return 2;
		} else return 0;
	} else {
		if (right_nonempty) {
			return 2;
		} else return 1;
	}
}

unsigned int max_arity(const tree_semantics& logical_form) {
	if (logical_form.left_child == NULL) {
		if (logical_form.right_child == NULL)
			return 0;
		else return 1;
	} else {
		if (logical_form.right_child == NULL)
			return 1;
		else return 2;
	}
}

bool check_arity(const tree_semantics& logical_form) {
	arity ar =
		(logical_form.label == LABEL_WILDCARD || logical_form.label == LABEL_WILDCARD_TREE)
		? TREE_SEMANTICS_ARITY_EITHER : arity_table[logical_form.label];
	switch (ar) {
	case TREE_SEMANTICS_ARITY_ZERO:
		if (min_arity(logical_form) != 0)
			return false;
		break;
	case TREE_SEMANTICS_ARITY_UNARY:
		if (min_arity(logical_form) > 1 || max_arity(logical_form) < 1)
			return false;
		break;
	case TREE_SEMANTICS_ARITY_BINARY:
		if (max_arity(logical_form) < 2)
			return false;
		break;
	default:
		break;
	}

	return ((logical_form.left_child == NULL || check_arity(*logical_form.left_child))
		 && (logical_form.right_child == NULL || check_arity(*logical_form.right_child)));
}

#endif


/**
 * Below are defined set operations on sets of logical forms.
 */

bool is_subset(const tree_semantics* first, const tree_semantics* second)
{
#if !defined(NDEBUG)
	if ((first != NULL && first->label == LABEL_EMPTY)
	 || (second != NULL && second->label == LABEL_EMPTY))
		fprintf(stderr, "is_subset WARNING: Arguments are empty.\n");
	if ((first != NULL && first->label == LABEL_EITHER && first->excluded_count < 2)
	 || (second != NULL && second->label == LABEL_EITHER && second->excluded_count < 2))
		fprintf(stderr, "is_subset WARNING: Invalid union-type tree_semantics structures.\n");
#endif

	if (first == NULL) {
		if (second == NULL) return true;
		else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD)
			return !is_excluded(*second, LABEL_EMPTY);
		else if (second->label == LABEL_EITHER)
			return is_excluded(*second, LABEL_EMPTY);
		else return false;
	} else if (second == NULL) {
		return false;
	} else if (second->label == LABEL_WILDCARD_TREE) {
		if (first->label == LABEL_WILDCARD || first->label == LABEL_WILDCARD_TREE) {
			return is_subset(
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count);
		} else if (first->label == LABEL_EITHER) {
			return has_intersection(
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
		} else return !is_excluded(*second, first->label);
	} else if (second->label == LABEL_WILDCARD) {
		if (first->label == LABEL_WILDCARD_TREE) {
			return is_subset(
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count)
				&& is_subset(&WILDCARD_TREE, second->left_child)
				&& is_subset(&WILDCARD_TREE, second->right_child);
		} else if (first->label == LABEL_WILDCARD) {
			if (!is_subset(
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count))
				return false;
		} else if (first->label == LABEL_EITHER) {
			if (!has_intersection(
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count))
				return false;
		} else if (is_excluded(*second, first->label)) {
			return false;
		}
	} else if (second->label == LABEL_EITHER) {
		if (first->label == LABEL_WILDCARD || first->label == LABEL_WILDCARD_TREE) {
			return false;
		} else if (first->label == LABEL_EITHER) {
			if (!is_subset(
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count))
				return false;
		} else if (!is_excluded(*second, first->label)) {
			return false;
		}
	} else {
		if (first->label == LABEL_WILDCARD || first->label == LABEL_WILDCARD_TREE || first->label == LABEL_EITHER)
			return false;
		else if (first->label != second->label)
			return false;
	}

	/* check the child nodes */
	return is_subset(first->left_child, second->left_child)
		&& is_subset(first->right_child, second->right_child);
}

bool subtract_node(
		tree_semantics& difference,
		const tree_semantics* first,
		const tree_semantics* second)
{
#if !defined(NDEBUG)
	if ((first != NULL && first->label == LABEL_EMPTY)
	 || (second != NULL && second->label == LABEL_EMPTY))
		fprintf(stderr, "subtract_node WARNING: Arguments are empty.\n");
	if ((first != NULL && first->label == LABEL_EITHER && first->excluded_count < 2)
	 || (second != NULL && second->label == LABEL_EITHER && second->excluded_count < 2))
		fprintf(stderr, "subtract_node WARNING: Invalid union-type tree_semantics structures.\n");
#endif

	difference.reference_count = 1;
	if (first == NULL) {
		if (second == NULL) {
			return false;
		} else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD) {
			if (!is_excluded(*second, LABEL_EMPTY))
				return false;
		} else if (second->label == LABEL_EITHER) {
			if (is_excluded(*second, LABEL_EMPTY))
				return false;
		}
		difference.label = LABEL_EMPTY;
		difference.excluded_count = 0;
		return true;
	} else if (first->label == LABEL_WILDCARD_TREE || first->label == LABEL_WILDCARD) {
		if (second == NULL) {
			difference.label = first->label;
			difference.excluded = (unsigned int*) malloc(sizeof(unsigned int) * (first->excluded_count + 1));
			difference.excluded_count = 0;
			unsigned int empty = LABEL_EMPTY;
			set_union(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count, &empty, 1);
		} else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD) {
			if (second->excluded_count == 0)
				return false;

			unsigned int diff_length = 0;
			unsigned int* diff = (unsigned int*) malloc(sizeof(unsigned int) * second->excluded_count);
			set_subtract(diff, diff_length,
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count);
			if (diff_length == 0) {
				free(diff);
				return false;
			} else if (diff_length == 1) {
				/* TODO: difference is copied from logical_form_set */
				difference.label = diff[0];
				difference.excluded_count = 0;
				free(diff);
			} else {
				difference.label = LABEL_EITHER;
				difference.excluded = diff;
				difference.excluded_count = diff_length;
			}
		} else if (second->label == LABEL_EITHER) {
			difference.label = first->label;
			difference.excluded = (unsigned int*) malloc(
					sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
			difference.excluded_count = 0;
			set_union(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
		} else {
			difference.label = LABEL_WILDCARD;
			difference.excluded = (unsigned int*) malloc(sizeof(unsigned int) * (first->excluded_count + 1));
			difference.excluded_count = 0;
			set_union(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count, &second->label, 1);
		}
	} else if (first->label == LABEL_EITHER) {
		difference.label = LABEL_EITHER;
		difference.excluded_count = 0;
		if (second == NULL) {
			difference.excluded = (unsigned int*) malloc(sizeof(unsigned int) * (first->excluded_count + 1));
			unsigned int empty = LABEL_EMPTY;
			set_subtract(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count, &empty, 1);
		} else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD) {
			difference.excluded = (unsigned int*) malloc(
					sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
			set_intersect(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
		} else if (second->label == LABEL_EITHER) {
			difference.excluded = (unsigned int*) malloc(
					sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
			set_subtract(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
		} else {
			difference.excluded = (unsigned int*) malloc(
					sizeof(unsigned int) * (first->excluded_count + second->excluded_count));
			set_subtract(difference.excluded, difference.excluded_count,
					first->excluded, first->excluded_count, &second->label, 1);
		}

		if (difference.excluded_count == 0) {
			free(difference.excluded);
			return false;
		} else if (difference.excluded_count == 1) {
			difference.label = difference.excluded[0];
			free(difference.excluded);
			difference.excluded_count = 0;
		}
	} else {
		difference.label = first->label;
		difference.excluded_count = 0;
		if (second == NULL) {
			/* do nothing */
		} else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD) {
			if (!is_excluded(*second, first->label)) return false;
		} else if (second->label == LABEL_EITHER) {
			if (is_excluded(*second, first->label)) return false;
		} else if (first->label == second->label) {
			return false;
		}
	}

	return true;
}

inline tree_semantics* left_child(const tree_semantics* logical_form_set) {
	if (logical_form_set == NULL) return NULL;
	else if (logical_form_set->label == LABEL_WILDCARD_TREE) return &WILDCARD_TREE;
	else return logical_form_set->left_child;
}

inline tree_semantics* right_child(const tree_semantics* logical_form_set) {
	if (logical_form_set == NULL) return NULL;
	else if (logical_form_set->label == LABEL_WILDCARD_TREE) return &WILDCARD_TREE;
	else return logical_form_set->right_child;
}

bool contains_wildcard_tree(const tree_semantics& logical_form) {
	if (logical_form.label == LABEL_WILDCARD_TREE) {
		if (logical_form.left_child != NULL || logical_form.right_child != NULL)
			fprintf(stderr, "THIS SHOULDNT HAPPEN\n");
		if (logical_form.excluded_count == 0)
			return &logical_form != &WILDCARD_TREE;
	}
	bool left = (logical_form.left_child == NULL) ? false : contains_wildcard_tree(*logical_form.left_child);
	if (left) return true;
	return (logical_form.right_child == NULL) ? false : contains_wildcard_tree(*logical_form.right_child);
}

template<bool First = true>
bool set_subtract(
		array<tree_semantics>& difference,
		const tree_semantics* first,
		const tree_semantics* second)
{
	if (first == NULL) {
		if (second == NULL)
			return true;
		else if ((second->label == LABEL_WILDCARD || second->label == LABEL_WILDCARD_TREE) && !is_excluded(*second, LABEL_EMPTY))
			return true;
	} else if (first->label == LABEL_WILDCARD_TREE) {
		if (second != NULL && second->label == LABEL_WILDCARD_TREE && second->excluded_count == 0)
			return true;
	}

	if (!difference.ensure_capacity(difference.length + 3))
		return false;

	tree_semantics* first_left = left_child(first);
	tree_semantics* first_right = right_child(first);
	tree_semantics* second_left = left_child(second);
	tree_semantics* second_right = right_child(second);

	/* first compute the set difference of the labels */
	if (subtract_node(difference[difference.length], first, second)) {
		if (First && difference[difference.length].label == LABEL_EMPTY) {
			if (difference[difference.length].excluded_count > 0)
				free(difference[difference.length].excluded);
		} else {
			/* the difference is not empty */
			difference[difference.length].left_child = first_left;
			difference[difference.length].right_child = first_right;
			if (first_left != NULL) first_left->reference_count++;
			if (first_right != NULL) first_right->reference_count++;
			difference[difference.length].recompute_hash();
			difference.length++;
		}
	}

	tree_semantics intersection;
	if (intersect_node<false>(intersection, first, second)
	 && intersection.label != LABEL_EMPTY)
	{
		/* the intersection is not empty */

		/* compute (first->left \ second->left) x (first->right intersect second->right) */
		tree_semantics* right_intersection = (tree_semantics*) malloc(sizeof(tree_semantics));
		if (!intersect_node<true>(*right_intersection, first_right, second_right)) {
			free(right_intersection);
			right_intersection = NULL;
		} else if (right_intersection->label == LABEL_EMPTY) {
			free(*right_intersection);
			free(right_intersection);
			right_intersection = NULL;
		} else if (right_intersection->label == LABEL_WILDCARD_TREE && right_intersection->excluded_count == 0) {
			free(*right_intersection);
			free(right_intersection);
			right_intersection = &WILDCARD_TREE;
			right_intersection->reference_count++;
		} else {
			right_intersection->recompute_hash();
		}

		array<tree_semantics> children_difference = array<tree_semantics>(8);
		if (!set_subtract<false>(children_difference, first_left, second_left)
		 || !difference.ensure_capacity(difference.length + children_difference.length))
			return false;
		for (tree_semantics& child_diff : children_difference) {
			if (child_diff.label == LABEL_EMPTY) {
				free(child_diff);
				intersection.left_child = NULL;
			} else {
				intersection.left_child = (tree_semantics*) malloc(sizeof(tree_semantics));
				move(child_diff, *intersection.left_child);
				intersection.left_child->reference_count = 0;
			}
			intersection.right_child = right_intersection;
			intersection.recompute_hash();

			difference[difference.length] = intersection;
			difference.length++;
		}
		if (right_intersection != NULL) {
			free(*right_intersection);
			if (right_intersection->reference_count == 0)
				free(right_intersection);
		}

		/* compute first->left x (first->right \ second->right) */
		children_difference.clear();
		if (!set_subtract<false>(children_difference, first_right, second_right)
		 || !difference.ensure_capacity(difference.length + children_difference.length))
			return false;
		for (tree_semantics& child_diff : children_difference) {
			intersection.left_child = first_left;
			if (child_diff.label == LABEL_EMPTY) {
				free(child_diff);
				intersection.right_child = NULL;
			} else {
				intersection.right_child = (tree_semantics*) malloc(sizeof(tree_semantics));
				move(child_diff, *intersection.right_child);
				intersection.right_child->reference_count = 0;
			}
			intersection.recompute_hash();

			difference[difference.length] = intersection;
			difference.length++;
		}
	}

	/* avoid double free of child nodes */
	intersection.left_child = NULL;
	intersection.right_child = NULL;
	return true;
}

inline void union_children(tree_semantics& output,
		const tree_semantics& first, const tree_semantics& second)
{
	/* intersect the children */
	set_union(output.left_child, first.left_child, second.left_child);
	set_union(output.right_child, first.right_child, second.right_child);
}

/* TODO: this is wrong; the union can be three logical form structures */
void set_union(tree_semantics*& dst, const tree_semantics* first, const tree_semantics* second)
{
#if !defined(NDEBUG)
	if ((first != NULL && first->label == LABEL_EITHER && first->excluded_count < 2)
	 || (second != NULL && second->label == LABEL_EITHER && second->excluded_count < 2))
		fprintf(stderr, "intersect_node WARNING: Invalid union-type tree_semantics structures.\n");
#endif

	/* compute the union of the labels */
	if (first == NULL || first->label == LABEL_EMPTY) {
		if (second == NULL || second->label == LABEL_EMPTY) {
			dst = NULL;
		} else if (second->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD) {
			dst = copy(*second);
			unsigned int empty = LABEL_EMPTY;
			set_subtract(dst->excluded, dst->excluded_count, &empty, 1);
			dst->recompute_hash();
		} else if (second->label == LABEL_EITHER) {
			dst = copy(*second);
			dst->exclude(LABEL_EMPTY);
			dst->recompute_hash();
		} else {
			dst = new_tree_without_excluded(LABEL_EITHER, second->left_child, second->right_child);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * 2);
			dst->excluded[0] = second->label; dst->excluded[1] = LABEL_EMPTY;
			dst->excluded_count = 2;
			dst->recompute_hash();
		}
		return;
	} else if (second == NULL || second->label == LABEL_EMPTY) {
		if (first->label == LABEL_WILDCARD_TREE || first->label == LABEL_WILDCARD) {
			dst = copy(*first);
			unsigned int empty = LABEL_EMPTY;
			set_subtract(dst->excluded, dst->excluded_count, &empty, 1);
			dst->recompute_hash();
		} else if (first->label == LABEL_EITHER) {
			dst = copy(*first);
			dst->exclude(LABEL_EMPTY);
			dst->recompute_hash();
		} else {
			dst = new_tree_without_excluded(LABEL_EITHER, first->left_child, first->right_child);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * 2);
			dst->excluded[0] = first->label; dst->excluded[1] = LABEL_EMPTY;
			dst->excluded_count = 2;
			dst->recompute_hash();
		}
		return;
	} else if (first->label == LABEL_WILDCARD_TREE || second->label == LABEL_WILDCARD_TREE) {
		dst = &WILDCARD_TREE;
		dst->reference_count++;
		return;
	} else if (first->label == LABEL_WILDCARD) {
		if (second->label == LABEL_WILDCARD) {
			dst = new_empty_tree(LABEL_WILDCARD);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int)
					* min(first->excluded_count, second->excluded_count));
			dst->excluded_count = 0;
			set_intersect(dst->excluded, dst->excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		} else if (second->label == LABEL_EITHER) {
			dst = new_empty_tree(LABEL_WILDCARD);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * first->excluded_count);
			dst->excluded_count = 0;
			set_subtract(dst->excluded, dst->excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		} else {
			dst = new_empty_tree(LABEL_WILDCARD);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * first->excluded_count);
			dst->excluded_count = 0;
			set_subtract(dst->excluded, dst->excluded_count,
					first->excluded, first->excluded_count, &second->label, 1);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		}
	} else if (second->label == LABEL_WILDCARD) {
		if (first->label == LABEL_EITHER) {
			dst = new_empty_tree(LABEL_WILDCARD);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * second->excluded_count);
			dst->excluded_count = 0;
			set_subtract(dst->excluded, dst->excluded_count,
					second->excluded, second->excluded_count,
					first->excluded, first->excluded_count);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		} else {
			dst = new_empty_tree(LABEL_WILDCARD);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * second->excluded_count);
			dst->excluded_count = 0;
			set_subtract(dst->excluded, dst->excluded_count,
					second->excluded, second->excluded_count, &first->label, 1);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		}
	} else if (first->label == LABEL_EITHER) {
		if (second->label == LABEL_EITHER) {
			dst = new_empty_tree(LABEL_EITHER);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int)
					* (first->excluded_count + second->excluded_count));
			dst->excluded_count = 0;
			set_union(dst->excluded, dst->excluded_count,
					first->excluded, first->excluded_count,
					second->excluded, second->excluded_count);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		} else {
			dst = new_empty_tree(LABEL_EITHER);
			dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * (first->excluded_count + 1));
			dst->excluded_count = 0;
			set_union(dst->excluded, dst->excluded_count,
					first->excluded, first->excluded_count, &second->label, 1);
			if (dst->excluded_count == 0)
				free(dst->excluded);
		}
	} else if (second->label == LABEL_EITHER) {
		dst = new_empty_tree(LABEL_EITHER);
		dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * (second->excluded_count + 1));
		dst->excluded_count = 0;
		set_union(dst->excluded, dst->excluded_count,
				second->excluded, second->excluded_count, &first->label, 1);
		if (dst->excluded_count == 0)
			free(dst->excluded);
	} else if (first->label < second->label) {
		dst = new_empty_tree(LABEL_EITHER);
		dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * 2);
		dst->excluded[0] = first->label; dst->excluded[1] = second->label;
		dst->excluded_count = 2;
	} else if (first->label > second->label) {
		dst = new_empty_tree(LABEL_EITHER);
		dst->excluded = (unsigned int*) malloc(sizeof(unsigned int) * 2);
		dst->excluded[0] = second->label; dst->excluded[1] = first->label;
		dst->excluded_count = 2;
	} else {
		dst = new_empty_tree(first->label);
		dst->excluded_count = 0;
	}

	union_children(*dst, *first, *second);

	if (dst->label == LABEL_WILDCARD && dst->left_child == &WILDCARD_TREE && dst->right_child == &WILDCARD_TREE) {
		if (dst->reference_count == 0) {
			free(*dst);
			if (dst->reference_count == 0)
				free(dst);
			dst = &WILDCARD_TREE;
			dst->reference_count++;
		} else {
			dst->label = LABEL_WILDCARD_TREE;
			dst->left_child = NULL;
			dst->right_child = NULL;
			free(WILDCARD_TREE);
			free(WILDCARD_TREE);
			dst->recompute_hash();
		}
	} else if (dst->label == LABEL_WILDCARD_TREE && dst->reference_count == 0) {
		free(*dst);
		if (dst->reference_count == 0)
			free(dst);
		dst = &WILDCARD_TREE;
		dst->reference_count++;
	} else {
		dst->recompute_hash();
	}
}

inline void set_union(tree_semantics& dst, const tree_semantics* first, const tree_semantics* second) {
	tree_semantics* output;
	set_union(output, first, second);

	if (output == NULL) {
		dst = EMPTY_TREE;
	} else {
		dst = *output;
		free(*output);
		if (output->reference_count == 0)
			free(output);
	}
}

void remove_children(tree_semantics& logical_form) {
	if (logical_form.left_child != NULL) {
		free(*logical_form.left_child);
		if (logical_form.left_child->reference_count == 0)
			free(logical_form.left_child);
		logical_form.left_child = &WILDCARD_TREE;
		logical_form.left_child->reference_count++;
	}
	if (logical_form.right_child != NULL) {
		free(*logical_form.right_child);
		if (logical_form.right_child->reference_count == 0)
			free(logical_form.right_child);
		logical_form.right_child = &WILDCARD_TREE;
		logical_form.right_child->reference_count++;
	}
}

tree_semantics prune(const tree_semantics& src, unsigned int depth)
{
	tree_semantics root = tree_semantics(src.label);

	if (src.left_child == NULL) {
		root.left_child = NULL;
	} else if (depth == 1) {
		root.left_child = copy(*src.left_child);
		remove_children(*root.left_child);
	} else {
		tree_semantics new_left = prune(*src.left_child, depth - 1);
		root.left_child = copy(new_left);
	}

	if (src.right_child == NULL) {
		root.right_child = NULL;
	} else if (depth == 1) {
		root.right_child = copy(*src.right_child);
		remove_children(*root.right_child);
	} else {
		tree_semantics new_right = prune(*src.right_child, depth - 1);
		root.right_child = copy(new_right);
	}
	return root;
}


/**
 * A trie-like data structure for reasoning over sets of tree_semantics structures.
 */

void prefix_walk(const tree_semantics& logical_form, array<const tree_semantics*>& nodes)
{
	array<const tree_semantics*> stack = array<const tree_semantics*>(8);
	stack.add(&logical_form);
	while (stack.length > 0)
	{
		const tree_semantics* node = stack.pop();
		if (node == NULL) {
			nodes.add(NULL);
			continue;
		}
		if (node->label != LABEL_WILDCARD_TREE || node->excluded_count > 0)
			nodes.add(node);
		if (node->label == LABEL_WILDCARD_TREE)
			break;

		stack.add(node->right_child);
		stack.add(node->left_child);
	}
}

//template<typename V>
//struct tree_semantics_trie {
//	array_map<unsigned int, tree_semantics_trie<V>> children;
//	tree_semantics_trie<V>* wildcard;
//
//	V* node_value;
//	bool expanded;
//
//	template<typename T>
//	struct linked_list_node {
//		T value;
//		linked_list_node<T>* next;
//	};
//
//	tree_semantics* copy_tree(const tree_semantics& tree)
//	{
//		if (tree.label == LABEL_WILDCARD_TREE && tree.excluded_count == 0) {
//			WILDCARD_TREE.reference_count++;
//			return &WILDCARD_TREE;
//		}
//
//		tree_semantics* copy = (tree_semantics*) malloc(sizeof(tree_semantics));
//		if (copy == NULL) {
//			fprintf(stderr, "tree_semantics_rule.copy_tree ERROR: Out of memory.\n");
//			return NULL;
//		}
//
//		copy->label = tree.label;
//		copy->excluded_count = tree.excluded_count;
//		if (tree.excluded_count > 0) {
//			copy->excluded = (unsigned int*) malloc(sizeof(unsigned int) * tree.excluded_count);
//			memcpy(copy->excluded, tree.excluded, sizeof(unsigned int) * tree.excluded_count);
//		}
//		copy->left_child = (tree.left_child == NULL) ? NULL : copy_tree(*tree.left_child);
//		copy->right_child = (tree.right_child == NULL) ? NULL : copy_tree(*tree.right_child);
//		copy->reference_count = 1;
//		return copy;
//	}
//
//	tree_semantics* copy_tree(const tree_semantics& tree, linked_list_node<tree_semantics*>* stack)
//	{
//		if (stack == NULL) return copy_tree(tree);
//
//		/* the node at the end of the stack is the root */
//		while (stack->next != NULL) stack = stack->next;
//		return copy_tree(*stack->value);
//	}
//
//	enum expansion_type {
//		EXPAND_UNEXPANDED,
//		EXPAND_DESCENDANTS,
//		EXPAND_NONE
//	};
//
//	template<typename Function, expansion_type Expand, bool Equal = true>
//	void map_descendants(tree_semantics*& tree, linked_list_node<tree_semantics*>* stack, Function function)
//	{
//		tree_semantics* logical_form_set = copy_tree(*tree, stack);
//		/* we only expand this node if it's a leaf */
//		bool to_expand = (Expand == EXPAND_UNEXPANDED) && !expanded && children.size == 0 && wildcard == NULL;
//		function(*node_value, *logical_form_set, Equal ? SET_EQUAL : SET_SUBSET, to_expand);
//		core::free(*logical_form_set);
//		if (logical_form_set->reference_count == 0)
//			core::free(logical_form_set);
//		if (Expand == EXPAND_DESCENDANTS || to_expand)
//			expanded = true;
//
//		tree = (tree_semantics*) malloc(sizeof(tree_semantics));
//		tree->reference_count = 1;
//		tree->excluded_count = 0;
//		tree->left_child = &WILDCARD_TREE;
//		tree->right_child = &WILDCARD_TREE;
//		WILDCARD_TREE.reference_count += 2;
//		linked_list_node<tree_semantics*> new_stack = { tree, stack };
//
//		for (const auto& entry : children) {
//			if (entry.key == LABEL_EMPTY) {
//				if (stack != NULL) {
//					tree_semantics* old_tree = tree;
//					tree = NULL;
//					linked_list_node<tree_semantics*>* new_stack = stack;
//					tree_semantics*& next = get_next_node(tree, new_stack);
//					if (to_expand)
//						entry.value.template map_descendants<Function, EXPAND_DESCENDANTS, false>(next, new_stack, function);
//					else entry.value.template map_descendants<Function, Expand, false>(next, new_stack, function);
//					tree = old_tree;
//				}
//			} else {
//				tree->label = entry.key;
//				if (to_expand)
//					entry.value.template map_descendants<Function, EXPAND_DESCENDANTS, false>(tree->left_child, &new_stack, function);
//				else entry.value.template map_descendants<Function, Expand, false>(tree->left_child, &new_stack, function);
//			}
//		}
//
//		if (Expand == EXPAND_UNEXPANDED && wildcard == NULL && children.size > 0) {
//			wildcard = (tree_semantics_trie<V>*) malloc(sizeof(tree_semantics_trie<V>));
//			if (wildcard == NULL || !init(*wildcard))
//				exit(EXIT_FAILURE);
//		} if (wildcard != NULL) {
//			tree->label = LABEL_WILDCARD;
//			if (children.size > 0) {
//				tree->excluded = (unsigned int*) malloc(sizeof(unsigned int) * children.size);
//				memcpy(tree->excluded, children.keys, children.size * sizeof(unsigned int));
//			}
//			tree->excluded_count = children.size;
//			if (to_expand)
//				wildcard->map_descendants<Function, EXPAND_DESCENDANTS, false>(tree->left_child, &new_stack, function);
//			else wildcard->map_descendants<Function, Expand, false>(tree->left_child, &new_stack, function);
//		}
//
//		core::free(*tree);
//		if (tree->reference_count == 0)
//			core::free(tree);
//		tree = &WILDCARD_TREE;
//	}
//
//	tree_semantics*& get_next_node(tree_semantics*& tree, linked_list_node<tree_semantics*>*& stack)
//	{
//		if (stack == NULL) return tree; /* the stack is empty, so this is never used */
//		linked_list_node<tree_semantics*>& current = *stack;
//		if (&current.value->right_child != &tree)
//			return current.value->right_child;
//		stack = stack->next;
//		while (stack != NULL) {
//			tree_semantics* old_parent = current.value;
//			current = *stack;
//			if (current.value->right_child != old_parent)
//				return current.value->right_child;
//			stack = stack->next;
//		}
//
//		/* the stack is empty, so return the root*/
//		return current.value;
//	}
//
//	template<typename Function>
//	void expand(
//			tree_semantics*& tree, linked_list_node<tree_semantics*>* stack,
//			const tree_semantics** nodes, unsigned int node_count, Function function)
//	{
//		if (node_count == 0 || expanded) {
//			/* we found the node that maps to the logical form set */
//			map_descendants<Function, EXPAND_UNEXPANDED>(tree, stack, function);
//			return;
//		} else {
//			bool to_expand = false;
//			tree_semantics* logical_form_set = copy_tree(*tree, stack);
//			function(*node_value, *logical_form_set, SET_SUPERSET, to_expand);
//			core::free(*logical_form_set);
//			if (logical_form_set->reference_count == 0)
//				core::free(logical_form_set);
//		}
//
//		const tree_semantics* current = *nodes;
//		if (current == NULL) {
//			/* tree was initialized to WILDCARD_TREE, so decrement its reference counter */
//			WILDCARD_TREE.reference_count--;
//			tree = NULL;
//			linked_list_node<tree_semantics*>* new_stack = stack;
//			tree_semantics*& next = get_next_node(tree, new_stack);
//
//			unsigned int index = reverse_strict_linear_search(children.keys, LABEL_EMPTY, 0, children.size);
//			if (index > 0 && children.keys[index - 1] == LABEL_EMPTY) {
//				children.values[index - 1].expand(next, new_stack, nodes + 1, node_count - 1, function);
//			} else {
//				/* the child node does not exist, so create it */
//				create_child(index, LABEL_EMPTY);
//				children.values[index].expand(next, new_stack, nodes + 1, node_count - 1, function);
//			}
//		} else if (current->label == LABEL_WILDCARD || current->label == LABEL_WILDCARD_TREE) {
//			/* this is some wildcard label */
//			/* TODO: handle LABEL_WILDCARD_TREE more appropriately */
//			tree = (tree_semantics*) malloc(sizeof(tree_semantics));
//			tree->reference_count = 1;
//			tree->excluded_count = 0;
//			tree->left_child = &WILDCARD_TREE;
//			tree->right_child = &WILDCARD_TREE;
//			WILDCARD_TREE.reference_count += 2;
//			linked_list_node<tree_semantics*> new_stack = {tree, stack};
//
//			/* expand nodes that aren't excluded, and
//			   create nodes for each excluded label, but
//			   don't expand them */
//			unsigned int new_size = 0;
//			unsigned int new_capacity = 1 << (core::log2(current->excluded_count + children.size) + 2);
//			unsigned int* new_keys = (unsigned int*) malloc(sizeof(unsigned int) * new_capacity);
//			tree_semantics_trie<V>* new_values = (tree_semantics_trie<V>*)
//					malloc(sizeof(tree_semantics_trie<V>) * new_capacity);
//			auto union_both = [&](unsigned int label, unsigned int i, unsigned int j) {
//				new_keys[new_size] = label;
//				core::move(children.values[j], new_values[new_size]);
//				new_size++;
//			};
//			auto union_first = [&](unsigned int label, unsigned int i, unsigned int j) {
//				new_keys[new_size] = label;
//				create_child(new_values[new_size]);
//				new_size++;
//			};
//			auto union_second = [&](unsigned int label, unsigned int i, unsigned int j) {
//				new_keys[new_size] = label;
//				core::move(children.values[j], new_values[new_size]);
//				if (label == LABEL_EMPTY) {
//					if (stack != NULL) {
//						tree_semantics* old_tree = tree;
//						tree = NULL;
//						linked_list_node<tree_semantics*>* new_stack = stack;
//						tree_semantics*& next = get_next_node(tree, new_stack);
//						new_values[new_size].expand(next, new_stack, nodes + 1, node_count - 1, function);
//						tree = old_tree;
//					}
//				} else {
//					tree->label = label;
//					new_values[new_size].expand(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//				}
//				new_size++;
//			};
//			set_union(union_both, union_first, union_second,
//					current->excluded, current->excluded_count,
//					children.keys, children.size);
//			core::free(children.keys);
//			core::free(children.values);
//			children.keys = new_keys;
//			children.values = new_values;
//			children.capacity = new_capacity;
//			children.size = new_size;
//
//			/* expand the wildcard node after creating the new nodes */
//			if (wildcard == NULL) {
//				wildcard = (tree_semantics_trie<V>*) malloc(sizeof(tree_semantics_trie<V>));
//				if (wildcard == NULL || !init(*wildcard))
//					exit(EXIT_FAILURE);
//			}
//			tree->label = LABEL_WILDCARD;
//			if (children.size > 0) {
//				tree->excluded = (unsigned int*) malloc(sizeof(unsigned int) * children.size);
//				memcpy(tree->excluded, children.keys, children.size * sizeof(unsigned int));
//			}
//			tree->excluded_count = children.size;
//
//			wildcard->expand(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//
//			core::free(*tree);
//			if (tree->reference_count == 0)
//				core::free(tree);
//			tree = &WILDCARD_TREE;
//		} else {
//			tree = new_empty_tree(current->label);
//			tree->excluded_count = 0;
//			tree->left_child = &WILDCARD_TREE;
//			tree->right_child = &WILDCARD_TREE;
//			WILDCARD_TREE.reference_count += 2;
//			linked_list_node<tree_semantics*> new_stack = {tree, stack};
//
//			unsigned int index = reverse_strict_linear_search(children.keys, current->label, 0, children.size);
//			if (index > 0 && children.keys[index - 1] == current->label) {
//				children.values[index - 1].expand(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//			} else {
//				/* the child node does not exist, so create it */
//				create_child(index, current->label);
//				children.values[index].expand(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//			}
//
//			core::free(*tree);
//			if (tree->reference_count == 0)
//				core::free(tree);
//			tree = &WILDCARD_TREE;
//		}
//	}
//
//	template<typename Function>
//	inline bool expand(const tree_semantics& logical_form_set, Function function)
//	{
//		array<const tree_semantics*> walk = array<const tree_semantics*>(8);
//		prefix_walk(logical_form_set, walk);
//
//		tree_semantics* tree = &WILDCARD_TREE;
//		WILDCARD_TREE.reference_count++;
//		expand(tree, NULL, walk.data, walk.length, function);
//		return true;
//	}
//
//	template<typename Function>
//	void map(tree_semantics*& tree, linked_list_node<tree_semantics*>* stack,
//			const tree_semantics** nodes, unsigned int node_count, Function function)
//	{
//		if (node_count == 0) {
//			/* we found the node that maps to the logical form set */
//			map_descendants<Function, EXPAND_UNEXPANDED>(tree, stack, function);
//			return;
//		} else {
//			bool complete = children.size == 0 && wildcard == NULL;
//			tree_semantics* logical_form_set = copy_tree(*tree, stack);
//			function(*node_value, *logical_form_set, SET_SUPERSET, complete);
//			core::free(*logical_form_set);
//			if (logical_form_set->reference_count == 0)
//				core::free(logical_form_set);
//		}
//
//		const tree_semantics* current = *nodes;
//		if (current == NULL) {
//			/* tree was initialized to WILDCARD_TREE, so decrement its reference counter */
//			WILDCARD_TREE.reference_count--;
//			tree = NULL;
//			linked_list_node<tree_semantics*>* new_stack = stack;
//			tree_semantics*& next = get_next_node(tree, new_stack);
//
//			unsigned int index = reverse_strict_linear_search(children.keys, LABEL_EMPTY, 0, children.size);
//			if (index > 0 && children.keys[index - 1] == LABEL_EMPTY)
//				children.values[index - 1].map(next, new_stack, nodes + 1, node_count - 1, function);
//			else if (wildcard != NULL)
//				wildcard->map(next, new_stack, nodes + 1, node_count - 1, function);
//		} else if (current->label == LABEL_WILDCARD || current->label == LABEL_WILDCARD_TREE) {
//			/* this is some wildcard label */
//			/* TODO: handle LABEL_WILDCARD_TREE more appropriately */
//			tree = (tree_semantics*) malloc(sizeof(tree_semantics));
//			tree->reference_count = 1;
//			tree->excluded_count = 0;
//			tree->left_child = &WILDCARD_TREE;
//			tree->right_child = &WILDCARD_TREE;
//			WILDCARD_TREE.reference_count += 2;
//			linked_list_node<tree_semantics*> new_stack = {tree, stack};
//
//			/* recurse into nodes that aren't excluded */
//			auto do_subtract = [&](unsigned int i) {
//				if (children.keys[i] == LABEL_EMPTY) {
//					if (stack != NULL) {
//						tree_semantics* old_tree = tree;
//						tree = NULL;
//						linked_list_node<tree_semantics*>* new_stack = stack;
//						tree_semantics*& next = get_next_node(tree, new_stack);
//						children.values[i].map(next, new_stack, nodes + 1, node_count - 1, function);
//						tree = old_tree;
//					}
//				} else {
//					tree->label = children.keys[i];
//					children.values[i].map(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//				}
//			};
//			set_subtract(do_subtract, children.keys, children.size,
//					current->excluded, current->excluded_count);
//
//			/* expand the wildcard node after creating the new nodes */
//			if (wildcard != NULL) {
//				tree->label = LABEL_WILDCARD;
//				tree->excluded_count = 0;
//				if (children.size + current->excluded_count > 0) {
//					tree->excluded = (unsigned int*) malloc(sizeof(unsigned int) * (children.size + current->excluded_count));
//					set_union(tree->excluded, tree->excluded_count,
//							children.keys, children.size,
//							current->excluded, current->excluded_count);
//				}
//				wildcard->map(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//			}
//
//			core::free(*tree);
//			if (tree->reference_count == 0)
//				core::free(tree);
//			tree = &WILDCARD_TREE;
//		} else {
//			tree = new_empty_tree(current->label);
//			tree->excluded_count = 0;
//			tree->left_child = &WILDCARD_TREE;
//			tree->right_child = &WILDCARD_TREE;
//			WILDCARD_TREE.reference_count += 2;
//			linked_list_node<tree_semantics*> new_stack = {tree, stack};
//
//			unsigned int index = reverse_strict_linear_search(children.keys, current->label, 0, children.size);
//			if (index > 0 && children.keys[index - 1] == current->label)
//				children.values[index - 1].map(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//			else if (wildcard != NULL)
//				wildcard->map(tree->left_child, &new_stack, nodes + 1, node_count - 1, function);
//
//			core::free(*tree);
//			if (tree->reference_count == 0)
//				core::free(tree);
//			tree = &WILDCARD_TREE;
//		}
//	}
//
//	template<typename Function>
//	inline bool map(const tree_semantics& logical_form_set, Function function)
//	{
//		array<const tree_semantics*> walk = array<const tree_semantics*>(8);
//		prefix_walk(logical_form_set, walk);
//
//		tree_semantics* tree = &WILDCARD_TREE;
//		WILDCARD_TREE.reference_count++;
//		map(tree, NULL, walk.data, walk.length, function);
//		return true;
//	}
//
//	template<typename Function>
//	inline void iterate(Function function) const
//	{
//		array<const tree_semantics_trie<V>*> stack = array<const tree_semantics_trie<V>*>(256);
//		stack.add(this);
//		while (stack.length > 0) {
//			const tree_semantics_trie<V>& node = *stack.pop();
//			if (!function(*node.node_value))
//				return;
//
//			for (const auto& child : node.children)
//				stack.add(&child.value);
//			if (node.wildcard != NULL) stack.add(node.wildcard);
//		}
//	}
//
//	void create_child(unsigned int index, unsigned int label) {
//		if (!children.ensure_capacity(children.size + 1)) {
//			fprintf(stderr, "tree_semantics_trie.create_child ERROR: Out of memory.\n");
//			exit(EXIT_FAILURE);
//		}
//		shift_right(children.keys, children.size, index);
//		shift_right(children.values, children.size, index);
//		children.keys[index] = label;
//		create_child(children.values[index]);
//		children.size++;
//	}
//
//	inline void create_child(tree_semantics_trie<V>& new_node) {
//		if (wildcard == NULL) {
//			if (!init(new_node))
//				exit(EXIT_FAILURE);
//		} else if (!copy(*wildcard, new_node)) {
//			/* TODO: make this robust to memory errors */
//			exit(EXIT_FAILURE);
//		}
//	}
//
//	static bool copy(const tree_semantics_trie<V>& src, tree_semantics_trie<V>& dst)
//	{
//		/* first copy the wildcard node */
//		if (src.wildcard == NULL) {
//			dst.wildcard = NULL;
//		} else {
//			dst.wildcard = (tree_semantics_trie<V>*) malloc(sizeof(tree_semantics_trie<V>));
//			if (!copy(*src.wildcard, *dst.wildcard)) {
//				core::free(dst.wildcard);
//				return false;
//			}
//		}
//
//		/* initialize the cell value */
//		dst.node_value = (V*) malloc(sizeof(V));
//		if (dst.node_value == NULL) {
//			fprintf(stderr, "tree_semantics_trie.copy ERROR: Out of memory.\n");
//			free(*dst.wildcard); core::free(dst.wildcard);
//			return false;
//		} else if (!V::copy(*src.node_value, *dst.node_value)) {
//			fprintf(stderr, "tree_semantics_trie.copy ERROR: "
//					"Unable to initialize generic data field.\n");
//			free(*dst.wildcard); core::free(dst.wildcard);
//			core::free(dst.node_value);
//			return false;
//		}
//
//		/* copy the remaining children */
//		if (!array_map_init(dst.children, src.children.capacity)) {
//			fprintf(stderr, "tree_semantics_trie.copy ERROR: "
//					"Unable to initialize children array_map.\n");
//			free(*dst.wildcard); core::free(dst.wildcard);
//			core::free(*dst.node_value); core::free(dst.node_value);
//			return false;
//		}
//		for (unsigned int i = 0; i < src.children.size; i++) {
//			dst.children.keys[i] = src.children.keys[i];
//			if (!copy(src.children.values[i], dst.children.values[i])) {
//				free(dst); return false;
//			}
//			dst.children.size++;
//		}
//		dst.expanded = src.expanded;
//		return true;
//	}
//
//	static void move(const tree_semantics_trie<V>& src, tree_semantics_trie<V>& dst) {
//		core::move(src.children, dst.children);
//		dst.wildcard = src.wildcard;
//		dst.node_value = src.node_value;
//		dst.expanded = src.expanded;
//	}
//
//	static void free(tree_semantics_trie<V>& node) {
//		for (auto entry : node.children)
//			core::free(entry.value);
//		core::free(node.children);
//		if (node.wildcard != NULL) {
//			core::free(*node.wildcard);
//			core::free(node.wildcard);
//		}
//		core::free(*node.node_value);
//		core::free(node.node_value);
//	}
//
//	template<typename A> friend bool init(tree_semantics_trie<A>&);
//};
//
//template<typename V>
//inline bool init(tree_semantics_trie<V>& node)
//{
//	node.wildcard = NULL;
//	if (!array_map_init(node.children, 8)) {
//		fprintf(stderr, "init ERROR: Unable to initialize array_map in tree_semantics_trie.\n");
//		return false;
//	}
//
//	node.node_value = (V*) malloc(sizeof(V));
//	if (node.node_value == NULL) {
//		fprintf(stderr, "init ERROR: Insufficient memory for generic data field in tree_semantics_trie.\n");
//		free(node.children);
//		return false;
//	} else if (!init(*node.node_value)) {
//		fprintf(stderr, "init ERROR: Unable to initialize generic data field in tree_semantics_trie.\n");
//		free(node.children); free(node.node_value);
//		return false;
//	}
//	node.expanded = false;
//	return true;
//}


#endif /* TREE_SEMANTICS_H_ */
