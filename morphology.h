/**
 * morphology.h - Implements a simple model and parser for noun and verb morphology.
 *
 *  Created on: May 5, 2017
 *      Author: asaparov
 */

#ifndef MORPHOLOGY_H_
#define MORPHOLOGY_H_

#include <core/array.h>
#include <core/lex.h>

using namespace core;

/* TODO: add more entries for a broader set of languages */
enum grammatical_number {
	NUMBER_SINGULAR = 1,
	NUMBER_PLURAL = 2,
	NUMBER_UNCOUNTABLE = 3,
	NUMBER_NON_SINGULAR = 4,	/* plural or uncountable */
	NUMBER_NON_PLURAL = 5,		/* singular or uncountable */
	NUMBER_ALL = 6,				/* singular, plural, or uncountable (not set-valued) */
	NUMBER_NONE = 7,

	/* set-valued numbers */
	NUMBER_ANY = 8
};

constexpr unsigned int grammatical_number_count = 8;

/* TODO: add more entries for a broader set of languages */
enum inflection {
	INFLECTION_PAST_PARTICIPLE = 1,
	INFLECTION_PRESENT_PARTICIPLE = 2,
	INFLECTION_INFINITIVE = 3,
	INFLECTION_OTHER_VERB = 4,

	INFLECTION_NOUN = 5,
	INFLECTION_ADJECTIVE = 6,
	INFLECTION_COMPARATIVE = 7,
	INFLECTION_SUPERLATIVE = 8,

	INFLECTION_NONE = 9,

	INFLECTION_ANY = 10
};

enum part_of_speech {
	POS_NOUN = 1,
	POS_VERB = 2,
	POS_ADJECTIVE = 3,
	POS_OTHER = 4
};

struct token {
	unsigned int id;
	grammatical_number number;
	inflection inf;

	inline part_of_speech get_part_of_speech() const {
		switch (inf) {
		case INFLECTION_PAST_PARTICIPLE:
		case INFLECTION_PRESENT_PARTICIPLE:
		case INFLECTION_INFINITIVE:
		case INFLECTION_OTHER_VERB:
			return POS_VERB;
		case INFLECTION_NOUN:
			return POS_NOUN;
		case INFLECTION_ADJECTIVE:
		case INFLECTION_COMPARATIVE:
		case INFLECTION_SUPERLATIVE:
			return POS_ADJECTIVE;
		case INFLECTION_ANY:
		case INFLECTION_NONE:
			return POS_OTHER;
		}
		fprintf(stderr, "token.part_of_speech ERROR: Unrecognized inflection.\n");
		exit(EXIT_FAILURE);
	}

	static inline unsigned int hash(const token& tok) {
		return default_hash(tok);
	}

	static inline bool is_empty(const token& tok) {
		return tok.id == 0;
	}

	static inline void move(const token& src, token& dst) {
		dst.id = src.id;
		dst.number = src.number;
		dst.inf = src.inf;
	}
};

inline bool operator == (const token& first, const token& second) {
	return first.id == second.id && first.number == second.number && first.inf == second.inf;
}

inline bool operator != (const token& first, const token& second) {
	return first.id != second.id || first.number != second.number || first.inf != second.inf;
}

inline bool intersect(grammatical_number& intersection,
		grammatical_number first, grammatical_number second)
{
	if (first == NUMBER_ANY || first == NUMBER_ALL) {
		intersection = second;
	} else if (second == NUMBER_ANY || second == NUMBER_ALL) {
		intersection = first;
	} else if (first == NUMBER_NON_SINGULAR) {
		if (second == NUMBER_SINGULAR) {
			return false;
		} else {
			intersection = second;
		}
	} else if (second == NUMBER_NON_SINGULAR) {
		if (first == NUMBER_SINGULAR) {
			return false;
		} else {
			intersection = first;
		}
	} else if (first == second) {
		intersection = first;
	} else {
		return false;
	}
	return true;
}

inline bool has_intersection(grammatical_number first, grammatical_number second)
{
	if (first == NUMBER_ANY || second == NUMBER_ANY || first == NUMBER_ALL || second == NUMBER_ALL) {
		return true;
	} else if (first == NUMBER_NON_SINGULAR) {
		return second != NUMBER_SINGULAR;
	} else if (second == NUMBER_NON_SINGULAR) {
		return first != NUMBER_SINGULAR;
	} else {
		return first == second;
	}
}

inline bool intersect(inflection& intersection,
		inflection first, inflection second)
{
	if (first == INFLECTION_ANY) {
		intersection = second;
	} else if (second == INFLECTION_ANY) {
		intersection = first;
	} else if (first == second) {
		intersection = first;
	} else if ((first == INFLECTION_NONE && second == INFLECTION_OTHER_VERB)
			|| (first == INFLECTION_OTHER_VERB && second == INFLECTION_NONE)) {
		intersection = INFLECTION_NONE;
	} else {
		return false;
	}
	return true;
}

template<typename Stream>
inline bool read(part_of_speech& pos, Stream& stream) {
	unsigned char c;
	if (!read(c, stream)) return false;
	pos = static_cast<part_of_speech>(c);
	return true;
}

template<typename Stream>
inline bool write(part_of_speech pos, Stream& stream) {
	return write((unsigned char) pos, stream);
}

template<typename Stream>
inline bool print(grammatical_number number, Stream& out) {
	switch (number) {
	case NUMBER_SINGULAR:
		return print("sg", out);
	case NUMBER_PLURAL:
		return print("pl", out);
	case NUMBER_UNCOUNTABLE:
		return print("uncountable", out);
	case NUMBER_NON_SINGULAR:
		return print("not_sg", out);
	case NUMBER_NON_PLURAL:
		return print("not_pl", out);
	case NUMBER_ALL:
		return print("all", out);
	case NUMBER_ANY:
		return print("any", out);
	case NUMBER_NONE:
		return print("none", out);
	}
	fprintf(stderr, "print ERROR: Unrecognized grammatical_number.\n");
	return false;
}

template<typename Stream>
inline bool print(inflection inf, Stream& out) {
	switch (inf) {
	case INFLECTION_PAST_PARTICIPLE:
		return print("past_participle", out);
	case INFLECTION_PRESENT_PARTICIPLE:
		return print("present_participle", out);
	case INFLECTION_INFINITIVE:
		return print("infinitive", out);
	case INFLECTION_OTHER_VERB:
		return print("other_verb_form", out);
	case INFLECTION_NOUN:
		return print("noun", out);
	case INFLECTION_ADJECTIVE:
		return print("adjective", out);
	case INFLECTION_COMPARATIVE:
		return print("comparative", out);
	case INFLECTION_SUPERLATIVE:
		return print("superlative", out);
	case INFLECTION_ANY:
		return print("any", out);
	case INFLECTION_NONE:
		return print("none", out);
	}
	fprintf(stderr, "print ERROR: Unrecognized inflection.\n");
	return false;
}

template<typename Stream, typename Printer>
inline bool print(const token& tok, Stream& out, Printer& printer) {
	return print("{root:'", out) && print(tok.id, out, printer)
		&& print("', number:", out) && print(tok.number, out)
		&& print(", form:", out) && print(tok.inf, out) && print('}', out);
}


template<typename T>
struct fixed_array {
	T* elements;
	unsigned int length;

	fixed_array(unsigned int length) : length(length) {
		elements = (T*) malloc(max((size_t) 1, sizeof(T) * length));
		if (elements == NULL) {
			fprintf(stderr, "fixed_array ERROR: Out of memory.\n");
			exit(EXIT_FAILURE);
		}
	}

	~fixed_array() {
		core::free(elements);
	}

	inline bool ensure_capacity(unsigned int new_length) {
		if (new_length > length
		 && !core::resize(elements, new_length)) return false;
		return true;
	}

	inline bool contains(const T& element) const {
		return index_of(element, elements, length) < length;
	}

	inline T& operator [] (unsigned int index) {
		return elements[index];
	}

	inline const T& operator [] (unsigned int index) const {
		return elements[index];
	}

	static inline void move(const fixed_array<T>& src, fixed_array<T>& dst) {
		dst.elements = src.elements;
		dst.length = src.length;
	}

	static inline void free(fixed_array<T>& items) {
		core::free(items.elements);
	}
};

template<typename T, typename Stream, typename... Printer,
	typename std::enable_if<is_printable<Stream>::value>::type* = nullptr>
inline bool print(const fixed_array<T>& a, Stream& out, Printer&&... printer) {
	return print(a.elements, a.length, out, std::forward<Printer>(printer)...);
}

template<typename T>
inline bool init(fixed_array<T>& tokens, unsigned int initial_capacity = 1) {
	tokens.length = 0;
	tokens.elements = (T*) malloc(sizeof(T) * initial_capacity);
	if (tokens.elements == NULL) {
		fprintf(stderr, "init ERROR: Insufficient memory for fixed_array.\n");
		return false;
	}
	return true;
}

struct token_sequence {
	token* tokens;
	unsigned int length;

	inline bool operator = (const token_sequence& src) {
		return initialize(src);
	}

	inline token& operator [] (unsigned int index) {
		return tokens[index];
	}

	inline const token& operator [] (unsigned int index) const {
		return tokens[index];
	}

	static inline unsigned int hash(const token_sequence& key) {
		return default_hash(key.tokens, key.length);
	}

	static inline bool is_empty(const token_sequence& key) {
		return key.tokens == NULL;
	}

	static inline void set_empty(token_sequence& key) {
		key.tokens = NULL;
	}

	static inline void move(const token_sequence& src, token_sequence& dst) {
		dst.tokens = src.tokens;
		dst.length = src.length;
	}

	static inline bool copy(const token_sequence& src, token_sequence& dst) {
		return dst.initialize(src);
	}

	static inline void free(token_sequence& seq) {
		core::free(seq.tokens);
	}

private:
	inline bool initialize(const token_sequence& src) {
		length = src.length;
		tokens = (token*) malloc(sizeof(token) * length);
		if (tokens == NULL) {
			fprintf(stderr, "token_sequence.initialize ERROR: Out of memory.\n");
			return false;
		}
		memcpy(tokens, src.tokens, sizeof(token) * length);
		return true;
	}
};

/* TODO: need to handle compound words better */
struct morphology
{
	/* map from inflected words to roots */
	hash_map<unsigned int, fixed_array<token>> word_to_root_map;

	/* map from roots to inflections of the root */
	hash_map<token, fixed_array<unsigned int>> root_to_word_map;

	fixed_array<unsigned int> auxiliaries;
	fixed_array<unsigned int> auxiliary_roots;

	morphology() : word_to_root_map(1 << 18), root_to_word_map(1 << 19), auxiliaries(8), auxiliary_roots(8) { }

	~morphology() {
		for (auto entry : word_to_root_map)
			free(entry.value);
		for (auto entry : root_to_word_map)
			free(entry.value);
	}

	inline bool initialize(hash_map<string, unsigned int>& token_map) {
		unsigned int be, is, are, was, were, being, been;
		unsigned int wit, wist, witting, wot, wite;
		if (!get_token("be", be, token_map) || !get_token("is", is, token_map)
		 || !get_token("are", are, token_map) || !get_token("was", was, token_map)
		 || !get_token("were", were, token_map) || !get_token("being", being, token_map)
		 || !get_token("been", been, token_map) || !get_token("wit", wit, token_map)
		 || !get_token("wist", wist, token_map) || !get_token("witting", witting, token_map)
		 || !get_token("wot", wot, token_map) || !get_token("wite", wite, token_map))
			return false;

		if (!add_token(be,		{be, NUMBER_ANY,		INFLECTION_INFINITIVE})
		 || !add_token(is,		{be, NUMBER_SINGULAR,	INFLECTION_OTHER_VERB})
		 || !add_token(are,		{be, NUMBER_PLURAL,		INFLECTION_OTHER_VERB})
		 || !add_token(was,		{be, NUMBER_SINGULAR,	INFLECTION_OTHER_VERB})
		 || !add_token(were,	{be, NUMBER_PLURAL,		INFLECTION_OTHER_VERB})
		 || !add_token(being,	{be, NUMBER_ANY,		INFLECTION_PRESENT_PARTICIPLE})
		 || !add_token(been,	{be, NUMBER_ANY,		INFLECTION_PAST_PARTICIPLE})
		 || !add_token(wit,		{wit, NUMBER_ANY,		INFLECTION_INFINITIVE})
		 || !add_token(wot,		{wit, NUMBER_SINGULAR,	INFLECTION_OTHER_VERB})
		 || !add_token(wite,	{wit, NUMBER_PLURAL,	INFLECTION_OTHER_VERB})
		 || !add_token(wist,	{wit, NUMBER_ANY,		INFLECTION_OTHER_VERB})
		 || !add_token(witting,	{wit, NUMBER_ANY,		INFLECTION_PRESENT_PARTICIPLE})
		 || !add_token(wist,	{wit, NUMBER_ANY,		INFLECTION_PAST_PARTICIPLE}))
			return false;

		if (!auxiliaries.ensure_capacity(7)
		 || !auxiliary_roots.ensure_capacity(1)) return false;
		auxiliaries.elements[0] = be;
		auxiliaries.elements[1] = is;
		auxiliaries.elements[2] = are;
		auxiliaries.elements[3] = was;
		auxiliaries.elements[4] = were;
		auxiliaries.elements[5] = being;
		auxiliaries.elements[6] = been;
		auxiliaries.length = 7;
		auxiliary_roots.elements[0] = be;
		auxiliary_roots.length = 1;
		insertion_sort(auxiliaries.elements, auxiliaries.length);
		insertion_sort(auxiliary_roots.elements, auxiliary_roots.length);
		return true;
	}

	inline bool is_auxiliary_verb(unsigned int word) const {
		return auxiliaries.contains(word);
	}

	inline bool is_auxiliary_root(unsigned int root) const {
		return auxiliary_roots.contains(root);
	}

	const fixed_array<token>& parse(unsigned int word) const {
		static const fixed_array<token> empty_roots(0);

		bool contains;
		const fixed_array<token>& roots = word_to_root_map.get(word, contains);
		if (!contains)
			return empty_roots;
		else return roots;
	}

	const fixed_array<unsigned int>& inflect(const token& tok) const {
		static const fixed_array<unsigned int> empty_words(0);

		bool contains;
		const fixed_array<unsigned int>& words = root_to_word_map.get(tok, contains);
		if (!contains)
			return empty_words;
		else return words;
	}

	template<bool Quiet>
	bool add_root(const array<char>& token,
			part_of_speech pos, bool uncertain_pos,
			const array<array<string>>& inflected_forms,
			hash_map<string, unsigned int>& token_map)
	{
		/* drop the word if one of the inflected forms are missing */
		for (const array<string>& inflected_form : inflected_forms)
			if (inflected_form.length == 0) return true;

		unsigned int root, token_id;
		switch (pos) {
		case POS_VERB:
			if (inflected_forms.length == 3) {
				if (!get_token(string(token.data, token.length), root, token_map))
					return false;
				for (unsigned int i = 0; i < inflected_forms[0].length; i++) {
					if (!get_token(inflected_forms[0][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_OTHER_VERB})
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_PAST_PARTICIPLE}))
						return false;
				} for (unsigned int i = 0; i < inflected_forms[1].length; i++) {
					if (!get_token(inflected_forms[1][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_PRESENT_PARTICIPLE}))
						return false;
				} for (unsigned int i = 0; i < inflected_forms[2].length; i++) {
					if (!get_token(inflected_forms[2][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_SINGULAR, INFLECTION_OTHER_VERB}))
						return false;
				}
				return add_token(root, {root, NUMBER_ANY, INFLECTION_INFINITIVE})
					&& add_token(root, {root, NUMBER_PLURAL, INFLECTION_OTHER_VERB}); /* TODO: we currently only use third-person */
			} else if (inflected_forms.length == 4) {
				if (!get_token(string(token.data, token.length), root, token_map))
					return false;
				for (unsigned int i = 0; i < inflected_forms[0].length; i++) {
					if (!get_token(inflected_forms[0][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_OTHER_VERB}))
						return false;
				} for (unsigned int i = 0; i < inflected_forms[1].length; i++) {
					if (!get_token(inflected_forms[1][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_PAST_PARTICIPLE}))
						return false;
				} for (unsigned int i = 0; i < inflected_forms[2].length; i++) {
					if (!get_token(inflected_forms[2][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_PRESENT_PARTICIPLE}))
						return false;
				} for (unsigned int i = 0; i < inflected_forms[3].length; i++) {
					if (!get_token(inflected_forms[3][i], token_id, token_map)
					 || !add_token(token_id, {root, NUMBER_SINGULAR, INFLECTION_OTHER_VERB}))
						return false;
				}
				return add_token(root, {root, NUMBER_ANY, INFLECTION_INFINITIVE})
					&& add_token(root, {root, NUMBER_PLURAL, INFLECTION_OTHER_VERB}); /* TODO: we currently only use third-person */
			} else if (compare_strings(token, "be") || compare_strings(token, "wit")) {
				/* these are exceptions we consider separately */
				return true;
			} else {
				if (!Quiet) {
					print("morphology.add_root WARNING: Incorrect number of inflected forms for verb '", stderr);
					print(string(token.data, token.length), stderr); print("'.\n", stderr);
				}
				return true;
			}

		case POS_NOUN:
			if (inflected_forms.length != 1) {
				if (!Quiet) {
					print("morphology.add_root WARNING: Incorrect number of inflected forms for noun '", stderr);
					print(string(token.data, token.length), stderr); print("'.\n", stderr);
				}
				return true;
			}
			if (!get_token(string(token.data, token.length), root, token_map))
				return false;
			for (unsigned int i = 0; i < inflected_forms[0].length; i++) {
				if (!get_token(inflected_forms[0][i], token_id, token_map)
				 || !add_token(token_id, {root, NUMBER_PLURAL, INFLECTION_NOUN}))
					return false;
			}
			return add_token(root, {root, NUMBER_SINGULAR, INFLECTION_NOUN});

		case POS_ADJECTIVE:
			if (inflected_forms.length != 2) {
				if (!Quiet) {
					print("morphology.add_root WARNING: Incorrect number of inflected forms for adjective/adverb '", stderr);
					print(string(token.data, token.length), stderr); print("'.\n", stderr);
				}
				return true;
			}
			if (!get_token(string(token.data, token.length), root, token_map))
				return false;
			for (unsigned int i = 0; i < inflected_forms[0].length; i++) {
				if (!get_token(inflected_forms[0][i], token_id, token_map)
				 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_COMPARATIVE}))
					return false;
			} for (unsigned int i = 0; i < inflected_forms[1].length; i++) {
				if (!get_token(inflected_forms[1][i], token_id, token_map)
				 || !add_token(token_id, {root, NUMBER_ANY, INFLECTION_SUPERLATIVE}))
					return false;
			}
			return add_token(root, {root, NUMBER_ANY, INFLECTION_ADJECTIVE});

		case POS_OTHER:
			break;
		}

		fprintf(stderr, "morphology.add_root ERROR: Unrecognized part of speech.\n");
		return false;
	}

	template<bool Quiet>
	bool add_uncountable_noun(const array<char>& token,
			hash_map<string, unsigned int>& token_map)
	{
		unsigned int root;
		return get_token(string(token.data, token.length), root, token_map)
			&& add_token(root, {root, NUMBER_UNCOUNTABLE, INFLECTION_NOUN});
	}

private:
	inline bool add_token(unsigned int word, const token& tok) {
		if (!word_to_root_map.check_size()
		 || !root_to_word_map.check_size()) return false;

		bool contains; unsigned int bucket;
		fixed_array<token>& tokens = word_to_root_map.get(word, contains, bucket);
		if (!contains) {
			if (!init(tokens)) return false;
			word_to_root_map.table.keys[bucket] = word;
			word_to_root_map.table.size++;
		} else if (!tokens.ensure_capacity(tokens.length + 1)) {
			return false;
		}

		/* check if the token already exists in the map */
		if (tokens.contains(tok)) return true;

		tokens[tokens.length] = tok;
		tokens.length++;

		fixed_array<unsigned int>& words = root_to_word_map.get(tok, contains, bucket);
		if (!contains) {
			if (!init(words)) return false;
			root_to_word_map.table.keys[bucket] = tok;
			root_to_word_map.table.size++;
		} else if (!words.ensure_capacity(words.length + 1)) {
			return false;
		}

		/* check if the word already exists in the map */
		if (words.contains(word)) return true;

		words[words.length] = word;
		words.length++;
		return true;
	}
};

template<bool Lowercase, typename Stream>
inline bool agid_parse_token(Stream& in, int& next,
		position& current, array<char>& token)
{
	next = fgetc(in); current.column++;
	if (next == EOF) {
		/* end of stream */
		return true;
	} if (!isalpha(next) && next != '\'') {
		read_error("Expected alphabetic character at beginning of word", current);
		return false;
	} else if (!token.add(Lowercase ? tolower(next) : next)) return false;

	next = fgetc(in); current.column++;
	while (isalpha(next) || next == '\'' || next == '_') {
		if (next == '_' && !token.add(' ')) return false;
		else if (!token.add(Lowercase ? tolower(next) : next)) return false;
		next = fgetc(in); current.column++;
	}

	return true;
}

template<bool Lowercase, typename Stream>
inline bool agid_parse_inflected_entry(Stream& in, int& next,
		position& current, array<string>& inflected_form)
{
	array<char> token = array<char>(64);
	if (!agid_parse_token<Lowercase>(in, next, current, token))
		return false;

	bool discard_entry = false;
	if (next == '~') {
		next = fgetc(in); current.column++;
	} if (next == '!') {
		next = fgetc(in); current.column++;
		discard_entry = true;
	} if (next == '<') {
		next = fgetc(in); current.column++;
		discard_entry = true;
	} if (next == '?') {
		next = fgetc(in); current.column++;
	}

	if (!discard_entry) {
		/* add the inflected entry into the list */
		if (!inflected_form.ensure_capacity(inflected_form.length + 1)
		 || !init(inflected_form[inflected_form.length], token.data, token.length))
			return false;
		inflected_form.length++;
	}

	if (next == ' ') {
		next = fgetc(in); current.column++;
		if (next == '|') {
			/* this is actually the separator between inflected forms */
			if (ungetc(next, in) == EOF) return false;
			next = ' '; return true;
		} else if (isdigit(next)) {
			/* this is a variant level indicator */
			/* we ignore the variant level */
			next = fgetc(in); current.column++;
			if (next == '.') {
				next = fgetc(in); current.column++;
				if (!isdigit(next)) {
					read_error("Expected number after period in variant specification", current);
					return false;
				}
				next = fgetc(in); current.column++;
			}

			if (next != ' ') {
				return true;
			}

			next = fgetc(in); current.column++;
			if (next == '|') {
				/* this is actually the separator between inflected forms */
				if (ungetc(next, in) == EOF) return false;
				next = ' '; return true;
			}
		}

		if (next == '{') {
			/* this is an explanation */
			next = fgetc(in); current.column++;
			while (next != '}') {
				next = fgetc(in); current.column++;
				if (next == '\n') {
					read_error("Expected space between inflected entries", current);
					return false;
				}
			}
			next = fgetc(in); current.column++;
		} else {
			read_error("Unexpected symbol after inflected entry", current);
			return false;
		}
	}

	return true;
}

inline void free_inflected_form(array<string>& inflected_form) {
	for (string& entry : inflected_form)
		free(entry);
	free(inflected_form);
}

void free_inflected_forms(array<array<string>>& inflected_forms) {
	for (array<string>& inflected_form : inflected_forms)
		free_inflected_form(inflected_form);
}

template<bool Lowercase, typename Stream>
inline bool agid_parse_inflected_form(Stream& in, int& next,
		position& current, array<string>& inflected_form)
{
	/* parse first inflected entry */
	if (!agid_parse_inflected_entry<Lowercase>(in, next, current, inflected_form)) {
		free_inflected_form(inflected_form); return false;
	}

	/* parse the remaining inflected entries */
	while (true) {
		if (next == ',') {
			/* this is another inflected entry */
			next = fgetc(in); current.column++;
			if (next != ' ') {
				read_error("Expected space between inflected entries", current);
				free_inflected_form(inflected_form); return false;
			}
			if (!agid_parse_inflected_entry<Lowercase>(in, next, current, inflected_form)) {
				free_inflected_form(inflected_form); return false;
			}
		} else {
			/* this is the end of this inflected form */
			return true;
		}
	}
}

template<bool Lowercase, bool Quiet, typename Stream>
inline bool agid_parse_word(Stream& in, morphology& morph,
		hash_map<string, unsigned int>& token_map,
		int& next, position& current)
{
	array<char> token = array<char>(64);
	array<array<string>> inflected_forms = array<array<string>>(8);
	if (!agid_parse_token<Lowercase>(in, next, current, token))
		return false;
	if (next == EOF) return true;

	if (next != ' ') {
		read_error("Invalid character in word", current);
		return false;
	}

	part_of_speech pos;
	next = fgetc(in); current.column++;
	if (next == 'V') {
		pos = POS_VERB;
	} else if (next == 'N') {
		pos = POS_NOUN;
	} else if (next == 'A') {
		pos = POS_ADJECTIVE;
	} else {
		read_error("Expected part of speech marker 'V', 'N', or 'A'", current);
		return false;
	}

	bool uncertain_pos = false;
	next = fgetc(in); current.column++;
	if (next == '?') {
		uncertain_pos = true;
		next = fgetc(in); current.column++;
	}

	if (next != ':') {
		read_error("Expected colon ':'", current);
		return false;
	}
	next = fgetc(in); current.column++;
	if (next != ' ') {
		read_error("Expected space before inflected forms", current);
		return false;
	}

	/* read the first inflected form */
	if (!array_init(inflected_forms[0], 4)
	 || !agid_parse_inflected_form<Lowercase>(in, next, current, inflected_forms[0])) {
		free_inflected_forms(inflected_forms); return false;
	}
	inflected_forms.length++;

	/* read the remaining inflected forms */
	while (true) {
		if (next == ' ') {
			/* this is another inflected form */
			next = fgetc(in); current.column++;
			if (next != '|') {
				read_error("Expected separator '|' between inflected forms", current);
				free_inflected_forms(inflected_forms); return false;
			}
			next = fgetc(in); current.column++;
			if (next != ' ') {
				read_error("Expected space after separator '|' between inflected forms", current);
				free_inflected_forms(inflected_forms); return false;
			}
			if (!array_init(inflected_forms[inflected_forms.length], 4)
			 || !agid_parse_inflected_form<Lowercase>(in, next, current, inflected_forms[inflected_forms.length])) {
				free_inflected_forms(inflected_forms); return false;
			}
			inflected_forms.length++;
		} else if (next == '\n') {
			/* this is the end of list of inflected forms */
			current.column = 1; current.line++; break;
		} else {
			read_error("Expected space or newline after inflected form", current);
			free_inflected_forms(inflected_forms); return false;
		}
	}

	bool success = morph.add_root<Quiet>(token, pos, uncertain_pos, inflected_forms, token_map);
	free_inflected_forms(inflected_forms);
	return success;
}

/**
 * This function parses the Automatically Generated Inflection Database (AGID),
 * available at: https://github.com/en-wl/wordlist
 */
template<bool Lowercase, bool Quiet, typename Stream>
bool agid_parse(Stream& in, morphology& morph,
		hash_map<string, unsigned int>& token_map)
{
	int next = 0;
	position current = position(1, 1);
	while (next != EOF) {
		if (!agid_parse_word<Lowercase, Quiet>(in, morph, token_map, next, current))
			return false;
	}
	return true;
}

template<bool Lowercase, bool Quiet, typename Stream>
bool uncountable_parse(Stream& in, morphology& morph,
		hash_map<string, unsigned int>& token_map)
{
	int next = 0;
	position current = position(1, 1);
	array<char> token = array<char>(64);
	while (next != EOF) {
		if (!agid_parse_token<Lowercase>(in, next, current, token))
			return false;
		if (next == EOF) {
			return true;
		} else if (next != '\n') {
			read_error("Invalid character in word", current);
			return false;
		}

		if (!morph.add_uncountable_noun<Quiet>(token, token_map))
			return false;
		current.line++;
		current.column = 1;
		token.clear();
	}
	return true;
}

inline bool morphology_read(
		morphology& morph, hash_map<string, unsigned int>& names,
		const char* agid_filepath, const char* uncountable_filepath)
{
	FILE* in = fopen(agid_filepath, "r");
	if (in == NULL) {
		fprintf(stderr, "morphology_read ERROR: Unable to open '%s' for reading.\n", agid_filepath);
		return false;
	} else if (!agid_parse<true, true>(in, morph, names)) {
		fclose(in); return false;
	}
	fclose(in);

	in = fopen(uncountable_filepath, "r");
	if (in == NULL) {
		fprintf(stderr, "morphology_read ERROR: Unable to open '%s' for reading.\n", uncountable_filepath);
		return false;
	} else if (!uncountable_parse<true, true>(in, morph, names)) {
		fclose(in); return false;
	}
	fclose(in);
	return true;
}

/* unit test for the morphology model */
inline bool morphology_test(const char* agid_filepath = "infl.txt")
{
	morphology morph;
	hash_map<string, unsigned int> names(1 << 19);
	if (!morph.initialize(names)) {
		fprintf(stderr, "morphology_test ERROR: Unable to initialize morphology structure.\n");
		return false;
	}

	/* read the word inflection database */
	FILE* in = fopen(agid_filepath, "r");
	if (in == NULL) {
		fprintf(stderr, "morphology_test ERROR: Unable to open '%s' for reading.\n", agid_filepath);
		return false;
	} else if (!agid_parse<true, true>(in, morph, names)) {
		for (auto entry : names) free(entry.key);
		fclose(in); return false;
	}
	fclose(in);

	const string** name_ids = invert(names);
	string_map_scribe terminal_printer = { name_ids, names.table.size + 1 };

	/* try parsing some words */
	unsigned int sung, flies, sheep, are, were, sing, fly, be, asdf;
	if (!get_token("sung", sung, names) || !get_token("flies", flies, names) || !get_token("sheep", sheep, names)
	 || !get_token("are", are, names) || !get_token("were", were, names) || !get_token("sing", sing, names)
	 || !get_token("fly", fly, names) || !get_token("be", be, names) || !get_token("asdf", asdf, names)) {
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<token>& tokens_are = morph.parse(are);
	const token token_be = {be, NUMBER_PLURAL, INFLECTION_OTHER_VERB};
	const token token_are = {are, NUMBER_SINGULAR, INFLECTION_NOUN};
	if (tokens_are.length != 2 || tokens_are[0] != token_be || tokens_are[1] != token_are) {
		print("morphology_test ERROR: Unexpected parse output for input 'are': ", stderr);
		print(tokens_are, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<token>& tokens_sung = morph.parse(sung);
	const token token_sing = {sing, NUMBER_ANY, INFLECTION_PAST_PARTICIPLE};
	if (tokens_sung.length != 1 || tokens_sung[0] != token_sing) {
		print("morphology_test ERROR: Unexpected parse output for input 'sung': ", stderr);
		print(tokens_sung, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<token>& tokens_flies = morph.parse(flies);
	const token token_fly_n = {fly, NUMBER_PLURAL, INFLECTION_NOUN};
	const token token_fly_v = {fly, NUMBER_SINGULAR, INFLECTION_OTHER_VERB};
	if (tokens_flies.length != 2 || tokens_flies[0] != token_fly_n || tokens_flies[1] != token_fly_v) {
		print("morphology_test ERROR: Unexpected parse output for input 'flies': ", stderr);
		print(tokens_flies, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<token>& tokens_sheep = morph.parse(sheep);
	const token token_sheep_plu = {sheep, NUMBER_PLURAL, INFLECTION_NOUN};
	const token token_sheep_sing = {sheep, NUMBER_SINGULAR, INFLECTION_NOUN};
	if (tokens_sheep.length != 2 || tokens_sheep[0] != token_sheep_plu || tokens_sheep[1] != token_sheep_sing) {
		print("morphology_test ERROR: Unexpected parse output for input 'sheep': ", stderr);
		print(tokens_sheep, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<token>& tokens_asdf = morph.parse(asdf);
	if (tokens_asdf.length != 0) {
		print("morphology_test ERROR: Unexpected parse output for input 'asdf': ", stderr);
		print(tokens_asdf, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	/* try generating some inflections */
	const fixed_array<unsigned int>& words_sing = morph.inflect({sing, NUMBER_ANY, INFLECTION_PAST_PARTICIPLE});
	if (words_sing.length != 1 || words_sing[0] != sung) {
		print("morphology_test ERROR: Unexpected inflection output for input 'sing': ", stderr);
		print(words_sing, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<unsigned int>& words_be = morph.inflect({be, NUMBER_PLURAL, INFLECTION_OTHER_VERB});
	if (words_be.length != 2 || words_be[0] != are || words_be[1] != were) {
		print("morphology_test ERROR: Unexpected inflection output for input 'be': ", stderr);
		print(words_be, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	const fixed_array<unsigned int>& words_fly = morph.inflect({fly, NUMBER_SINGULAR, INFLECTION_OTHER_VERB});
	if (words_fly.length != 1 || words_fly[0] != flies) {
		print("morphology_test ERROR: Unexpected inflection output for input 'fly': ", stderr);
		print(words_fly, stderr, terminal_printer); print(".\n", stderr);
		for (auto entry : names) free(entry.key);
		free(name_ids); return false;
	}

	for (auto entry : names) free(entry.key);
	free(name_ids);
	return true;
}

#endif /* MORPHOLOGY_H_ */
