/**
 * hdp_grammar_io.h
 *
 *  Created on: Jan 24, 2017
 *      Author: asaparov
 */

#ifndef HDP_GRAMMAR_IO_H_
#define HDP_GRAMMAR_IO_H_

#include <core/lex.h>

#include "hdp_grammar.h"
#include "token_distribution.h"

enum grammar_token_type {
	GRAMMAR_IDENTIFIER,
	GRAMMAR_FLOAT,
	GRAMMAR_COLON,
	GRAMMAR_COMMA,
	GRAMMAR_SLASH,
	GRAMMAR_LEFT_BRACE,
	GRAMMAR_RIGHT_BRACE,
	GRAMMAR_END_STATEMENT,
	GRAMMAR_KEYWORD_ARROW,
	GRAMMAR_KEYWORD_NONEMPTY,
	GRAMMAR_KEYWORD_NOSPACE,
	GRAMMAR_KEYWORD_TOKEN,
	GRAMMAR_KEYWORD_NONTERMINAL,
	GRAMMAR_KEYWORD_SIMPLE,
	GRAMMAR_KEYWORD_SPECIAL,
	GRAMMAR_KEYWORD_PRETERMINAL,
	GRAMMAR_KEYWORD_PRETERMINAL_NUMBER,
	GRAMMAR_KEYWORD_PRETERMINAL_STRING
};

template<typename Stream>
bool print(const grammar_token_type& token, Stream& out) {
	switch (token) {
	case GRAMMAR_IDENTIFIER:
		return fprintf(out, "identifier") > 0;
	case GRAMMAR_FLOAT:
		return fprintf(out, "floating-point number") > 0;
	case GRAMMAR_COLON:
		return fprintf(out, "colon") > 0;
	case GRAMMAR_COMMA:
		return fprintf(out, "comma") > 0;
	case GRAMMAR_SLASH:
		return fprintf(out, "slash") > 0;
	case GRAMMAR_LEFT_BRACE:
		return fprintf(out, "left curly brace") > 0;
	case GRAMMAR_RIGHT_BRACE:
		return fprintf(out, "right curly brace") > 0;
	case GRAMMAR_END_STATEMENT:
		return fprintf(out, "newline") > 0;
	case GRAMMAR_KEYWORD_ARROW:
		return fprintf(out, "arrow keyword") > 0;
	case GRAMMAR_KEYWORD_NONEMPTY:
		return fprintf(out, "nonempty keyword") > 0;
	case GRAMMAR_KEYWORD_NOSPACE:
		return fprintf(out, "no_whitespace keyword") > 0;
	case GRAMMAR_KEYWORD_NONTERMINAL:
		return fprintf(out, "nonterminal keyword") > 0;
	case GRAMMAR_KEYWORD_SIMPLE:
		return fprintf(out, "simple keyword") > 0;
	case GRAMMAR_KEYWORD_SPECIAL:
		return fprintf(out, "special keyword") > 0;
	case GRAMMAR_KEYWORD_PRETERMINAL:
		return fprintf(out, "preterminal keyword") > 0;
	case GRAMMAR_KEYWORD_PRETERMINAL_NUMBER:
		return fprintf(out, "number_preterminal keyword") > 0;
	case GRAMMAR_KEYWORD_PRETERMINAL_STRING:
		return fprintf(out, "string_preterminal keyword") > 0;
	default:
		fprintf(stderr, "print ERROR: Unrecognized grammar_token_type.\n");
		return false;
	}
}

typedef lexical_token<grammar_token_type> grammar_token;

const char* grammar_keywords[] = {
	"->",
	"nonempty",
	"no_whitespace",
	"is_token",
	"nonterminal",
	"simple",
	"special",
	"preterminal",
	"number_preterminal",
	"string_preterminal"
};

grammar_token_type grammar_keyword_tokens[] = {
	GRAMMAR_KEYWORD_ARROW,
	GRAMMAR_KEYWORD_NONEMPTY,
	GRAMMAR_KEYWORD_NOSPACE,
	GRAMMAR_KEYWORD_TOKEN,
	GRAMMAR_KEYWORD_NONTERMINAL,
	GRAMMAR_KEYWORD_SIMPLE,
	GRAMMAR_KEYWORD_SPECIAL,
	GRAMMAR_KEYWORD_PRETERMINAL,
	GRAMMAR_KEYWORD_PRETERMINAL_NUMBER,
	GRAMMAR_KEYWORD_PRETERMINAL_STRING
};

enum grammar_lexer_state {
	GRAMMAR_START,
	GRAMMAR_STRING,
	GRAMMAR_ESCAPE,
	GRAMMAR_NAME,
	GRAMMAR_NUMBER,
	GRAMMAR_DECIMAL,
	GRAMMAR_EXPONENT
};

inline bool grammar_emit_name(array<grammar_token>& tokens,
		array<char>& token, const position& start, const position& end)
{
	/* check if this is a keyword */
	for (unsigned int i = 0; i < array_length(grammar_keywords); i++) {
		if (compare_strings(token, grammar_keywords[i])) {
			return emit_token(tokens, token, start, end, grammar_keyword_tokens[i]);
		}
	}

	/* it's an identifier */
	return emit_token(tokens, token, start, end, GRAMMAR_IDENTIFIER);
}

inline bool grammar_process_symbol(array<grammar_token>& tokens,
		const char* input, grammar_lexer_state& state, const position& start,
		const position& current, array<char>& token, unsigned int i,
		unsigned int char_width, grammar_token_type token_type)
{
	if (state == GRAMMAR_STRING) {
		if (!token.append(input + i, char_width))
			return false;
	} else if (state == GRAMMAR_ESCAPE) {
		if (!token.append(input + i, char_width))
			return false;
		state = GRAMMAR_STRING;
	} else if (state == GRAMMAR_NAME) {
		if (!grammar_emit_name(tokens, token, start, current)
		 || !emit_token(tokens, current, current + char_width, token_type))
			return false;
		state = GRAMMAR_START;
	} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL || state == GRAMMAR_EXPONENT) {
		if (!emit_token(tokens, token, start, current, GRAMMAR_FLOAT)
		 || !emit_token(tokens, current, current + char_width, token_type))
			return false;
		state = GRAMMAR_START;
	} else if (state == GRAMMAR_START) {
		if (!emit_token(tokens, current, current + char_width, token_type))
			return false;
	} else {
		read_error("Unexpected symbol", current);
		return false;
	}
	return true;
}

bool grammar_lex(array<grammar_token>& tokens,
		const char* input, unsigned int length)
{
	position start = position(1, 1);
	position current = position(1, 1);
	grammar_lexer_state state = GRAMMAR_START;
	array<char> token = array<char>(1024);

	for (unsigned int i = 0; i < length;) {
		wchar_t next, peek;
		bool new_line = false;
		unsigned int peek_width;
		unsigned int char_width = mbtowc(&next, input + i, length - i);

		switch (next) {
		case '"':
			if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_STRING) {
				if (!grammar_emit_name(tokens, token, start, current))
					return false;
				state = GRAMMAR_START;
			} else if (state == GRAMMAR_START) {
				state = GRAMMAR_STRING;
				start = current;
			} else {
				read_error("Unexpected double quote", current);
				return false;
			}
			break;

		case '\r':
			if (i + char_width < length) {
				peek_width = mbtowc(&peek, input + i + char_width, length - i - char_width);
				if (peek_width > 0 && peek == '\n') {
					i += char_width; current.column++;
					char_width = peek_width; next = peek;
				}
			}
		case '\n':
			new_line = true;
			if (state == GRAMMAR_NAME) {
				if (!grammar_emit_name(tokens, token, start, current)
				 || !emit_token(tokens, current, current + char_width, GRAMMAR_END_STATEMENT))
					return false;
				state = GRAMMAR_START;
				break;
			} else if (state == GRAMMAR_START) {
				if (tokens.length > 0 && tokens.last().type == GRAMMAR_END_STATEMENT)
					break; /* ignore empty lines */
				if (!emit_token(tokens, current, current + char_width, GRAMMAR_END_STATEMENT))
					return false;
				break;
			} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL || state == GRAMMAR_EXPONENT) {
				if (!emit_token(tokens, token, start, current, GRAMMAR_FLOAT)
				 || !emit_token(tokens, current, current + char_width, GRAMMAR_END_STATEMENT))
					return false;
				state = GRAMMAR_START;
				break;
			}
		case ' ':
		case '\t':
			if (state == GRAMMAR_STRING) {
				if (!token.append(input + i, char_width))
					return false;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_NAME) {
				if (!grammar_emit_name(tokens, token, start, current))
					return false;
				state = GRAMMAR_START;
			} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL || state == GRAMMAR_EXPONENT) {
				if (!emit_token(tokens, token, start, current, GRAMMAR_FLOAT))
					return false;
				state = GRAMMAR_START;
			}
			break;

		case ':':
			if (!grammar_process_symbol(tokens, input, state, start, current, token, i, char_width, GRAMMAR_COLON))
				return false;
			break;

		case '{':
			if (!grammar_process_symbol(tokens, input, state, start, current, token, i, char_width, GRAMMAR_LEFT_BRACE))
				return false;
			break;

		case '}':
			if (!grammar_process_symbol(tokens, input, state, start, current, token, i, char_width, GRAMMAR_RIGHT_BRACE))
				return false;
			break;

		case ',':
			if (!grammar_process_symbol(tokens, input, state, start, current, token, i, char_width, GRAMMAR_COMMA))
				return false;
			break;

		case '/':
			if (!grammar_process_symbol(tokens, input, state, start, current, token, i, char_width, GRAMMAR_SLASH))
				return false;
			break;

		case '#':
			if (state == GRAMMAR_STRING) {
				if (!token.append(input + i, char_width))
					return false;
				break;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
				break;
			} else if (state == GRAMMAR_NAME) {
				if (!grammar_emit_name(tokens, token, start, current))
					return false;
			} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL || state == GRAMMAR_EXPONENT) {
				if (!emit_token(tokens, token, start, current, GRAMMAR_FLOAT))
					return false;
			}

			/* this is a comment, so consume the entire line */
			peek_width = char_width;
			while (i + peek_width < length) {
				i += peek_width;
				current.column += peek_width;
				peek_width = mbtowc(&peek, input + i, length - i);
				if (peek == '\n' || peek_width == 0) {
					break;
				} else if (peek_width == static_cast<unsigned int>(-1)) {
					read_error("Invalid character", current);
					return false;
				}
			}
			if (!emit_token(tokens, current, current + char_width, GRAMMAR_END_STATEMENT))
				return false;
			new_line = true;
			char_width = peek_width; next = peek;
			state = GRAMMAR_START;
			break;

		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
			if (state == GRAMMAR_STRING || state == GRAMMAR_NAME
			 || state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL
			 || state == GRAMMAR_EXPONENT) {
				if (!token.append(input + i, char_width))
					return false;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_START) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_NUMBER;
				start = current;
			} else {
				read_error("Unexpected numeral", current);
				return false;
			}
			break;

		case 'e':
		case 'E':
			if (state == GRAMMAR_STRING || state == GRAMMAR_NAME) {
				if (!token.append(input + i, char_width))
					return false;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_START) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_NAME;
				start = current;
			} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL) {
				if (!token.append(input + i, char_width))
					return false;
				if (i + char_width < length) {
					peek_width = mbtowc(&peek, input + i + char_width, length - i - char_width);
					if (peek_width > 0 && (peek == '+' || peek == '-')) {
						if (!token.append(input + i + char_width, peek_width))
							return false;
						i += char_width; current.column++;
						char_width = peek_width; next = peek;
					}
				}
				state = GRAMMAR_EXPONENT;
			} else {
				read_error("Unexpected 'e' or 'E'", current);
				return false;
			}
			break;

        case '.':
			if (state == GRAMMAR_STRING) {
				if (!token.append(input + i, char_width))
					return false;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_NUMBER) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_DECIMAL;
			} else {
				read_error("Unexpected period", current);
				return false;
			}
			break;

		default:
			if (state == GRAMMAR_STRING || state == GRAMMAR_NAME) {
				if (!token.append(input + i, char_width))
					return false;
			} else if (state == GRAMMAR_ESCAPE) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_STRING;
			} else if (state == GRAMMAR_START) {
				if (!token.append(input + i, char_width))
					return false;
				state = GRAMMAR_NAME;
				start = current;
			} else {
				read_error("Unexpected symbol", current);
				return false;
			}
		}

		i += char_width;
		if (new_line) {
			current.line++;
			current.column = 1;
		} else current.column++;
	}

	if (state == GRAMMAR_STRING || state == GRAMMAR_ESCAPE) {
		/* TODO: feed non-trivial length tokens to the error so that it may compute its position */
		read_error("Unterminated string", current);
		return false;
	} else if (state == GRAMMAR_NAME) {
		if (!grammar_emit_name(tokens, token, start, current))
			return false;
	} else if (state == GRAMMAR_NUMBER || state == GRAMMAR_DECIMAL || state == GRAMMAR_EXPONENT) {
		if (!emit_token(tokens, token, start, current, GRAMMAR_FLOAT))
			return false;
	}

	return true;
}

template<typename Semantics>
inline bool read_feature_list_item(
		const array<grammar_token>& tokens,
		unsigned int& index, typename Semantics::feature& item)
{
	if (!expect_token(tokens, index, GRAMMAR_IDENTIFIER, "semantic feature/function identifier")) {
		return false;
	} else if (!Semantics::interpret(item, tokens[index].text)) {
		fprintf(stderr, "ERROR at %d:%d: Failed to read semantic feature name.\n", tokens[index].start.line, tokens[index].start.column);
		return false;
	}
	return true;
}

inline bool read_list_item(
		const array<grammar_token>& tokens,
		unsigned int& index, double& item)
{
	return (expect_token(tokens, index, GRAMMAR_FLOAT, "a floating-point number")
		 && parse_float(tokens[index].text, item));
}

inline bool read_list_item(
		const array<grammar_token>& tokens,
		unsigned int& index, string& item)
{
	return (expect_token(tokens, index, GRAMMAR_IDENTIFIER, "a string")
		 && init(item, tokens[index].text));
}

template<typename T>
inline bool read_list(const array<grammar_token>& tokens,
		unsigned int& index, T*& list, unsigned int fixed_length)
{
	/* check if the list is empty */
	if (index < tokens.length && tokens[index].type == GRAMMAR_RIGHT_BRACE) {
		index++;
		return true;
	}

	unsigned int length = 0;
	while (true) {
		if (length >= fixed_length) {
			fprintf(stderr, "ERROR at %d:%d: Too many entries in list.\n",
					tokens[index - 1].end.line, tokens[index - 1].end.column);
			return false;
		}

		if (!read_list_item(tokens, index, list[length]))
			return false;
		index++; length++;

		if (index == tokens.length) {
			fprintf(stderr, "ERROR at %d:%d: Unexpected end of input.\n",
					tokens[index - 1].end.line, tokens[index - 1].end.column);
			return false;
		} else if (tokens[index].type == GRAMMAR_RIGHT_BRACE) {
			index++; break;
		} else if (tokens[index].type == GRAMMAR_COMMA) {
			index++;
		} else {
			fprintf(stderr, "ERROR at %d:%d: Unexpected token ",
					tokens[index].start.line, tokens[index].start.column);
			print(tokens[index].type, stderr);
			fprintf(stderr, ". Expected a comma or closing brace.\n");
			return false;
		}
	}

	if (length < fixed_length) {
		fprintf(stderr, "ERROR at %d:%d: Too few entries in list.\n",
				tokens[index - 1].end.line, tokens[index - 1].end.column);
		return false;
	}

	return true;
}

template<typename T, typename SizeType,
	typename std::enable_if<std::is_integral<SizeType>::value>::type* = nullptr>
inline bool read_list(
		const array<grammar_token>& tokens, unsigned int& index,
		T*& list, SizeType& length, SizeType& capacity)
{
	/* check if the list is empty */
	if (index < tokens.length && tokens[index].type == GRAMMAR_RIGHT_BRACE) {
		index++;
		return true;
	}

	while (true) {
		if (!ensure_capacity(list, capacity, length + 1)) {
			fprintf(stderr, "read_list ERROR: Unable to expand list.\n");
			return false;
		}
		if (!read_list_item(tokens, index, list[length]))
			return false;
		index++; length++;

		if (index == tokens.length) {
			fprintf(stderr, "ERROR at %d:%d: Unexpected end of input.\n",
					tokens[index - 1].end.line, tokens[index - 1].end.column);
			return false;
		} else if (tokens[index].type == GRAMMAR_RIGHT_BRACE) {
			index++; break;
		} else if (tokens[index].type == GRAMMAR_COMMA) {
			index++;
		} else {
			fprintf(stderr, "ERROR at %d:%d: Unexpected token ",
					tokens[index].start.line, tokens[index].start.column);
			print(tokens[index].type, stderr);
			fprintf(stderr, ". Expected a comma or closing brace.\n");
			return false;
		}
	}

	return true;
}

template<typename Semantics, typename SizeType,
	typename std::enable_if<std::is_integral<SizeType>::value>::type* = nullptr>
inline bool read_feature_list(
		const array<grammar_token>& tokens, unsigned int& index,
		typename Semantics::feature*& list, SizeType& length, SizeType& capacity)
{
	/* check if the list is empty */
	if (index < tokens.length && tokens[index].type == GRAMMAR_RIGHT_BRACE) {
		index++;
		return true;
	}

	while (true) {
		if (!ensure_capacity(list, capacity, length + 1)) {
			fprintf(stderr, "read_feature_list ERROR: Unable to expand list.\n");
			return false;
		}
		if (!read_feature_list_item<Semantics>(tokens, index, list[length]))
			return false;
		index++; length++;

		if (index == tokens.length) {
			fprintf(stderr, "ERROR at %d:%d: Unexpected end of input.\n",
					tokens[index - 1].end.line, tokens[index - 1].end.column);
			return false;
		} else if (tokens[index].type == GRAMMAR_RIGHT_BRACE) {
			index++; break;
		} else if (tokens[index].type == GRAMMAR_COMMA) {
			index++;
		} else {
			fprintf(stderr, "ERROR at %d:%d: Unexpected token ",
					tokens[index].start.line, tokens[index].start.column);
			print(tokens[index].type, stderr);
			fprintf(stderr, ". Expected a comma or closing brace.\n");
			return false;
		}
	}

	return true;
}

template<typename RulePrior, typename Semantics>
inline void free_nonterminal(
		nonterminal<Semantics, hdp_rule_distribution<RulePrior, Semantics>>& N,
		typename Semantics::feature* features = NULL, double* a = NULL, double* b = NULL)
{
	if (a != NULL) free(a);
	if (b != NULL) free(b);
	if (features != NULL) free(features);
	free(N.name);
}

template<typename T>
inline void free_array(array<T>& items) {
	for (unsigned int i = 0; i < items.length; i++)
		free(items[i]);
}

template<typename V>
inline bool parse(token_distribution<V>& prior,
		const array<grammar_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names)
{
	array<string> excluded = array<string>(16);
	if (!expect_token(tokens, index, GRAMMAR_LEFT_BRACE, "left-brace for list of excluded tokens"))
		return false;
	index++;
	if (!read_list(tokens, index, excluded.data, excluded.length, excluded.capacity))
		return false;

	unsigned int atom_count;
	if (!expect_token(tokens, index, GRAMMAR_FLOAT,
			"an integer indicating the number of atoms")
	 || !parse_uint(tokens[index].text, atom_count)
	 || !init(prior, atom_count))
		return false;
	index++;

	unsigned int id;
	for (const string& token : excluded) {
		if (!get_token(token, id, names)
		 || !prior.set(id, 0.0))
		{
			free_array(excluded);
			free(prior);
			return false;
		}
	}
	free_array(excluded);
	return true;
}

template<typename ElementDistribution>
inline bool parse(sequence_distribution<ElementDistribution>& prior,
		const array<grammar_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names)
{
	if (!parse(prior.element_distribution, tokens, index, names))
		return false;
	if (!expect_token(tokens, index, GRAMMAR_FLOAT, "floating-point value"
			" indicating the end probability of the sequence_distribution")
	 || !parse_float(tokens[index].text, prior.end_probability))
	{
		free(prior.element_distribution);
		return false;
	}
	index++;
	prior.log_end_probability = log(prior.end_probability);
	prior.log_not_end_probability = log(1.0 - prior.end_probability);
	return true;
}

template<typename RulePrior>
inline bool parse(terminal_prior<RulePrior>& prior,
		const array<grammar_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names)
{
	if (!parse(prior.prior, tokens, index, names))
		return false;

	prior.pos = POS_OTHER;
	if (index < tokens.length && tokens[index].type == GRAMMAR_IDENTIFIER) {
		/* this preterminal has a part of speech specification */
		if (tokens[index].text == "verb") {
			prior.pos = POS_VERB;
		} else if (tokens[index].text == "noun") {
			prior.pos = POS_NOUN;
		} else if (tokens[index].text == "adjective") {
			prior.pos = POS_ADJECTIVE;
		} else if (tokens[index].text == "adverb") {
			prior.pos = POS_ADVERB;
		} else {
			read_error("Unrecognized part of speech specification", tokens[index].start);
			return false;
		}
		index++;
	}

	array<string> excluded = array<string>(16);
	if (!expect_token(tokens, index, GRAMMAR_LEFT_BRACE, "left-brace for list of excluded tokens")) {
		free(prior.prior);
		return false;
	}
	index++;
	if (!read_list(tokens, index, excluded.data, excluded.length, excluded.capacity)) {
		free(prior.prior);
		return false;
	}

	sequence& seq = *((sequence*) alloca(sizeof(sequence)));
	if (!hash_set_init(prior.excluded, 8)) {
		free(prior.prior); free_array(excluded);
		return false;
	}
	for (const string& str : excluded) {
		/* tokenize the string */
		array<unsigned int> tokens = array<unsigned int>(4);
		if (!tokenize(str.data, str.length, tokens, names)) {
			free(prior); free_array(excluded);
			return false;
		}

		if (!init(seq, tokens.length)) {
			free(prior); free_array(excluded);
			return false;
		}
		memcpy(seq.tokens, tokens.data, sizeof(unsigned int) * tokens.length);
		if (!prior.excluded.add(seq)) {
			free(seq); free(prior); free_array(excluded);
			return false;
		}
		free(seq);
	}
	free_array(excluded);
	return true;
}

template<typename RulePrior, typename Semantics>
inline bool parse(rule_list_prior<RulePrior, Semantics>& prior,
		const array<grammar_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names)
{
	if (!hash_map_init(prior.rules, 4))
		return false;
	if (!parse(prior.backoff_prior, tokens, index, names)) {
		free(prior.rules);
		return false;
	}
	return true;
}

template<nonterminal_type Type, typename RulePrior, typename Semantics>
inline bool read_nonterminal(const array<grammar_token>& tokens,
		unsigned int& index, hdp_grammar<RulePrior, Semantics>& G,
		const grammar_token& identifier, hash_map<string, unsigned int>& names)
{
	if (!G.nonterminals.ensure_capacity(G.nonterminals.length + 1)
	 || !init(G.nonterminals[G.nonterminals.length],
			 identifier.text, G.nonterminals.length + 1))
		return false;
	auto& new_nonterminal = G.nonterminals[G.nonterminals.length];

	/* parse the list of features */
	unsigned int feature_count = 0, feature_capacity = 4;
	typename Semantics::feature* features = (typename Semantics::feature*) malloc(sizeof(typename Semantics::feature) * feature_capacity);
	if (!expect_token(tokens, index, GRAMMAR_LEFT_BRACE, "left-brace for declaration of feature list")) {
		free_nonterminal(new_nonterminal, features); return false;
	}
	index++;
	if (!read_feature_list<Semantics>(tokens, index, features, feature_count, feature_capacity)) {
		free_nonterminal(new_nonterminal, features); return false;
	}
	if (feature_count == 0) {
		free(features);
		features = NULL;
		feature_capacity = 0;
	} else {
		resize(features, feature_count);
	}

	/* parse the prior parameters for alpha in the HDP */
	unsigned int depth = feature_count + 1;
	double* a = (double*) malloc(sizeof(double) * depth);
	double* b = (double*) malloc(sizeof(double) * depth);
	if (a == NULL || b == NULL) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}
	if (!expect_token(tokens, index, GRAMMAR_LEFT_BRACE, "left-brace for list of 'a' parameters")) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}
	index++;
	if (!read_list(tokens, index, a, depth)) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}

	if (!expect_token(tokens, index, GRAMMAR_LEFT_BRACE, "left-brace for list of 'b' parameters")) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}
	index++;
	if (!read_list(tokens, index, b, depth)) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}

	/* parse the prior distribution on production rules and construct the HDP */
	RulePrior& prior = *((RulePrior*) alloca(sizeof(RulePrior)));
	if (!parse(prior, tokens, index, names)
	 || !init(new_nonterminal.rule_distribution, Type, prior, features, a, b, feature_count)) {
		free_nonterminal(new_nonterminal, features, a, b); return false;
	}
	free(prior); free(a); free(b); free(features);
	G.nonterminals.length++;
	return true;
}

template<typename RulePrior, typename Semantics>
bool read_nonterminal(hdp_grammar<RulePrior, Semantics>& G,
		const array<grammar_token>& tokens,
		unsigned int& index, const grammar_token& identifier,
		hash_map<string, unsigned int>& names)
{
	grammar_token_type type = tokens[index].type;
	index++;

	/* parse the type of the declared nonterminal */
	switch (type) {
	case GRAMMAR_KEYWORD_NONTERMINAL:
		return read_nonterminal<NONTERMINAL>(tokens, index, G, identifier, names);
	case GRAMMAR_KEYWORD_PRETERMINAL:
		return read_nonterminal<PRETERMINAL>(tokens, index, G, identifier, names);
	case GRAMMAR_KEYWORD_PRETERMINAL_NUMBER:
		return read_nonterminal<PRETERMINAL_NUMBER>(tokens, index, G, identifier, names);
	case GRAMMAR_KEYWORD_PRETERMINAL_STRING:
		return read_nonterminal<PRETERMINAL_STRING>(tokens, index, G, identifier, names);
	default:
		read_error("Unexpected token in nonterminal declaration."
				" Expected a nonterminal type identifier", tokens[index].start);
		fprintf(stderr, "  Nonterminal identifier is '"); print(identifier.text, stderr); fprintf(stderr, "'.\n");
		return false;
	}
}

inline bool emit_preterminal_token(
		array<unsigned int>& preterminal_tokens,
		string& token, hash_map<string, unsigned int>& names)
{
	unsigned int id;
	if (!get_token(token, id, names))
		return false;

	return preterminal_tokens.add(id);
}

inline bool read_string(const string& src,
		array<unsigned int>& preterminal_tokens,
		hash_map<string, unsigned int>& names)
{
	bool whitespace_state = true;
	unsigned int token_start = 0;
	string& token = *((string*) alloca(sizeof(string)));
	for (unsigned int i = 0; i < src.length; i++) {
		if (src.data[i] == ' ') {
			if (!whitespace_state) {
				token.data = src.data + token_start;
				token.length = i - token_start;
				if (!emit_preterminal_token(preterminal_tokens, token, names))
					return false;
				whitespace_state = true;
			}
		} else {
			if (whitespace_state) {
				whitespace_state = false;
				token_start = i;
			}
		}
	}

	if (!whitespace_state) {
		token.data = src.data + token_start;
		token.length = src.length - token_start;
		if (!emit_preterminal_token(preterminal_tokens, token, names))
			return false;
	}
	return true;
}

bool read_preterminal_rule(
		const array<grammar_token>& tokens,
		unsigned int& index,
		array<unsigned int>& preterminal_tokens,
		hash_map<string, unsigned int>& names)
{
	if (!expect_token(tokens, index, GRAMMAR_IDENTIFIER, "right-hand side string"))
		return false;
	const string& src = tokens[index].text;
	if (!read_string(src, preterminal_tokens, names))
		return false;
	index++;
	return true;
}

template<typename Semantics, typename TokenType, TokenType ColonToken, TokenType CommaToken, TokenType IdentifierToken>
bool read_transformation(const array<lexical_token<TokenType>>& tokens,
		unsigned int& index, transformation<Semantics>& t)
{
	typedef typename Semantics::function function;
	array<function>& functions = *((array<function>*) alloca(sizeof(array<function>)));
	if (!array_init(functions, 4)) return false;
	if (index < tokens.length && tokens[index].type == ColonToken) {
		index++;
		while (true) {
			if (!functions.ensure_capacity(functions.length + 1)) {
				free(functions);
				return false;
			}

			if (!expect_token(tokens, index, IdentifierToken, "semantic transformation function in right-hand side token")) {
				free(functions);
				return false;
			}
			const lexical_token<TokenType>& transform = tokens[index];
			index++;

			if (!Semantics::interpret(functions[functions.length], transform.text)) {
				fprintf(stderr, "ERROR at %u:%u: Unrecognized semantic transform '",
						transform.start.line, transform.start.column);
				print(transform.text, stderr);
				fprintf(stderr, "'.\n");
				free(functions); return false;
			}
			functions.length++;

			if (index >= tokens.length || tokens[index].type != CommaToken)
				break;
			index++;
		}
	}

	if (functions.length == 0)
		functions[functions.length++] = Semantics::default_function();

	t.functions = functions.data;
	t.function_count = functions.length;
	return true;
}

template<typename RulePrior, typename Semantics>
bool read_rule(const hdp_grammar<RulePrior, Semantics>& G,
		const array<grammar_token>& tokens,
		unsigned int& index, array<unsigned int>& nonterminals,
		array<transformation<Semantics>>& transformations, double& prior)
{
	bool contains;
	while (true) {
		/* first ensure the rule is large enough */
		if (!nonterminals.ensure_capacity(nonterminals.length + 1)
		 || !transformations.ensure_capacity(transformations.length + 1))
			return false;

		if (!expect_token(tokens, index, GRAMMAR_IDENTIFIER, "right-hand side nonterminal symbol"))
			return false;
		unsigned int id = G.nonterminal_names.get(tokens[index].text, contains);
		if (!contains) {
			fprintf(stderr, "ERROR at %d:%d: Undefined nonterminal '", tokens[index].start.line, tokens[index].start.column);
			print(tokens[index].text, stderr); print("'.\n", stderr);
			return false;
		}
		index++;

		nonterminals[nonterminals.length++] = id;
		if (!read_transformation<Semantics, grammar_token_type, GRAMMAR_COLON, GRAMMAR_COMMA, GRAMMAR_IDENTIFIER>(tokens, index, transformations[transformations.length]))
			return false;
		transformations.length++;

		/* check for the end of the statement */
		if (index == tokens.length) {
			break;
		} else if (tokens[index].type == GRAMMAR_END_STATEMENT) {
			index++;
			break;
		} else if (tokens[index].type == GRAMMAR_FLOAT) {
			/* read the prior probability associated with this rule */
			if (!parse_float(tokens[index].text, prior)) return false;
			index++;

			if (index == tokens.length) {
				break;
			} else if (!expect_token(tokens, index, GRAMMAR_END_STATEMENT, "end of rule after prior probability"))
				return false;
			index++;
			break;
		}
	}
	return true;
}

template<typename RulePrior, typename Semantics>
bool read_rule(
		hdp_grammar<RulePrior, Semantics>& G,
		const array<grammar_token>& tokens,
		unsigned int& index, unsigned int left,
		hash_map<string, unsigned int>& names)
{
	auto& N = G.nonterminals[left - 1];

	double prior = 0.0;
	array<unsigned int> nonterminals(4);
	if (N.rule_distribution.type == NONTERMINAL) {
		array<transformation<Semantics>> transformations(4);
		if (!read_rule(G, tokens, index, nonterminals, transformations, prior)) {
			for (transformation<Semantics>& t : transformations) core::free(t);
			return false;
		}

		rule<Semantics>& new_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
		new_rule.type = rule_type::NONTERMINAL;
		new_rule.nt.length = nonterminals.length;
		new_rule.nt.nonterminals = nonterminals.data;
		new_rule.nt.transformations = transformations.data;
		bool result = add_rule(N.rule_distribution, new_rule, prior);
		for (transformation<Semantics>& t : transformations) core::free(t);
		return result;
	} else {
		if (!read_preterminal_rule(tokens, index, nonterminals, names))
			return false;

		rule<Semantics>& new_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
		new_rule.type = rule_type::TERMINAL;
		new_rule.t.terminals = nonterminals.data;
		new_rule.t.length = nonterminals.length;
		new_rule.t.inflected = nullptr;
		new_rule.t.inflected_length = 0;
		return add_rule(N.rule_distribution, new_rule, prior);
	}
}

template<typename RulePrior, typename Semantics>
bool read_rule(
		hdp_grammar<RulePrior, Semantics>& G,
		const array<grammar_token>& tokens,
		unsigned int& index, const grammar_token& identifier,
		hash_map<string, unsigned int>& names)
{
	bool contains;
	unsigned int nonterminal = G.nonterminal_names.get(identifier.text, contains);
	if (!contains) {
		read_error("Undefined left-hand side nonterminal symbol", identifier.start);
		return false;
	}

	/* add the rule to the appropriate nonterminal */
	if (!read_rule(G, tokens, index, nonterminal, names)) {
		read_error("Unable to read rule", identifier.start);
		return false;
	}
	return true;
}

void eat_line(const array<grammar_token>& tokens, unsigned int& index) {
	while (index < tokens.length && tokens[index].type != GRAMMAR_END_STATEMENT)
		index++;
	index++;
}

template<bool FirstPass, typename RulePrior, typename Semantics>
bool read_statement(hdp_grammar<RulePrior, Semantics>& G,
		const array<grammar_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names)
{
	if (index == tokens.length) {
		fprintf(stderr, "ERROR: Unexpected end of input.\n");
		return false;
	} else if (tokens[index].type == GRAMMAR_END_STATEMENT) {
		index++;
		return true;
	} else if (FirstPass && tokens[index].type != GRAMMAR_IDENTIFIER) {
		fprintf(stderr, "ERROR at %u:%u: Expected an identifier.\n",
				tokens[index].start.line, tokens[index].start.column);
		return false;
	}
	const grammar_token& identifier = tokens[index];
	index++;

	if (index == tokens.length) {
		fprintf(stderr, "ERROR: Unexpected end of input.\n");
		return false;
	} else if (tokens[index].type == GRAMMAR_KEYWORD_ARROW) {
		/* this statement is a rule */
		index++;
		if (FirstPass) {
			eat_line(tokens, index);
			return true;
		}
		return read_rule(G, tokens, index, identifier, names);
	} else {
		if (!FirstPass) {
			eat_line(tokens, index);
			return true;
		}

		/* this statement is a nonterminal declaration */
		return read_nonterminal(G, tokens, index, identifier, names);
	}
}

template<typename RulePrior, typename Semantics>
bool read(hdp_grammar<RulePrior, Semantics>& G,
		const char* input, unsigned int length,
		hash_map<string, unsigned int>& names)
{
	array<grammar_token> tokens = array<grammar_token>(256);
	if (!grammar_lex(tokens, input, length)) {
		free_tokens(tokens);
		return false;
	} else if (tokens.last().type != GRAMMAR_END_STATEMENT
	 && !emit_token(tokens, tokens.last().end, tokens.last().end, GRAMMAR_END_STATEMENT)) {
		free_tokens(tokens);
		return false;
	}

	/* first pass to parse nonterminal declarations */
	unsigned int index = 0;
	while (index < tokens.length) {
		if (!read_statement<true>(G, tokens, index, names)) {
			free_tokens(tokens);
			return false;
		}
	}
	if (!G.compute_nonterminal_names()) {
		free_tokens(tokens);
		return false;
	}

	/* second pass to parse rules */
	index = 0;
	while (index < tokens.length) {
		if (!read_statement<false>(G, tokens, index, names)) {
			free_tokens(tokens);
			return false;
		}
	}

	/* finish initializing the rule prior distributions */
	for (auto& N : G.nonterminals)
		N.rule_distribution.h.pi.finish();

	/* free everything */
	free_tokens(tokens);
	return true;
}

template<typename RulePrior, typename Semantics>
bool read_grammar(
		hdp_grammar<RulePrior, Semantics>& G,
		hash_map<string, unsigned int>& names,
		const char* grammar_filepath)
{
	/* read the grammar from file */
	size_t bytes_read;
	char* grammar_src = read_file<false>(grammar_filepath, bytes_read);
	if (grammar_src == NULL) {
		fprintf(stderr, "ERROR: Unable to read file '%s'.\n", grammar_filepath);
		return false;
	}

	/* interpret and construct the grammar */
	if (!read(G, grammar_src, bytes_read, names)) {
		free(grammar_src);
		return false;
	}
	free(grammar_src);
	return true;
}


/**
 * Code for tokenizing/lexing derivation trees.
 */

enum class derivation_token_type {
	LPAREN,
	RPAREN,
	TOKEN,
	COLON,
	COMMA,
	SLASH,
	STRING
};

typedef lexical_token<derivation_token_type> derivation_token;

template<typename Stream>
inline bool print(derivation_token_type type, Stream& stream) {
	switch (type) {
	case derivation_token_type::LPAREN:
		return print('(', stream);
	case derivation_token_type::RPAREN:
		return print(')', stream);
	case derivation_token_type::COLON:
		return print(':', stream);
	case derivation_token_type::COMMA:
		return print(',', stream);
	case derivation_token_type::SLASH:
		return print('/', stream);
	case derivation_token_type::TOKEN:
		return print("TOKEN", stream);
	case derivation_token_type::STRING:
		return print("STRING", stream);
	}
	fprintf(stderr, "print ERROR: Unknown derivation_token_type.\n");
	return false;
}

enum class derivation_lexer_state {
	DEFAULT,
	TOKEN,
	STRING,
	COMMENT
};

bool derivation_emit_symbol(array<derivation_token>& tokens, const position& start, char symbol) {
	switch (symbol) {
	case '(':
		return emit_token(tokens, start, start + 1, derivation_token_type::LPAREN);
	case ')':
		return emit_token(tokens, start, start + 1, derivation_token_type::RPAREN);
	case ':':
		return emit_token(tokens, start, start + 1, derivation_token_type::COLON);
	case ',':
		return emit_token(tokens, start, start + 1, derivation_token_type::COMMA);
	case '/':
		return emit_token(tokens, start, start + 1, derivation_token_type::SLASH);
	default:
		fprintf(stderr, "derivation_emit_symbol ERROR: Unexpected symbol.\n");
		return false;
	}
}

template<typename Stream>
bool derivation_lex(array<derivation_token>& tokens,
		Stream& input, position start = position(1, 1))
{
	position current = start;
	derivation_lexer_state state = derivation_lexer_state::DEFAULT;
	array<char> token = array<char>(1024);

	std::mbstate_t shift = {0};
	wint_t next = fgetwc(input);
	bool new_line = false;
	while (next != WEOF) {
		switch (state) {
		case derivation_lexer_state::TOKEN:
			if (next == '(' || next == ')' || next == ':' || next == ',' || next == '/') {
				if (!emit_token(tokens, token, start, current, derivation_token_type::TOKEN)
				 || !derivation_emit_symbol(tokens, current, next))
					return false;
				state = derivation_lexer_state::DEFAULT;
				token.clear(); shift = {0};
			} else if (next == '"') {
				if (!emit_token(tokens, token, start, current, derivation_token_type::TOKEN))
					return false;
				state = derivation_lexer_state::STRING;
				token.clear(); shift = {0};
				start = current;
			} else if (next == '#') {
				if (!emit_token(tokens, token, start, current, derivation_token_type::TOKEN))
					return false;
				state = derivation_lexer_state::COMMENT;
				token.clear(); shift = {0};
			} else if (next == ' ' || next == '\t' || next == '\n' || next == '\r') {
				if (!emit_token(tokens, token, start, current, derivation_token_type::TOKEN))
					return false;
				state = derivation_lexer_state::DEFAULT;
				token.clear(); shift = {0};
				new_line = (next == '\n');
			} else {
				if (!append_to_token(token, next, shift)) return false;
			}
			break;

		case derivation_lexer_state::STRING:
			if (next == '"') {
				if (!emit_token(tokens, token, start, current, derivation_token_type::STRING))
					return false;
				state = derivation_lexer_state::DEFAULT;
			} else {
				if (!append_to_token(token, next, shift)) return false;
				new_line = (next == '\n');
			}
			break;

		case derivation_lexer_state::COMMENT:
			if (next == '\n') {
				state = derivation_lexer_state::DEFAULT;
				new_line = true;
			}
			break;

		case derivation_lexer_state::DEFAULT:
			if (next == '(' || next == ')' || next == ':' || next == ',' || next == '/') {
				if (!derivation_emit_symbol(tokens, current, next))
					return false;
			} else if (next == '"') {
				state = derivation_lexer_state::STRING;
				token.clear(); shift = {0};
				start = current;
			} else if (next == '#') {
				state = derivation_lexer_state::COMMENT;
				token.clear(); shift = {0};
			} else if (next == ' ' || next == '\t' || next == '\n' || next == '\r') {
				new_line = (next == '\n');
			} else {
				if (!append_to_token(token, next, shift)) return false;
				state = derivation_lexer_state::TOKEN;
				start = current;
			}
			break;
		}

		if (new_line) {
			current.line++;
			current.column = 1;
			new_line = false;
		} else current.column++;
		next = fgetwc(input);
	}

	if (state == derivation_lexer_state::TOKEN)
		return emit_token(tokens, token, start, current, derivation_token_type::TOKEN);
	return true;
}


/**
 * Recursive-descent parser for derivation trees.
 */

template<typename Semantics>
bool derivation_interpret(unsigned int& root_nonterminal,
		transformation<Semantics>& root_transform, syntax_node<Semantics>*& node,
		array<derivation_token>& tokens, unsigned int& index,
		hash_map<string, unsigned int>& names,
		const hash_map<string, unsigned int>& nonterminal_names)
{
	bool contains;
	if (!expect_token(tokens, index, derivation_token_type::LPAREN, "left parenthesis of derivation tree node"))
		return false;
	index++;
	if (!expect_token(tokens, index, derivation_token_type::TOKEN, "nonterminal"))
		return false;
	root_nonterminal = nonterminal_names.get(tokens[index].text, contains);
	if (!contains) {
		fprintf(stderr, "ERROR at %d:%d: Undefined nonterminal '", tokens[index].start.line, tokens[index].start.column);
		print(tokens[index].text, stderr); print("'.\n", stderr);
		return false;
	}
	index++;

	/* check if there is a transformation label */
	if (!read_transformation<Semantics, derivation_token_type, derivation_token_type::COLON, derivation_token_type::COMMA, derivation_token_type::TOKEN>(tokens, index, root_transform))
		return false;

	/* check if this is a preterminal rule */
	if (index == tokens.length) {
		fprintf(stderr, "ERROR at %d:%d: Unexpected end of input.\n",
				tokens[index - 1].end.line, tokens[index - 1].end.column);
		free(root_transform);
		return false;
	} else if (tokens[index].type == derivation_token_type::STRING) {
		/* this is a preterminal rule */
		array<unsigned int> terminals(4);
		if (!read_string(tokens[index].text, terminals, names))
			return false;
		index++;

		rule<Semantics>& new_rule = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
		new_rule.type = rule_type::TERMINAL;
		new_rule.t.terminals = terminals.data;
		new_rule.t.length = terminals.length;
		new_rule.t.inflected = nullptr;
		new_rule.t.inflected_length = 0;

		array<unsigned int> inflected(4);
		if (index < tokens.length && tokens[index].type == derivation_token_type::SLASH) {
			index++;
			if (!expect_token(tokens, index, derivation_token_type::STRING, "inflected form string following slash"))
				return false;
			if (!read_string(tokens[index].text, inflected, names))
				return false;
			index++;

			new_rule.t.inflected = inflected.data;
			new_rule.t.inflected_length = inflected.length;
		}

		node = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
		if (node == nullptr) {
			free(root_transform);
			return false;
		} else if (!init(*node, new_rule)) {
			free(root_transform); free(node);
			return false;
		}

		if (!expect_token(tokens, index, derivation_token_type::RPAREN, "right parenthesis of terminal node"))
			return false;
		index++;
		return true;

	} else if (tokens[index].type == derivation_token_type::LPAREN) {
		array<unsigned int> child_nonterminals(4);
		array<transformation<Semantics>> child_transforms(4);
		array<syntax_node<Semantics>*> child_nodes(4);
		while (true) {
			if (!derivation_interpret(child_nonterminals[child_nonterminals.length], child_transforms[child_transforms.length], child_nodes[child_nodes.length], tokens, index, names, nonterminal_names)) {
				for (transformation<Semantics>& transform : child_transforms) free(transform);
				for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
				free(root_transform);
				return false;
			}
			child_nonterminals.length++;
			child_transforms.length++;
			child_nodes.length++;

			if (index == tokens.length) {
				fprintf(stderr, "ERROR at %d:%d: Unexpected end of input. "
						"Expected right parenthesis of derivation tree node.\n",
						tokens[index - 1].end.line, tokens[index - 1].end.column);
				for (transformation<Semantics>& transform : child_transforms) free(transform);
				for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
				free(root_transform);
				return false;
			} else if (tokens[index].type == derivation_token_type::RPAREN) {
				index++;
				break;
			} else if (!child_nonterminals.ensure_capacity(child_nonterminals.length + 1)
					|| !child_transforms.ensure_capacity(child_transforms.length + 1)
					|| !child_nodes.ensure_capacity(child_nodes.length + 1))
			{
				for (transformation<Semantics>& transform : child_transforms) free(transform);
				for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
				free(root_transform);
				return false;
			}
		}

		/* we finished reading all the child nodes */
		rule<Semantics>& r = *((rule<Semantics>*) alloca(sizeof(rule<Semantics>)));
		r.type = rule_type::NONTERMINAL;
		r.nt.nonterminals = (unsigned int*) malloc(1);
		r.nt.transformations = (transformation<Semantics>*) malloc(1);
		r.nt.length = child_nodes.length;
		if (r.nt.nonterminals == nullptr || r.nt.transformations == nullptr) {
			fprintf(stderr, "derivation_interpret ERROR: Out of memory.\n");
			if (r.nt.nonterminals != nullptr) free(r.nt.nonterminals);
			for (transformation<Semantics>& transform : child_transforms) free(transform);
			for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
			free(root_transform);
			return false;
		}
		swap(r.nt.nonterminals, child_nonterminals.data);
		swap(r.nt.transformations, child_transforms.data);

		syntax_node<Semantics>* new_node = (syntax_node<Semantics>*) malloc(sizeof(syntax_node<Semantics>));
		if (new_node == nullptr) {
			fprintf(stderr, "derivation_interpret ERROR: Out of memory.\n");
			for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
			free(r); free(root_transform);
			return false;
		} else if (!init(*new_node, r)) {
			for (syntax_node<Semantics>* node : child_nodes) { free(*node); if (node->reference_count == 0) free(node); }
			free(r); free(root_transform); free(new_node);
			return false;
		}
		swap(new_node->children, child_nodes.data);
		free(r);
		node = new_node;
		return true;

	} else {
		fprintf(stderr, "ERROR at %d:%d: Unexpected symbol. Expected a "
				"terminal or a left parenthesis of a child derivation tree node.\n",
				tokens[index - 1].end.line, tokens[index - 1].end.column);
		free(root_transform);
		return false;
	}
}

template<typename Stream, typename Semantics>
inline bool parse(Stream& in,
		syntax_node<Semantics>*& derivation,
		unsigned int& root_nonterminal,
		hash_map<string, unsigned int>& names,
		const hash_map<string, unsigned int>& nonterminal_names,
		position start = position(1, 1))
{
	array<derivation_token> tokens = array<derivation_token>(128);
	if (!derivation_lex(tokens, in, start)) {
		read_error("Unable to parse derivation tree (lexical analysis failed)", start);
		free_tokens(tokens); return false;
	}

	unsigned int index = 0;
	transformation<Semantics> root_transform;
	if (!derivation_interpret(root_nonterminal, root_transform, derivation, tokens, index, names, nonterminal_names)) {
		read_error("Unable to parse derivation tree", start);
		free_tokens(tokens); return false;
	}
	free_tokens(tokens);

	if (root_transform.function_count != 1 || root_transform.functions[0] != Semantics::default_function())
		fprintf(stderr, "WARNING at %d:%d: Unexpected transformation label at root of derivation tree.\n", start.line, start.column);
	free(root_transform);
	return true;
}

template<typename Stream, typename Semantics>
inline bool parse(Stream& in,
		rooted_syntax_node<Semantics>& derivation,
		hash_map<string, unsigned int>& names,
		const hash_map<string, unsigned int>& nonterminal_names,
		position start = position(1, 1))
{
	return parse(in, derivation.tree, derivation.root, names, nonterminal_names, start);
}

#endif /* HDP_GRAMMAR_IO_H_ */
