/**
 * pcfg_induction.cpp
 *
 *  Created on: Jun 24, 2016
 *      Author: asaparov
 */

#include "parser.h"
#include "pcfg_grammar.h"

/* simple grammar where each zero must be paired with a one on the right */
string sentences[] = {
	"01",
	"000111",
	"00001111",
	"0011",
	"0000011111",
	"0101",
	"001101",
	"001011",
	"00011011",
	"010011",
	"001101",
	"010101",
	"00100111",
	"010011",
	"00110011",
	"000111",
	"0011",
	"0011001101",
	"01001101",
	"0101010101",
	"0001110011",
	"0011000111"
};

constexpr unsigned int sentence_count = (unsigned int) array_length(sentences);

char characters[] = { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '+', '-', '(', ')' };
hash_map<char, unsigned int> inverse_characters =
	hash_map<char, unsigned int>(characters, (unsigned int) array_length(characters));

inline unsigned int char_to_id(char c) {
	bool contains;
	unsigned int id = inverse_characters.get(c, contains);
	if (!contains) {
		fprintf(stderr, "char_to_id ERROR: Unrecognized character.\n");
		exit(EXIT_FAILURE);
	}
	return id;
}

struct character_printer { };

template<typename Stream>
inline bool print(unsigned int id, Stream& out, const character_printer& printer) {
	if (id >= array_length(characters)) {
		fprintf(stderr, "print ERROR: Unrecognized character id.\n");
		return false;
	}
	return print(characters[id], out);
}

void free_sequences(sequence* sequences, unsigned int count = sentence_count) {
	for (unsigned int i = 0; i < count; i++)
		free(sequences[i].tokens);
	free(sequences);
}

sequence* sentences_to_ids() {
	sequence* sequences = (sequence*) malloc(sizeof(sequence) * sentence_count);
	if (sequences == NULL) {
		fprintf(stderr, "sentences_to_ids ERROR: Out of memory.\n");
		return NULL;
	}

	for (unsigned int i = 0; i < sentence_count; i++) {
		sequences[i].length = sentences[i].length;
		sequences[i].tokens = (unsigned int*) malloc(sizeof(unsigned int) * sentences[i].length);
		if (sequences[i].tokens == NULL) {
			fprintf(stderr, "sentences_to_ids ERROR: Insufficient memory to convert sentence %u.\n", i);
			free_sequences(sequences, i); free(sequences);
			return NULL;
		}

		for (unsigned int j = 0; j < sentences[i].length; j++)
			sequences[i].tokens[j] = char_to_id(sentences[i][j]);
	}
	return sequences;
}

unsigned int initialize_preterminal(const sequence& terminal) {
	return (terminal.tokens[0] + 1) * 2;
}

unsigned int random_nonterminal(unsigned int nonterminal_count) {
	return rand() % (nonterminal_count / 2) * 2 + 1;
}

bool initialize_tree(
	syntax_node<null_semantics>*& tree,
	const sequence& sentence,
	unsigned int nonterminal_count)
{
	tree = (syntax_node<null_semantics>*) malloc(sizeof(syntax_node<null_semantics>));
	if (tree == NULL) {
		return false;
	}
	/* is this a terminal? */
	if (sentence.length == 1) {
		if (!init(*tree, sentence)) {
			free(tree);
			return false;
		}
		return true;
	}

	/* pick a random split point from {1, ..., n - 1} */
	unsigned int k = rand() % (sentence.length - 1) + 1;

	rule<null_semantics>& branch = *((rule<null_semantics>*) alloca(sizeof(rule<null_semantics>)));
	branch.type = rule_type::NONTERMINAL;
	branch.nt.length = 2;
	branch.nt.transformations = (transformation<null_semantics>*) malloc(sizeof(transformation<null_semantics>) * branch.nt.length);
	branch.nt.nonterminals = (unsigned int*) malloc(sizeof(unsigned int) * branch.nt.length);
	branch.nt.transformations[0].function_count = 1;
	branch.nt.transformations[0].functions = (null_semantics::function*) malloc(sizeof(null_semantics::function) * branch.nt.transformations[0].function_count);
	branch.nt.transformations[0].functions[0] = null_semantics::FUNCTION_IDENTITY;
	branch.nt.transformations[1].function_count = 1;
	branch.nt.transformations[1].functions = (null_semantics::function*) malloc(sizeof(null_semantics::function) * branch.nt.transformations[1].function_count);
	branch.nt.transformations[1].functions[0] = null_semantics::FUNCTION_IDENTITY;
	branch.nt.nonterminals[0] = (k == 1)
		? initialize_preterminal({sentence.tokens, k})
		: random_nonterminal(nonterminal_count);
	branch.nt.nonterminals[1] = ((sentence.length - k) == 1)
		? initialize_preterminal({sentence.tokens + k, sentence.length - k})
		: random_nonterminal(nonterminal_count);

	bool result = init(*tree, branch)
	 		   && initialize_tree(tree->children[0], {sentence.tokens, k}, nonterminal_count)
			   && initialize_tree(tree->children[1], {sentence.tokens + k, sentence.length - k}, nonterminal_count);
	free(branch);
	return result;
}

template<bool Complete = false>
constexpr double log_probability(const null_semantics& logical_form) {
	return 0.0;
}

int main(int argc, const char** argv)
{
	FILE* out = stdout;
	constexpr double nonterminal_alpha = 0.1;
	constexpr double preterminal_alpha = 1.0e-16;
	constexpr unsigned int nonterminal_count = 4;

	pcfg_grammar<symmetric_dirichlet<double>, dense_categorical<double>, null_semantics> G;
	for (unsigned int i = 0; i < nonterminal_count; i++) {
		G.nonterminals[i].id = i + 1;
		G.nonterminals[i].name = "";

		bool is_preterminal = (i % 2 == 1);
		auto& distribution = G.nonterminals[i].rule_distribution;
		double alpha = is_preterminal ? preterminal_alpha : nonterminal_alpha;
		if (!init(distribution, is_preterminal, nonterminal_count, symmetric_dirichlet<double>(4, alpha / 4)))
			exit(EXIT_FAILURE);
	}
	G.nonterminals.length = nonterminal_count;

	/* load the sentences and construct the initial syntax trees (all randomly branching) */
	sequence* sentences = sentences_to_ids();
	syntax_node<null_semantics>** syntax = (syntax_node<null_semantics>**)
		malloc(sizeof(syntax_node<null_semantics>*) * sentence_count);
	if (syntax == NULL) {
		fprintf(stderr, "ERROR: Insufficient memory for syntax trees.\n");
		free_sequences(sentences);
		return EXIT_FAILURE;
	}
	for (unsigned int i = 0; i < sentence_count; i++) {
		initialize_tree(syntax[i], sentences[i], nonterminal_count);

		if (!add_tree(1, *syntax[i], null_semantics(), G))
			return EXIT_FAILURE;
	}

	character_printer printer; default_scribe nonterminal_printer;
	unsigned int* order = (unsigned int*) malloc(sizeof(unsigned int) * sentence_count);
	for (unsigned int i = 0; i < sentence_count; i++)
		order[i] = i;
	for (unsigned int t = 0; t < 100000; t++) {
		if (t % 100 == 0) {
			fprintf(out, "[iteration %u]\n", t);
			for (unsigned int i = 0; i < sentence_count; i++) {
				print(*syntax[i], out, printer, nonterminal_printer); print("\n\n", out);
			}
			fflush(out);
		}
		shuffle(order, sentence_count);
		for (unsigned int i = 0; i < sentence_count; i++) {
			auto sentence = tokenized_sentence<null_semantics>(sentences[order[i]]);
			resample(syntax[order[i]], G, null_semantics(), sentence, dummy_morphology_parser(), NULL);
		}
		/* TODO: cleanup the rule distributions (remove zeros) */
	}

	for (unsigned int i = 0; i < sentence_count; i++) {
		print(*syntax[i], out, printer, nonterminal_printer); print("\n\n", out);
		free(*syntax[i]); free(syntax[i]);
	}
	free(order);
	free(syntax);
	free_sequences(sentences);
	return EXIT_SUCCESS;
}
