/**
 * math_induction.cpp
 *
 *  Created on: Jul 21, 2016
 *      Author: asaparov
 */

#include "tree_semantics.h"
#include "tree_semantics_hdp.h"

#include "parser.h"
#include "hdp_grammar.h"

typedef hdp_grammar<rule_prior<dense_categorical<double>, sparse_categorical<sequence, double>>, tree_semantics> hdp_tree_grammar;

inline tree_semantics operator + (const tree_semantics& first, const tree_semantics& second) {
	tree_semantics sum = tree_semantics('+');
	sum.left_child = copy(first);
	sum.right_child = copy(second);
	sum.excluded_count = 0;
	sum.reference_count = 1;
	return sum;
}

inline tree_semantics operator - (const tree_semantics& first, const tree_semantics& second) {
	tree_semantics sum = tree_semantics('-');
	sum.left_child = copy(first);
	sum.right_child = copy(second);
	sum.excluded_count = 0;
	sum.reference_count = 1;
	return sum;
}

inline tree_semantics operator * (const tree_semantics& first, const tree_semantics& second) {
	tree_semantics sum = tree_semantics('*');
	sum.left_child = copy(first);
	sum.right_child = copy(second);
	sum.excluded_count = 0;
	sum.reference_count = 1;
	return sum;
}

inline tree_semantics operator / (const tree_semantics& first, const tree_semantics& second) {
	tree_semantics sum = tree_semantics('/');
	sum.left_child = copy(first);
	sum.right_child = copy(second);
	sum.excluded_count = 0;
	sum.reference_count = 1;
	return sum;
}

unsigned int ADD = '+';
unsigned int SUBTRACT = '-';
unsigned int MULTIPLY = '*';
unsigned int DIVIDE = '/';
unsigned int DIGITS[] = { '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' };

tree_semantics zero = tree_semantics('0');
tree_semantics one = tree_semantics('1');

tree_semantics logical_forms[] = {
	zero + one,
	one + zero,
	zero + zero,
	one + one,
	zero - one,
	one - zero,
	zero - zero,
	one - one,
	zero * zero,
	one * one,
	zero / one,
	one / zero,
	(zero * one) + one,
	(zero * one) - zero,
	zero + (zero / one),
	zero + (zero * zero),
	one - (zero / one),
	(one * zero) + one,
	(one / zero) + zero,
	zero + (one * one),
	zero + (one / zero),
	((one - zero) + one) - zero,
	(zero / one) - (zero * one),
	(one * one) - ((zero / one) * zero),
	(((one * zero) / zero) + zero) - one,
	(zero - one) + ((zero * one) / zero),
	(one * zero) - ((one * zero) / zero),
	(zero / one) - ((zero / one) / one),
	(zero / one) + ((one / one) * zero)
};

constexpr unsigned int sentence_count = (unsigned int) array_length(logical_forms);

template<bool Root = false>
void to_sentence(const tree_semantics& logical_form, array<unsigned int>& sentence) {
	if (logical_form.left_child == NULL && logical_form.right_child == NULL) {
		sentence.add(logical_form.label);
		return;
	}

	//const bool parentheses = !Root && (logical_form.left_child != NULL && logical_form.right_child != NULL);
	//if (parentheses) sentence.add('(');

	to_sentence(*logical_form.left_child, sentence);
	sentence.add(logical_form.label);
	to_sentence(*logical_form.right_child, sentence);

	//if (parentheses) sentence.add(')');
}

struct character_printer { };

template<typename Stream>
bool print_character(unsigned int character, Stream& out) {
	return print((char) character, out);
}

void print_sentence(unsigned int* sentence, unsigned int length) {
	for (unsigned int i = 0; i < length; i++)
		fputc(sentence[i], stdout);
}

template<typename Stream>
inline bool print(unsigned int character, Stream& stream, character_printer& printer, unsigned int level = 0) {
	return print_character(character, stream);
}

template<typename T>
void free_arrays(array<T>* arrays, unsigned int count) {
	for (unsigned int i = 0; i < count; i++)
		free(arrays[i]);
	free(arrays);
}

template<bool IsPreterminal, typename NonterminalPrior, typename TerminalPrior, size_t N>
bool add_nonterminal(hdp_tree_grammar& G, tree_semantics::feature (&features)[N],
	const double* a, const double* b, NonterminalPrior& nonterminal_prior, TerminalPrior& terminal_prior)
{
	if (!G.nonterminals.ensure_capacity(G.nonterminals.length + 1))
		return false;

	auto& nonterminal = G.nonterminals[(unsigned int) G.nonterminals.length];
	nonterminal.id = (unsigned int) G.nonterminals.length + 1;
	nonterminal.name = "";

	if (!init(nonterminal.rule_distribution, IsPreterminal ? PRETERMINAL : NONTERMINAL,
			rule_prior<NonterminalPrior, TerminalPrior>(nonterminal_prior, terminal_prior),
			features, a, b, array_length(features)))
		return false;
	G.nonterminals.length++;
	return true;
}

inline sequence new_sequence(const unsigned int* data, unsigned int length) {
	unsigned int* new_data = (unsigned int*) malloc(sizeof(unsigned int) * length);
	if (new_data == NULL) exit(EXIT_FAILURE);
	memcpy(new_data, data, sizeof(unsigned int) * length);
	return sequence(new_data, length);
}

/* semantic prior model */
double left_alpha[] = { 1.0e1, 1.0e-4 };
double right_alpha[] = { 1.0e1, 1.0e0, 1.0e-4 };
tree_semantics_prior prior(200, left_alpha, right_alpha);

template<bool Complete>
inline double log_probability(const tree_semantics& logical_form) {
	return 0.0; //prior.log_probability(logical_form);
}

int main(int argc, const char** argv)
{
	printf("(seed = %u)\n", get_seed());
	double nonterminal_a[] = { 10000.0, 100.0 };
	double nonterminal_b[] = { 10.0, 10.0 };
	double preterminal_a[] = { 10000.0, 100.0 };
	double preterminal_b[] = { 10.0, 10.0 };
	constexpr unsigned int nonterminal_count = 3;

	if (!populate_arity_table(logical_forms, (unsigned int) array_length(logical_forms), NULL))
		return EXIT_FAILURE;

	hdp_tree_grammar G;
	dense_categorical<double> nonterminal_prior = dense_categorical<double>(nonterminal_count);
	for (unsigned int i = 0; i < nonterminal_count; i++)
		nonterminal_prior.phi[i] = 1.0 / nonterminal_count;
	sparse_categorical<sequence, double> terminal_prior(4);
	terminal_prior.set(new_sequence(&ADD, 1), 1.0 / 14);
	terminal_prior.set(new_sequence(&SUBTRACT, 1), 1.0 / 14);
	terminal_prior.set(new_sequence(&MULTIPLY, 1), 1.0 / 14);
	terminal_prior.set(new_sequence(&DIVIDE, 1), 1.0 / 14);
	for (unsigned int i = 0; i < 10; i++)
		terminal_prior.set(new_sequence(&DIGITS[i], 1), 1.0 / 14);

	tree_semantics::feature label[] = {tree_semantics::FEATURE_LABEL};
	tree_semantics::feature left_label[] = {tree_semantics::FEATURE_LABEL_LEFT};
	tree_semantics::feature right_label[] = {tree_semantics::FEATURE_LABEL_RIGHT};
	add_nonterminal<false>(G, right_label, nonterminal_a, nonterminal_b, nonterminal_prior, terminal_prior);
	add_nonterminal<false>(G, left_label, nonterminal_a, nonterminal_b, nonterminal_prior, terminal_prior);
	add_nonterminal<true>(G, label, preterminal_a, preterminal_b, nonterminal_prior, terminal_prior);
	if (G.nonterminals.length != nonterminal_count) {
		fprintf(stderr, "ERROR: Unexpected number of nonterminals.\n");
		return EXIT_FAILURE;
	}

	/* generate the sentences from the logical forms using a synthetic grammar */
	array<unsigned int>* sentences = (array<unsigned int>*)
		malloc(sizeof(array<unsigned int>) * array_length(logical_forms));
	for (unsigned int i = 0; i < array_length(logical_forms); i++) {
		if (!array_init(sentences[i], 16))
			return EXIT_FAILURE;
		to_sentence<true>(logical_forms[i], sentences[i]);
	}

	/* construct the initial syntax trees (all randomly branching) */
	syntax_node<tree_semantics>** syntax = (syntax_node<tree_semantics>**)
		calloc(sentence_count, sizeof(syntax_node<tree_semantics>*));
	if (syntax == NULL) {
		fprintf(stderr, "ERROR: Insufficient memory for syntax trees.\n");
		free_arrays(sentences, sentence_count);
		return EXIT_FAILURE;
	}
	for (unsigned int i = 0; i < sentence_count; i++) {
		while (!initialize_tree(G, syntax[i],
			{sentences[i].data, (unsigned int) sentences[i].length},
			logical_forms[i])) { }

		if (!add_tree(1, *syntax[i], logical_forms[i], G))
			return EXIT_FAILURE;
	}

	/* train the semantic model */
	FILE* out = stdout;
	fprintf(out, "Training semantics model... "); fflush(out);
	prior.train(logical_forms, array_length(logical_forms), 100, 80, 5); // use 200, 800, 5
	fprintf(out, "done.\n"); fflush(out);

	character_printer printer;
	default_scribe nonterminal_printer;
	unsigned int* order = (unsigned int*) alloca(sizeof(unsigned int) * sentence_count);
	for (unsigned int i = 0; i < sentence_count; i++)
		order[i] = i;
	for (unsigned int t = 0; t < 2000 + 1; t++) {
		if (t % 1 == 0) {
			fprintf(out, "[iteration %u]\n", t);
			for (unsigned int i = 0; i < sentence_count; i++) {
				print(logical_forms[i], out, printer); print('\n', out);
				print(*syntax[i], out, nonterminal_printer, printer); print("\n\n", out);
			}
			printf("(seed = %u)\n", get_seed());
			auto printers = make_pair<character_printer&, default_scribe&>(printer, nonterminal_printer);
			for (unsigned int i = 0; i < nonterminal_count; i++) {
				if (G.nonterminals[i].rule_distribution.observations.sum == 0) continue;
				print(G.nonterminals[i].rule_distribution.type, out); print(' ', out);
				print(G.nonterminals[i].id, out); print(" HDP: ", out);
				print(G.nonterminals[i].rule_distribution.sampler, out, printer, printers);
				print('\n', out);
			}
			fflush(out);
		}

		/* decrease the temperature by a bit */
		for (unsigned int i = 0; i < G.nonterminals.length; i++) {
			auto& rule_distribution = G.nonterminals[i].rule_distribution;
			for (unsigned int j = 0; j < G.nonterminals[i].rule_distribution.feature_count + 1; j++)
				rule_distribution.a[j] = (rule_distribution.a[j] - 0.1) * 0.998 + 0.1;
		}

		shuffle(order, sentence_count);
		for (unsigned int i = 0; i < sentence_count; i++) {
			auto sentence = tokenized_sentence<tree_semantics>({
				sentences[order[i]].data, (unsigned int) sentences[order[i]].length});
			resample(syntax[order[i]], G, logical_forms[order[i]], sentence, NULL);
			//resample_locally(syntax[order[i]], G, logical_forms[order[i]], 2);
			//printf("Reparsing sentence %u (ID: %u)\n", i, order[i]); fflush(stdout);
			//reparse<false>(syntax[order[i]], G, logical_forms[order[i]], sentence, NULL);
			sample_grammar(G);
		}

		/* iterate over all possible binary production rules (these are the types) */
		/*auto iterator = nonterminal_pair_iterator(nonterminal_prior);
		while (iterator.has_next()) {
			nonterminal_pair pair = iterator.next();
			rule<tree_semantics> new_rule = rule<tree_semantics>(2);
			new_rule.nonterminals[0] = pair.first;
			new_rule.nonterminals[1] = pair.second;

			for (unsigned int i = 0; i < array_length(tree_semantics::transformations); i++) {
				const auto& transformation = tree_semantics::transformations[i];
				new_rule.functions[0] = transformation.key;
				new_rule.functions[1] = transformation.value;
				resample_type(new_rule, syntax, G, logical_forms, sentence_count, 1);
			}
		}*/

		if (t == 30) {
			for (unsigned int i = 0; i < sentence_count; i++) {
				print(logical_forms[i], out, printer); print('\n', out);
				print(*syntax[i], out, nonterminal_printer, printer); print("\n\n", out);
			}

			for (unsigned int sentence_id = 0; sentence_id < sentence_count; sentence_id++)
			{
				printf("Parsing sentence %u...\n", sentence_id); fflush(stdout);
				tree_semantics logical_form = WILDCARD_TREE;
				tree_semantics logical_form_output;
				syntax_node<tree_semantics>& parsed_syntax =
					*((syntax_node<tree_semantics>*) alloca(sizeof(syntax_node<tree_semantics>)));
				auto sentence = tokenized_sentence<tree_semantics>({
					sentences[sentence_id].data, (unsigned int) sentences[sentence_id].length});
				unsigned int derivation_count;
				if (parse<false, false>(&parsed_syntax, derivation_count, logical_form, &logical_form_output, G, sentence, NULL)) {
					tree_semantics pruned_logical_form;
					remove_wildcard_leaves(logical_form_output, pruned_logical_form);
					print(pruned_logical_form, out, printer); print('\n', out);
					print(parsed_syntax, out, nonterminal_printer, printer); print("\n", out);

					printf("Parse log probability: %lf (sampled derivation has log probability %lf)\n",
							log_probability(G, parsed_syntax, pruned_logical_form, NULL),
							log_probability(G, *syntax[sentence_id], logical_forms[sentence_id], NULL));
					printf("Parse prior probability: %lf (true derivation has prior probability %lf)\n",
							log_probability<true>(pruned_logical_form),
							log_probability<true>(logical_forms[sentence_id]));
					print('\n', out);
					free(pruned_logical_form); free(logical_form);
					free(logical_form_output); free(parsed_syntax);
				}
			}
			break;
		}
	}

	for (unsigned int i = 0; i < sentence_count; i++) {
		if (syntax[i] != NULL) {
			free(*syntax[i]);
			free(syntax[i]);
		}
	}
	free_arrays(sentences, sentence_count);
	free(syntax);
	return EXIT_SUCCESS;
}
