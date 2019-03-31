
**TODO:** Document this code. The repository is located at <https://github.com/asaparov/grammar>.

This code implements the generative model of grammar as described in [this paper](https://asaparov.org/assets/conll_2017.pdf). Given a logical form, the grammar generates a derivation tree top-down, by selecting production rules probabilistically conditioned on the logical form. The leaves of the derivation tree form the tokens of the output utterance.

If you use this code in your research, please cite:
 > Abulhair Saparov, Vijay Saraswat, and Tom M. Mitchell. 2017. A Probabilistic Generative Grammar for Semantic Parsing. In *Proceedings of the 21st Conference on Computational Natural Language Learning (CoNLL 2017)*.

### Dependencies

To use the code, simply download the files into a folder named "grammar". Add this folder to the include path for the compiler, for example by using the `-I` flag.

This library depends on [core](https://github.com/asaparov/core), [math](https://github.com/asaparov/math), and [hdp](https://github.com/asaparov/hdp). The code makes use of `C++11` and is regularly tested with `gcc 8` but I have previously compiled it with `gcc 4.8`, `clang 4.0`, and `Microsoft Visual C++ 14.0 (2015)`. The code is intended to be platform-independent, so please create an issue if there are any compilation bugs.

### Code structure

`grammar.h` contains the definitions of the basic data structures, such as production rules in `struct rule`, nonterminals in `struct nonterminal`, the grammar in `struct grammar`, and the nodes of derivation trees in `struct syntax_node`. These data structures are defined as template types, where the logical form type is given by the `Semantics` typename parameter, and the distribution over production rules at each nonterminal is given by the `RuleDistribution` template parameter.

`struct null_semantics` in `grammar.h` is an example of a `Semantics` type where the logical forms are empty. `pcfg_grammar.h` implements a `RuleDistribution` type where the distribution over production rules does not depend on the logical form. The test program in `pcfg_induction.cpp` uses this rule distribution along with `null_semantics` to effectively perform grammar induction on a [probabilistic context-free grammar](https://en.wikipedia.org/wiki/Stochastic_context-free_grammar).

`hdp_grammar.h` defines `struct hdp_rule_distribution` which provides another example of a `RuleDistribution` type, where the distribution over production rules is given by a [hierarchical Dirichlet process](https://asaparov.org/docs/hdp/hdp.h.html) (HDP).

The parser and Metropolis-Hastings sampler (for training) are implemented in `parser.h`. Since the structure of the two algorithms are so similar, they are implemented as a single algorithm, where the `Mode` template parameter determines whether the algorithm is parsing or sampling. The function `parse_result parse(...)` contains the main loop of this algorithm, where at every iteration, the search state is popped from the priority queue (agenda) and processed according to its type. This processing may add new search states to the priority queue.

`morphology.h` implements a simple model of word morphology, where each word is modeled as an inflected root. The root may be inflected according to grammatical number, aspect, and tense.

### Examples

There are two test programs in this repository.
 - `pcfg_induction` creates an instance of the grammar where the logical forms are empty. So the grammar is a [probabilistic context-free grammar](https://en.wikipedia.org/wiki/Stochastic_context-free_grammar) and is purely syntactic. The program then trains the grammar on a handful of examples created from the reference grammar: `E -> 0 E 1`, `E -> 0 1`, `E -> E E`. The program is defined in `pcfg_induction.cpp` and can be compiled using `make pcfg_induction`.
 - `math_induction` learns a grammar where the logical forms are simple arithmetic expressions such as `1 + (1 * 0) / 1`. These logical expressions are modeled as simple binary trees, as defined in `tree_semantics.h`. This program uses an HDP to model the distribution over production rules at each nonterminal (`struct hdp_rule_distribution` in `hdp_grammar.h`). This program is located in `math_induction.cpp` and can be compiled using `make math_induction`.
