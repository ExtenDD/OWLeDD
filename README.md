# Description Logics with Two Types of Definite Descriptions: Complexity, Expressiveness, and Automated Deduction (materials for the proceedings of AAAI 2026)

This repository contains code and data used in the paper „Description Logics with Two Types of Definite Descriptions: Complexity, Expressiveness, and Automated Deduction” contained in the proceedings of the AAAI 2026 conference. Below, we briefly describe the implementation of tableau calculus TAB<sub>ALCi</sub> that was discussed in this paper, and provide instructions for how to use the prover as well as the generator of random concepts. In the last point, we provide information about how the data used in the paper was generated and the meaning of variables contained in it.

## 1. Implementation – general remarks
   ### 1.1 Introduction and main functionalities

The implementation, from now on called the „TAB<sub>ALCi</sub> prover”, or simply „prover” was written in the programming language Python 3.10. The code is divided between 5 files, which we describe below. Note that the code itself follows the jargon of classical and modal logic in referring to „formulas” rather than „concepts”.

Our prover allows to introduce single concepts, ABox and TBox, each of the three being optional. We describe in detail how to use it below, in point 2: „Instructions for using the prover”. Note that in the paper we only report usage of the prover as applied to single concepts. Note also that the prover allows using unrestricted number of roles, even though our experiments were only applied for concepts with one role.

  ### 1.2 Parser

Our parser was built using the Python library „Lark” (<https://github.com/lark-parser/lark>). The parser accepts a string object that is an initial representation of the concept, and parses it into an appropriate Pythonic class that further represents the concept in the prover. The structure of the those classes was built in a similar way as in the library „Mathesis”, some parts of our code are directly inspired by it (see <https://github.com/DigitalFormalLogic/mathesis>). See point 2 below for detailed instructions of how to use the parser.

Note that parsing time has not been analysed in the paper, but it grows linearily with concept size, with the runtime of the prover for concepts with 100 atoms being approx. 0.5s, and for concepts with 200 atoms approx. 1s.

  ### 1.3 Python scripts

**forms.py:**

This script contains the parsing mechanism as well as all definitions of the classes that encode the concepts/ formulas.

The main class is „Formula”, and the others inherit from it by the Pythonic inheritance mechanism. The functions than can be applied to the formula classes are grouped into four types: the first output atoms in a formula (e.g. `atom`); the second relate to the representation of a formula (e.g. `\__str_\_`); the third is necessary to implement equality of formulas (`\__eq_\_`); functions of the fourth type reflect structural properties of the formula („e.g. `descr_global_count`).

**interpretation.py:**

This script contains two main classes that encode the interpratation object (which can be seen as a Kripke structure) that is built during the construction of the tableau. The first class („Interpretation”) is the intepretation itself and the second („World”) corresponds to individuals that constitute domains in description logics („Kripke worlds” in the jargon of modal logic). The definitions of the classes are built on the implementation of a graph as an adjacency map structure, introduced by Goldwasser, Goodrich, Tamassia (2013).

**tableau.py:**

This is the main script, which defines the `DL_Tableau` object and can be used to build the tableau using the rules described in our paper. To initialize the `DL_Tableau` object, the user can enter a list of concepts, ABox and TBox in the input (at least one of them will be enough). An `initial_interpretation` is then created – a Pythonic object defined in the file „interpretation”. To build the whole tableau by applying the rules, the function `build_tableau` has to be used on the `DL_Tableau` object (note that this function was separated from building the tableau in order for our experiments to separate the time needed for parsing from the time needed to build the tableau by applying the rules). Detailed instructions as to how to use this function, and about other properties of the `DL_Tableau` object, are contained in point 2 – „Instructions for using the prover”.

The tableau works by consecutively applying the rules described, individual after individual. The order of applying the rules is defined in the list `rules_to_apply` introduced in the file. If any rule is applied, rules are applied all over again, in accordance with this order. Rules themselves are functions of the intepretation, and are contained in the script „rules”. Each rule, when applied, modifies the interpretation accordingly. If a rule is non-deterministic, additional interpretation is created and added to the list `alternative_interpretation`. Each of them can be considered to be a new branch of the tableau. If an inconsistency is found in an interpretation that the prover is currently working on, one of the interpretations from `alternative_interpretation` is explored. Note that at the moment the prover simply chooses the last element from the list, no heuristic is used to choose an interpretation. Building such heuristics can be one of the aims of future research.

**rules.py:**

This script contains rules of the calculus TAB<sub>ALCi</sub> in the form of functions, that take the interpretation object as argument, and outputs - if the rule is applied - the modified interpretatoion and a list of additional interpretations created (if the rule is deterministic, the latter is empty).

**generators.py:**

This is an additional, technical script, that helps generate new individual names, and new fresh atomic concept names (both are one of the effects of applying the tableau rules), making sure that the new names have not been used so far.

## 2. Instructions for using the prover

The main script in the prover is „tableau.py”, which has to be first run. Note that this script imports the scripts „forms.py”, „interpretation.py” and `rules.py' (the latter also imports „generators.py”), so all the scripts need to be in the same folder. For the script to work, the following libraries have to be installed as well: „lark”, „re”, „time” and „copy”. When the script „tableau” is run, one can build the `DL_Tableau` object. To do that, first it has to be explained how concepts should be constructed:

**Concepts**

In order for the parser to properly parse the concepts, they have to built in the following way:

- Atoms have to start with a capital letter, after which capital letters, small letters, digits, or the symbol `_` can follow (no other special symbols are allowed). For example:
  - `'A'`
  - `'B_12'`
  - `'Tall'`
- Negation of a concept can be built using either of the symbols `~` or `¬`. For example:
  - `'~F3'`
  - `'¬X'`
- Conjunction of two concepts can be built using either of the symbols `&` or `Π`. For example:
  - `'F & R1'`
  - `'Tall Π Pretty'`
- Subsumption of two concept can be built using either of the two strings of symbols "->" or "-:". For example:
  - `'A -> B'`
  - `'Tall -: ~Fat'`
- The quantifiers can be built either using the symbol `Ǝ` or the string of symbols `*E`. Roles have to start with small letters, followed by capital letters, small letters, digits or the symbol `_`. The whole concept consists of three parts that have to be put in the following order, with spaces between them:
\
\
`[quantifier] [role] [concept]`
\
\
Note that the symbol and rules for universal quantification are not applied at the moment. Instead, please simply use negated existantial quantifiers. For example:
  - `'*E role_1 A'`
  - `'Ǝ r R5'`
  - `'~*E likes Tall'`
- Global descriptions are built in following way (spaces between the dot and the concept names are not necessary):
\
\
`[i] [Concept1] [.] [Concept2]`
\
\
For example:
  - `'i A1.B4'`
  - `'~i Rich.Pretty'`
- Local descriptions are built in the following way (space between the dot and the concept name is not necessary):
\
\
`[i] [.] [Concept]`
\
\
For example:
  - `'i.Rich'`
  - `'~i.XaV'`

**Creating the tableau object**

In order to create the `DL_Tableau` object, the user has to give 4 arguments as input (note that what is usually taken as an ABox, is here divided into an ABox and an RBox). Note that all concept, individual and role names should be put between double or single quotation marks, as used in Python (' or ")

1. concept: this can be a concept or a list of concepts written in a Pythonic way, for example:
    - `concept = 'A'`
    - `concept = ['U&B', 'i.Y']`
2. ABox: this should be a Pythonic dictionary, with individual names as keys, and as values: single concepts or lists of concepts that are satisfied by the individual. Note that individual names can be any strings of symbols. For example
    - `ABox = {'individual1': ['B', 'C'], 'individual2': 'A'}`
    - `ABox = {'Mark' : ['Tall', 'Smart']}`
3. RBox: this should be a Pythonic dictionary, with role names as keys, and as values – pairs of individuals that are connected by the role, with the origin coming first and the destination second. Each pair of individuals should be a Pythonic list, and many pairs correspond to a list of lists that are pairs. For example:
    - `RBox = {'role' : ['ind1', 'ind2']}`
    - `RBox = {'likes': [['Tom', 'Ann'], ['Al', 'Mary']], 'loves' : ['Tom', 'Mary']}`
4. TBox: this should be a subsumption of two concepts or a list of subsumptions, for example:
    - `TBox = 'A -> B'`
    - `TBox = ['Tall' -> 'Pretty', 'Smart' -> 'Rich']`

Here is an example of a complete input, in which all 4 arguments are given one after another, after commas:

```
tab = DL_Tableau(concept = ['Man', 'i.Bob', 'Nice & Clean'],
                 ABox = {'Robert': 'Man', 'Ana': 'Nice'},
                 RBox = {'is_friend': [['Robert', 'Ana'], ['Robert', 'John']], 'neighbour': [['Ana', 'Robert']]},
                 TBox=['Man -> Nice', '~Clean -> ~Nice'])
```

We have saved our tableau object in the variable „tab”. In what follows, we will show what functions can be applied to the tableau encoded with this name.

Note, that the 4 arguments do not have to be given in this order, and that any non-empty combination of them can be given as input. After entering such input, a `DL_Tableau` object is created.

After creating the `DL_Tableau`, one can use the function `initial_interpretation` to view the interpretation in the form after parsing the input. For example:
```
tab.print_initial_interpretation()
```
Note that the concepts from the TBox are transferred to all the individuals mentioned in the input automatically at this stage.

**Build the tableau using the function „build_tableau”**

In order to apply the rules to the tableau, the function `build_tableau` has to be used on the `DL_Tableau` object, for example:
```
tab.build_tableau()
```
Applying it will result in the output that contains 4 elements (this form of output is used in the experiments; we leave it that way to enable their reproducibility). They are given in the form of a tuple, its elements have the following meaning:

`[0]`: did applying the tableau rules result in a time-out? True/False

`[1]`: is the input satisfiable? True/False

`[2]`: number of closed branches

`[3]`: number of applied rules

For example, to check satisfiability, we can directly refer to the second element of the output, by typing:
```
tab.build_tableau()[1]
```
When running the `tab.build_tableau()` command, an interpretation is automatically printed out, as well as information about the satisfiability (for convenience). Those elements have been added for comparison with the version of the prover used in the experiments.

Note, however, that not always this interpretation can can be considered as a proper model! For this to be possible, additional actions would need to be taken, for example some individuals would have to be merged into one, in order for the global and local descriptions to be satisfied and some role-links would need to be added. We plan to add the feature of constructing the whole model for the satisfied inputs to our implementation soon. The printout of the interpretation includes names of the individuals followed by all the concepts satisfied by them, and then relations between individuals.

## 3. Generator of random concepts

As written in our paper, the generator of random concepts first builds a random binary syntax tree containing a predefined number of nodes, each corresponding to a subconcept; then, atomic concepts are randomly distributed among the leaves, binary operators (including global descriptions) among the inner nodes, and unary operators (including local descriptions) among all the nodes. The generator allows to customise the following attributes of the concept:

- Number of occurrences of atoms (`no_atoms`): determines the size of the random syntax tree. It is identical to the number of leaves of the tree.
- Number of atoms (`no_diff_atoms`): number of different atoms – a number that can range betwen 1 and the number of occurrences of atoms
- Number of existential restrictions (`no_modal`) – number of operators of the form `Ǝ r A` or `~Ǝ r A`. If this operator is set to _n_, then _n_ existential restrictions are randomly distributed between all the subconcepts.
- Number of local descriptions (`no_LD`) – number of operators of the form `i.A` or `~i.A`. If this operator is set to _n_, _n_ local descriptions are randomly distributed between all the subconcepts.
- Number of global descriptions (`GD_count`) – number of operators of the form `iA.B` or `~i A.B`. If this operator is set to _n_, _n_ local descriptions are randomly distributed among the inner nodes of the syntax tree.
- Chance of a binary connective to be a global description (`GD_chance`): this is a parameter that can be set instead of `GD_count`. If this is done, for each inner node of the syntax tree, the binary connective associated with that tree has chance of `GD_chance` of being a global description. If both `GD_count` and `GD_chance` are given in the input, only `GD_count` is used.
- Chance of any subconcept being a negation (`neg_chance`).

**In order to use the generator:**

- Make sure you have installed the Python libraries „numpy” and „random”
- Run the file script „random_concept_generator.py”
- Use the function `random_ALCi_concept_str`, for example:
```
random_ALCi_concept_str(no_atoms = 6,
                        no_diff_atoms = 4,
                        no_modal = 3,
                        no_LD = 2,
                        GD_chance = None,
                        GD_count = 3,
                        neg_chance = 0.5)
```
The generator outputs the representation of a concept as a string of characters – in the form that can be then parsed by our parser described above.

Note that the generator produces single random concepts. The random concepts produced that way contain only one role type, and do not produce random ABox or TBox objects.

## 4. Information about the data generated for results

The data used in the paper has been generated using the script „data_generation.py”. To use it, one has to:

- Make sure you have installed the Python libraries „numpy”, „pandas”, „math”, „timeit” and „random”,
- set two parameters in the beginning of the script: `random_seed` and `no_formulas` (number of formulas/concepts to be generated),
- assign a value to the variable `no_atoms` – this will set the size of each generated concept separately. If it is chosen randomly (as in the current script), each generated concept will have a random size in a given range.
- fill the arguments of the function `random_ALCi_concept_str`, in order to determine what type of concepts should be contained in the data (note that the argument `no_atoms` is set before executing the function),
- Name the datafile(s) that appear in the output. Current script produces two files – an Excel file and a csv. file

For our paper we generated 7 datasets: 3 datasets with only global descriptions, 3 with only local descriptions, and one dataset without descriptions. For _k_ being the number of binary operators in a concept, the first three datasets contain 0.1\* _k_, 0.3\* _k_, and 0.5\* _k_ global descriptions, respectively, whereas the next three datasets contain 0.1\* _k_, 0.3\* _k_, and 0.5\* _k_ local descriptions. Below, those six datasets will be referred to as GD_0.1, GD_0.3, GD_0.5, LD_0.1, LD_0.3, LD_0.5. The dataset without descriptions will be referred to as NoDesc. Note that the datasets, which are also included in this repository, are named using the same names.

For each of the 7 datasets, the following parameters were constant:

- `no_diff_atoms = ceil(no_atoms/2)`
- `neg_chance = 0.5`
- `no_modal = ceil((2\*no_atoms-1)\*0.3)`
- `GD_chance = None`
- `no_atoms = random.randint(10,200)`

The other parameters are listed in the table below. Crucially, the table includes the random.seed needed to reproduce the random sets of concepts.

| **Dataset** | **`random_seed`** | **`no_formulas`** | **`GD_count`** | **`No_LD`** |
| --- | --- | --- | --- | --- |
| GD_0.1 | `41`  | `150` | `ceil(0.1\*(no_atoms-1))` | `0`   |
| GD_0.3 | `33`  | `150` | `ceil(0.3\*(no_atoms-1))` | `0`   |
| GD_0.5 | `30`  | `150` | `ceil(0.5\*(no_atoms-1))` | `0`   |
| LD_0.1 | `19`  | `150` | `0`   | `ceil(0.1\*(no_atoms-1))` |
| LD_0.3 | `51`  | `150` | `0`   | `ceil(0.3\*(no_atoms-1))` |
| LD_0.5 | `23`  | `150` | `0`   | `ceil(0.5\*(no_atoms-1))` |
| NoDesc | `50`  | `200` | `0`   | `0`  |

Note that, for example, ceil(0.1\*(no_atoms-1)) is an exact Python command, and the function „ceil” is the mathematical function „ceiling” (taking a real number _x_ as argument, and returning the smallest integer no less than _x_).

The variables in the dataset have the following meaning:

| **Formula** | **Formula in a string format (ready to be parsed)** |
| --- | --- |
| `formula2` | Formula in a string format – version 2 |
| `no_atoms` | Number of occurrences of atoms |
| `form_size` | Formula size (number of symbols excluding parentheses) |
| `modal_depth` | Greatest number of existential restrictions on a single branch in the syntax tree |
| `no_modal` | Number of existential restrictions |
| `modal_share` | `no_modal` / number of subformulas (nodes in the syntax tree) |
| `time_parsing` | parsing time |
| `time_tableau_min` | Time of tableau generation – minimum of generated values |
| `time_tableau_avg` | Time of tableau generation – average of generated values |
| `no_conj` | Number of concjunctions |
| `no_descr_global` | Number of global descriptions |
| `no_descr_local` | Number of local descriptions |
| `descr_global_share` | `no_descr_global` / number of binary formulas |
| `descr_local_share` | `no_descr_local` / number of subformulas |
| `no_diff_atoms` | Number of different atoms |
| `time_out` | Did the tableau generation end with a time-out (`True`/`False`) |
| `is_satisfiable` | Is the concept satisfiable (`True`/`False`) |
| `no_rules_applied` | Number of rules applied |
| `no_branches_explored` | Number of branches explored |
| `no_neg` | Number of negations |

## 5. Instructions for reproducing the results presented in the paper

The data analysis and results, as presented in our paper, were prepared using the programming language R. The code used to generate the results and the chart, using the data visualization package „ggplot2”, is also available („generation_of_results.R”). To generate the results, one should:

- Generate the data using the appropriate random.seeds and other parameters, using the Python scripts described above
- Run the R script, which reads the data, transforms it, and creates the table and chart

## 6. References

- Mathesis library <https://github.com/DigitalFormalLogic/mathesis>
- Lark library <https://github.com/lark-parser/lark>
- M.H. Goldwasser, M.T. Goodrich, R. Tamassia 2013: Data Structures & Algorithms in Python, Wiley 2013.
