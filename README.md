# OWLeDD: a Python Library for Tableu Reasoning in Description Logic ALC Extended with Definite Descriptions 

OWLeDD is an implementation of tableau-based prover for description logic ALC with two types of operators for definite descriptions. 


It can be used to:
- check for satisfiability of single ALC concepts with (or without) definite descriptions
- load ontologies with expressivity of ALC in functional syntax and check their consistency
- create simple ontologies within Pythonic syntax and check for their consistency
- check consistency of ALC concepts with respect to the input ontologies


Our library is currently available in the form of downloadable python scripts, but very soon a full package will be available to install. At the moment, to use the package the user needs to: download all the files contained in the folder „prover”; copy the files to one folder on a local compuer; open the script „tableau”; change the folder path at the top of the script; run the script. Then all the functions from the package described below will be usable..

## What are definite descriptions?

Definite descriptions (DDs) are expressions of the form "the *X* such that *P(X)*", which allow one to refer to objects by means of their unique properties. 
Our prover allows to express two kinds of DDs: "local" DDs make it possible to express concepts such as `highest peak in the world', whereas "global" DDs can capture assertions such as "the highest peak in the world is located in the Himalayas". In contex of description logic and OWL ontologies DDs can for example enforce that a given concept does (or does not) have a singleton extension.


## How to use the prover

We will refer to our implementation as to „TAB<sub>ALCi</sub> prover”, or simply „prover”. Below we explain how to use it, and next we shortly describe the contents of the Python scripts made available in this repository.

Starting the prover comes down to initialising an instance of the DL_Tableau class - the central class in the implementation. Here is a simple example:

```
tab = DL_Tableau(ontology = ontology_file.owl,
                 concept = ['Student ⊓ Tall', 'i.Bob', 'Ǝ isStudentOf John'],
                 ABox = {'Robert': 'Man'},
                 RBox = {'neighbour': ['Ana', 'Robert']},
                 TBox = ['Student ⊑ Man']))
```

When a DL_Tableau object is initialised, a tableau is built and the user can access various types of information about it.

The input can contain any subset of those 5 main arguments. Below we explain how to use them, what additional arguments can passed when creating a DL_Tableau object, and what information about the built tableau can be accessed. 



## Parsing

OWLeDD contains a parser for description logic concepts and OWL ontologies, which has been created using the library [lark](https://github.com/lark-parser/lark).
There are two parsing modes. In the first mode, only restricted syntax can be introduced. This is default, and can be used for any types of input.
The second mode is reserved for the situation, in which the input contains an ontology which contains concepts and roles expressed in any other type of syntax. We describe 
both modes below.

### Entering concepts using the default parsing mode

For convenience, the parser allows using both description logic "square" syntax, and a syntax that is more easy to type from keybord:

- Atoms have to start with a capital letter, after which capital letters, small letters, digits, or the symbol `_` can follow. Before such an atom string, the symbol ":" can also optionally appear (which is often the case in ontologies). For example:
  - `'A'`
  - `'B_12'`
  - `':Tall'`
- Negation of a concept can be built using either of the symbols `~` or `¬`. For example:
  - `'~F3'`
  - `'¬X'`
- Conjunction of two concepts can be built using either of the symbols `&` or `Π`. For example:
  - `'F & R1'`
  - `'Man Π Student'`
- Disjunction of two concepts can be built using either of the symbols `&` or `⊔`. For example:
  - `'F | R1'`
  - `'Tall ⊔ Pretty'`
- Subsumption of two concept can be built using the string of symbols "->" or the symbol "⊑". For example:
  - `'A -> B'`
  - `'Flower ⊑ ~Man'`
- The existential quantifier can be built either using the symbol `Ǝ` or the string of symbols `*E`. The general quantifier can be built either using the symbol `∀` or the string of symbols `*A`. Roles have to start with small letters, followed by capital letters, small letters, digits or the symbol `_` (as with concepts, they can also be precede by the symbol ":"). The whole concept consists of three parts that have to be put in the following order, with spaces between them:
\
\
`[quantifier] [role] [concept]`
\
\
  - `'*E role_1 A'`
  - `'Ǝ r R5'`
  - `'∀ :likes Tall'`
  - `'~*A isStudentOf John'`
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
\
\

Names of individuals can be any strings of symbols. 

Here is another example of the four arguments can be used:

 
### Building a simple ontology using a Pythonic syntax

You can check satisfiability of concepts or build a simple ontology from a code editor using a Pythonic syntax. To do that, initalize a DL_Tableau object with any of the 4 arguments as described below:

1. concept: this can be a concept or a list of concepts, for example:
    - `concept = 'A'`
    - `concept = ['U&B', 'i.Y']`
2. ABox: this should be a Pythonic dictionary, with individual names as keys, and as values: single concepts or lists of concepts that are satisfied by the individual, for example:
    - `ABox = {'individual1': ['B', 'C'], 'individual2': 'A'}`
    - `ABox = {'Mark' : ['Tall', 'Smart']}`
3. RBox: this should be a Pythonic dictionary, with role names as keys, and as values – pairs of individuals that are connected by the role, with the origin coming first and the destination second. Each pair of individuals should be a Pythonic list, and many pairs correspond to a list of lists that are pairs. For example:
    - `RBox = {'role' : ['ind1', 'ind2']}`
    - `RBox = {'likes': [['Tom', 'Ann'], ['Al', 'Mary']], 'loves' : ['Tom', 'Mary']}`
4. TBox: this should be a subsumption of two concepts or a list of subsumptions, for example:
    - `TBox = 'A -> B'`
    - `TBox = ['Tall' -> 'Pretty', 'Smart' -> 'Rich']`

Here is another example of a complete input, in which all 4 arguments are given one after another, after commas:
```
tab = DL_Tableau(concept = ['C1 ⊓ :T', 'i C2.C3'],
                 ABox = {'Robert': ''*A role1 S2''},
                 RBox = {'role2': ['ind1', 'ind$%@']},
                 TBox = ['C1 ⊑ C2&C5']))
```



### Loading an ontology from a file 

You can load an ontology from an "owl" file, using the "ontology" argument. At the moment, the OWLeDD accepts only ontologies in functional syntax and with a limited number of OWL constructs:

- Declaration (of a Class, ObjectProperty and NamedIndividual)
- ClassAssertion
- ObjectPropertyAssertion
- SubClassOf
- EquivalentClasses
- DisjointClasses





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

