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
tab = DL_Tableau(ontology = 'ontology_file.owl',
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

Notes:
- ABox statements are analogical to OWL "ClassAssertion" statements. However, concepts introduced in the "concept" argument are assumed to be satisfied in a new individual, not occuring in any other argument of DL_Tableau.
- if you just use the "concept" argument, you are effectively testing satisfiability of single ALC concept (note that this is equivalent to testing satisfiability of multi-modal logic formulas, just the syntax is different)
- "RBox" stands for what usually is considered a part of ABox  - "ObjectPropertyAssertion" OWL statements.
- using "TBox" you can OWL statements of the types "SubClassOf" and "Equivalence" 

Here is another example of a complete input with all the 4 arguments:
```
tab = DL_Tableau(concept = ['C1 ⊓ :T', 'i C2.C3'],
                 ABox = {'Robert': ''*A role1 S2''},
                 RBox = {'role2': ['ind1', 'ind$%@']},
                 TBox = ['C1 ⊑ C2&C5', 'A ]))
```



### Loading an ontology from a file 

You can load an ontology from an "owl" file, using the "ontology" argument. At the moment, OWLeDD accepts only ontologies in functional syntax and with a limited number of OWL constructs:

- Declaration (of a Class, ObjectProperty and NamedIndividual)
- ClassAssertion
- ObjectPropertyAssertion
- SubClassOf
- EquivalentClasses
- DisjointClasses

If concept and role names do not conform to the parsing conventions named above, you need to use set an additional argument "flexible_syntax" to "True" when creating a DL_Tableu. In this case, the parser accepts any non-space string of symbols (an exception are the parenthesis symbols "(" and ")" - using them inside concept, role or individual names will likely cause paring errors). Here is an example of such input:
```
tab = DL_Tableau(ontology = 'ontology_file.owl',
                 flexible_syntax = True)
```
If you set "flexible_syntax" to "True", you can also use the names from the ontology in the "concept", "ABox", "RBox" and "TBox" arguments. In particular, you can check if a concpet is satisfied with respect to an ontology. Here is an example of such application of the prover:

```
tab = DL_Tableau(ontology = 'ontology_file.owl',
                 concept = 'i.A',   
                 flexible_syntax = True)
```
In this particular application, we are checking the satisfiability of a local definite description with respect to the 
ontology. If the input turns out to be satisfiable, the ontology allows models in which the concept 'A' has singular extension.


## Functionalities of the prover 

### Main functions on the "DL_Tableau" object

If you save the initialized DL_Tableau object in a variable, you can access various types of information that are saved as attributes of that object, or using functions on the object. Here is the list of them (we take it that the tableau is saved in the variable "tab", as in the previous examples):

**tab.satisfiability_check()**: outputs True/False, indicating if the input is satisfiable 
**tab.nodes_count()**: outputs the number of nodes created while constructing the tableau. Corresponds to the number of rules applied 
**tab.branches_count()**: outputs the number of branches explored while constructing the tableau. If the output is "1", no non-deteministic rule has been applied, closing the tableau after exploring one branch. 
**tab.print_interpretation()**: prints an text interpretation of the tableau in the console, indicating individuals and atomic concepts that are satisfied in them, and list of roles that connect individuals


### Optimalisations

Note that the prover some performs some optimalisation, that can be "switched on or off" using arguments on initializing the DL_Tableau object. 

- use_absorption: this defaults to "True", and uses some basic absorption techniques
- use_foldable_TBox: this also defaults to "True", and divides TBox into foldable and unfoldable parts, that 
- use_SAT_optimisations: corresponds to selected standard SAT-inspired optimisations, like semantic branching or Boolean constraint propagation. This defaults to "False", as it using it might not be effective on selected ontologies. 
- use_add_disj_optimisations: this is a mechanism for selecting the concept to expand in the case of a disjunction, based on syntactic features. Each concept is assigned a score determined by its size and the types of constructors it contains.
In particular, concepts involving DDs incur penalty scores, since the corresponding tableau rules are computationally expensive due to their non-deterministic nature. 

Note that in the current implementation "use_absorption" and "use_foldable_TBox" have to be both True or both False, and similarly, "use_SAT_optimisations" and "use_add_disj_optimisations" have to be both True or both False. Below is an example of input that "turns on" the two latter optimisations:
```
tab = DL_Tableau(ontology = 'ontology_file.owl', 
                 flexible_syntax = True,
                 use_SAT_optimisations = True,
                 use_add_disj_optimisations = True)
```


## Short description of available scripts

### tableu

This is the main script, which defines the „DL_Tableau” class and builds the tableau using the tableau rules.

### forms

This script contains the parsing mechanism as well as all definitions of the classes that encode the concepts. 
Note that the strucuture of the main "Formula" class used in this script is inspired by the library [mathesis](https://github.com/ozekik/mathesis), although it is extended with classes for descriptions and existential restriction, as well as additional attributes that store syntactic properties of concepts. 

### interpretation 

This script contains two main classes that encode the interpretation object, which is a graph-like structure built when constructing the tableau. The first class („Interpretation”) is the intepretation itself and the second („World”) corresponds to individuals that constitute the semantics of description logics. 

### rules

This script contains rules of the calculus TAB<sub>ALCi</sub> in the form of functions, that take the interpretation object as argument, and outputs - if the rule is applied  - the modified interpretatoion and a list of additional interpretations created (if the rule is deterministic, this rule is empty).

### add_functions

This is an additional, technical script. It contains functions for parsing concepts from ontologies, or functions that generate new individual names or new fresh atom names.

### TBox_optimisations

This script contains functions that perform TBox optimisations and other necessary functions related with processing TBox (e.g. checking if TBox is acyclic or performing basic absorption techniques)


