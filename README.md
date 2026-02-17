# OWLeDD: a Python Library for Tableu Reasoning in Description Logic ALC Extended with Definite Descriptions 

Our library is currently available in the form of downloadable python scripts, but very soon a fool package will be available to install. At the moment, to use the package the user needs to: download all the files contained in the folder „prover”; copy the files to one folder on a local compuer; open the script „tableau”; change the folder path at the top of the script; run the script. Then all the functions from the package described below will be usable..

## 1. Implementation – general remarks
   ### 1.1 Introduction and main functionalities

The implementation, from now on called the „TAB<sub>ALCi</sub> prover”, or simply „prover” was written in the programming language Python 3.10. The code is divided between 5 files, which we describe below. Note that the code itself follows the jargon of classical and modal logic in referring to „formulas” rather than „concepts”.

Our prover allows to introduce single concepts, ABox and TBox, each of the three being optional. We describe in detail how to use it below, in point 2: „Instructions for using the prover”. Note that in the paper we only report usage of the prover as applied to single concepts. Note also that the prover allows using unrestricted number of roles, even though our experiments were only applied for concepts with one role.

  ### 1.2 Parser

Our parser was built using the Python library „Lark” (<https://github.com/lark-parser/lark>). The parser accepts a string object that is an initial representation of the concept, and parses it into an appropriate Pythonic class that further represents the concept in the prover. The structure of the those classes was built in a similar way as in the library „Mathesis”, some parts of our code are directly inspired by it (see <https://github.com/DigitalFormalLogic/mathesis>). See point 2 below for detailed instructions of how to use the parser.

Note that parsing time has not been analysed in the paper, but it grows linearily with concept size, with the runtime of the prover for concepts with 100 atoms being approx. 0.5s, and for concepts with 200 atoms approx. 1s.



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

