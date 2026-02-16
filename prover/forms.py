from lark import Lark, Transformer


#####################################
#PARSER------------------------------------------------------------
########################################


"""
Basic grammer for the language of the logic ALCi. 
Note that the grammar accepts two symbols for all the connectives - apart from descriptions:
& and Π for conjunction, ~ and ¬ for negation, etc.
"""

parser_DL = Lark(r"""
?fml: conjunction
    | disjunction
    | subsumption
    | equivalence
    | description_global
    | description_local
    | negation
    | diamond
    | box
    | atom
    | top
    | bot
    | _subfml

ATOM : /:?[A-Z]\w*/
ROLE : /:?[a-z]\w*/

atom : ATOM
top: "⊤" | "*T"
bot: "⊥" | "*F"
negation : ("~" | "¬") _subfml
conjunction : (conjunction | disjunction | subsumption | equivalence | _subfml | top | bot) ("&" | "⊓") _subfml
disjunction : (conjunction | disjunction | subsumption | equivalence | _subfml | top | bot) ("|" | "⊔") _subfml
subsumption : (conjunction | disjunction | subsumption | equivalence | _subfml | top | bot) ("->" | "⊑") _subfml
equivalence : (conjunction | disjunction | subsumption | equivalence | _subfml | top | bot) ("<->" | "≡") _subfml
description_global : "i" _subfml "." _subfml
description_local : "i" "." _subfml
diamond : ("Ǝ" | "*E") ROLE _subfml
box : ("∀" | "*A") ROLE _subfml

_unary : negation | diamond | box | description_local
_subfml : "(" fml ")" | _unary | atom | description_global | description_local | top | bot

%import common.WS
%ignore WS
""", start = "fml")

''
#parser='lalr' - nie udało się





parser_ONT = Lark(r"""
?fml: atom
    | top
    | bot

ATOM : /:?[A-Z]\w*/

atom : ATOM
top: "⊤" | "*T"
bot: "⊥" | "*F"

%import common.WS
%ignore WS
""", start = "fml", parser='lalr')

''




#_latex_symbols = {
#    "⊥": r"\bot",
#    "⊤": r"\top",
#}


class ToFml(Transformer):
    """ Transformer class, required by the Lark library to transform a tree object initially built by the parser into a proper Formula object (as defined below)"""
    
    def atom(self, v):
        return Atom(*v)


#wersja z bot i top
#    def atom(self, v):
#        return Atom(*v)
#        return Atom(*v, latex=_latex_symbols.get(v[0], None))
#        if len(v) == 1:
#            return Atom(*v, latex=_latex_symbols.get(v[0], None))
#        else:
#            return Atom(v)

    def negation(self, v):
        return Negation(*v)

    def diamond(self, v):
        return Diamond(*v)

    def box(self, v):
        return Negation(Diamond(v[0], Negation(v[1])))

    def conjunction(self, v):
        return Conjunction(*v)

    def disjunction(self, v):
        return Negation(Conjunction(Negation(v[0]), Negation(v[1])))
    
    def subsumption(self, v):
        return Subsumption(*v)

    def equivalence(self, v):
        return Conjunction(Subsumption(v[0], v[1]),Subsumption(v[1], v[0]))

    def description_local(self, v):
        return Description_Local(*v)

    def description_global(self, v):
        return Description_Global(*v)

    def top(self, v):
#        return Negation(Conjunction(Atom('Spec_atom_top_bot'), Negation(Atom('Spec_atom_top_bot'))))
        return Atom('Spec_atom_top')
    
    def bot(self, v):
        return Conjunction(Atom('Spec_atom_bot'), Negation(Atom('Spec_atom_bot')))



###############################
#FORMULA OBJECT-----------------------
#################################


class Formula():
    """Main formula class"""
    
    
    @property
    def atom_symbols(self):
        """ Returns the list of atoms present in any formula."""
        return list(self.atoms.keys())

    def transform(self, transformer):
        """ Technical function needed by the Lark library for parsing."""
        return transformer(self)

    def binary_count(self) -> int:
        """ Returns the number of binary connectives (excluding global descriptions) present in any formula (defined separately for each formula subclass)."""
        pass

    def binary_descr_global_count(self) -> int:
        """ Returns the number of all binary connectives in any formula (defined separately for each formula subclass)."""
        return self.binary_count() + self.descr_global_count()

    def descr_global_count(self) -> int:
        """ Returns the number of global descriptions present in any formula (defined separately for each formula subclass)."""
        pass

    def descr_local_count(self) -> int:
        """ Returns the number of local descriptions present in any formula (defined separately for each formula subclass)."""
        pass

    def descr_global_local_count(self) -> int:
        """ Returns the number of descriptions present in any formula."""
        return self.descr_local_count() + self.descr_global_count()

    def modal_count(self) -> int:
        """ Returns the number of modalities present in any formula (defined separately for each formula subclass)."""
        pass

    def modal_degree(self) -> int:
        """ Returns the modal degree (or modal depth) of any formula (defined separately for each formula subclass)."""
        pass

    def occur_var_count(self) -> int:
        """ Returns the number of occurrences of atoms in any formula."""
        return self.binary_descr_global_count() + 1
    
    def var_count(self) -> int:
        """ Returns the number of different atoms present in any formula."""
        return len(self.atom_symbols)

    def complexity_score(self) -> int:
        """ Returns the "complexity score" of a formula, reflecting the relative runtime of the prover for this formula """
        return self.descr_global_local_count()*2 + self.occur_var_count() + self.modal_count() + self.modal_degree()


#może będzie jeszcze potrzebne
#    def max_depth(self) -> int:
#        pass

#    def structural_balance(self) -> int:
#        pass

#    def var_weight(self) -> int:
#        return self.var_count() / self.occur_var_count()     



    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        """ Prints the formula in a "nice looking" form (defined separately for each formula subclass)."""
        pass

    def formula_string(self) -> str:
        """ Returns the formula in the same form as the functions __str__, but as a string to be further manipulated - not just a print-out (defined separately for each formula subclass)."""
        pass
    
    def __repr__(self) -> str:
        """ Returns a representation of a formula in a form (defined separately for each formula subclass)."""
        pass


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        """ Function necessary to implement equality of formulas."""
        pass



#ATOM-------------------------------------

class Atom(Formula):
    #_latex: str | None
    """Class for atomic formulas"""

    def __init__(self, atom_string: str):
        self.atom_string = atom_string

#poniższe - do FOL? jakie ze starej wersji
#        if isinstance(constant_or_nonzero, list):
#            self.predicate, self.terms = (
#                str(constant_or_nonzero[0]),
#                tuple(map(str, constant_or_nonzero[1:])),
#            )
#        else:
#            constant = constant_or_nonzero
#            self.predicate = str(constant)
#            self.terms = []
#        self._latex = latex



#poniższe - znów do FOL?
# =============================================================================
#     @property
#     def symbol(self) -> str:
#         if len(self.terms) == 0:
#             return f"{self.predicate}"
#         else:
#             return f"{self.predicate}({', '.join(self.terms)})"
# 
# =============================================================================

# =============================================================================
#     @property
#     def free_terms(self):
#         return self.terms
# 
#     def replace_term(self, replaced_term, replacing_term):
#         fml = self
#         fml.terms = [
#             replacing_term if term == replaced_term else term for term in self.terms
#         ]
#         return fml
# =============================================================================



    @property
    def atoms(self):
        return {str(self.atom_string): [self]}


    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        return f"{self.atom_string}"

    def formula_string(self) -> str:
        return f"{self.atom_string}"

    def __repr__(self) -> str:
        return f"Atom[{self.atom_string}]"

#    def latex(self):
#        return f"{self._latex or self.symbol}"
#        return f"{self.latex or self.atom_string}"
#        return f"{self.atom_string}"


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return ((self.atom_string == other.atom_string) if isinstance(other, Atom) else False) 

    def __hash__(self):
        return hash(self.atom_string)


    #FUNCTIONS  REFLECTING STRUCTURAL PROPERTIES

    def binary_count(self) -> int:
        return 0

    def descr_global_count(self) -> int:
        return 0

    def descr_local_count(self) -> int:
        return 0

    def modal_count(self) -> int:
        return 0

    def modal_degree(self) -> int:
        return 0



#UNARY FORMULAS-------------------------------------


class Unary(Formula):
    """Class for unary formulas"""
    
    def __init__(self, sub: Formula):
        self.sub = sub   #attribute for the subformula

    @property
    def atoms(self):
        return self.sub.atoms



    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        return self.connective + (
            f"({self.sub})" if isinstance(self.sub, Binary) else f"{self.sub}"
        )

    def formula_string(self) -> str:
        return self.connective + (
            f"({self.sub})" if isinstance(self.sub, Binary) else f"{self.sub}"
        )

    def __repr__(self) -> str:
        return f"{self.signature}[{repr(self.sub)}]"


#    def latex(self):
#        return f"{self.connective_latex} " + (
#            f"({self.sub.latex()})"
#            if isinstance(self.sub, Binary)
#            else f"{self.sub.latex()}"
#        )


    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def binary_count(self) -> int:
        return self.sub.binary_count()

    def descr_global_count(self) -> int:
        return self.sub.descr_global_count()

    def modal_count(self) -> int:
        return self.sub.modal_count()

    def modal_degree(self) -> int:
        return self.sub.modal_degree()



#NEGATION--------------------------------------

class Negation(Unary):
    """Class for negations"""
    signature = "Neg"   #used for the "__repr__" function
    connective = "¬"    #used for "__str__" and "formula_string" functions
#    connective_latex = r"\neg"


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return ((self.sub == other.sub) if isinstance(other, Negation) else False) 

    def __hash__(self):
        return hash(self.sub)


    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def descr_local_count(self) -> int:
        return self.sub.descr_local_count()



#LOCAL DEFINITE DESCRIPTION------------------------

class Description_Local(Unary):
    """Class for local definite descriptions"""
    signature = "Desc_Loc"   #used for the "__repr__" function
    connective = "i."     #used for "__str__" and "formula_string" functions
    #connective_latex = r"\iota ."

    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return ((self.sub == other.sub) if isinstance(other, Description_Local) else False) 

    def __hash__(self):
        return hash(self.sub)


    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def descr_local_count(self) -> int:
        return self.sub.descr_local_count() + 1



#DIAMOND -------------------------------

class Diamond(Formula):
    """ Class for modal formulas of the form "Ǝ modality_type Formula" """
    signature = "Diamond"  #used for the "__repr__" function
    connective = "Ǝ "  #used for "__str__" and "formula_string" functions
    #connective_latex = r"\exists"

    def __init__(self, sub1, sub2: Formula):
       self.role = str(sub1)  #attribute for the modality type (role - in the jargon of description logic)
       self.sub2 = sub2       #attribute for the subformula


    @property
    def atoms(self):
        return self.sub2.atoms



    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        return self.connective + self.role + " " + (
            f"({self.sub2})"
            if isinstance(self.sub2, Binary)  | isinstance(self.sub2, Diamond) | isinstance(self.sub2, Description_Local)            
            else f"{self.sub2}"
        )


    def formula_string(self) -> str:
        return self.connective + self.role + " " + (
            f"({self.sub2})"
            if isinstance(self.sub2, Binary)  | isinstance(self.sub2, Diamond) | isinstance(self.sub2, Description_Local)            
            else f"{self.sub2}"
        )

    def __repr__(self) -> str:
        return f"{self.signature}[{self.role} {repr(self.sub2)}]"


#    def latex(self):
#        return f"{self.connective_latex} " + f"{self.role}" + "." + (
#            f"({self.sub2.latex()})"
#            if isinstance(self.sub2, Binary) | isinstance(self.sub2, Diamond) | isinstance(self.sub2, Description_Local) 
#            else f"{self.sub2.latex()}"
 #       )


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return ((self.role == other.role and self.sub2 == other.sub2) if isinstance(other, Diamond) else False) 

    def __hash__(self):
        return hash((self.role, self.sub2))



    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def binary_count(self) -> int:
        return self.sub2.binary_count()

    def descr_global_count(self) -> int:
        return self.sub2.descr_global_count()

    def descr_local_count(self) -> int:
        return self.sub2.descr_local_count()

    def modal_count(self) -> int:
        return self.sub2.modal_count() + 1

    def modal_degree(self) -> int:
        return self.sub2.modal_degree() + 1



#BINARY FORMULAS ---------------------------------------------

class Binary(Formula):
    """ Class for binary formulas (conjunction and subsumption)"""
    """ Two attributes subs[0] and subs[1] for both subformulas"""
    subs: tuple[Formula, Formula]

    def __init__(self):
        pass

    @property
    def atoms(self):
        atoms = dict()
        for subfml in self.subs:
            for k, v in subfml.atoms.items():
                atoms[k] = atoms.get(k, []) + v
        return atoms



    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        return f"{self.connective}".join(
            map(
                lambda x: f"({x})" if isinstance(x, Binary) else f"{x}",
                self.subs,
            )
        )

    def formula_string(self) -> str:
        return f"{self.connective}".join(
            map(
                lambda x: f"({x})" if isinstance(x, Binary) else f"{x}",
                self.subs,
            )
        )

    def __repr__(self) -> str:
        return "{}[{}]".format(
            self.signature, ", ".join(map(lambda x: repr(x), self.subs))
        )


#    def latex(self):
#        return f" {self.connective_latex} ".join(
#            map(
#                lambda x: f"({x.latex()})" if isinstance(x, Binary) else f"{x.latex()}",
#                self.subs,
#            )
#        )


    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def binary_count(self) -> int:
        return self.subs[0].binary_count() + self.subs[1].binary_count() + 1

    def descr_global_count(self) -> int:
        return self.subs[0].descr_global_count() + self.subs[1].descr_global_count()

    def descr_local_count(self) -> int:
        return self.subs[0].descr_local_count() + self.subs[1].descr_local_count()

    def modal_count(self) -> int:
        return self.subs[0].modal_count() + self.subs[1].modal_count()

    def modal_degree(self) -> int:
        return max(self.subs[0].modal_degree(), self.subs[1].modal_degree())



#CONJUNCTION----------------------------------

class Conjunction(Binary):
    """ Class for Conjunctions """
    signature = "Conj"   #used for the "__repr__" function
    connective = "∧"    #used for "__str__" and "formula_string" functions
    #connective_latex = r"\land"

    def __init__(self, sub1: Formula, sub2: Formula):
        self.subs = (sub1, sub2)


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return ((self.subs[0] == other.subs[0] and self.subs[1] == other.subs[1]) or (self.subs[0] == other.subs[1] and self.subs[1] == other.subs[0]) if isinstance(other, Conjunction) else False)

    def __hash__(self):
        return hash(self.subs)


#!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!To do!!!!!!!!!!!!!!!!!!!!!!!!!!!!
#DISJUNCTION----------------------------------


#class Disjunction(Binary):
#    signature = "Disj"
#    connective = "∨"
#    connective_latex = r"\lor"

 #   def __init__(self, sub1: Formula, sub2: Formula):
#        self.subs = (sub1, sub2)
        

    #ATTRIBUTES FOR EQUALITY
    
 #   def __eq__(self,other):
#        return ((self.subs[0] == other.subs[0] and self.subs[1] == other.subs[1]) or (self.subs[0] == other.subs[1] and self.subs[1] == other.subs[0]) if isinstance(other, Disjunction) else False)

 #   def __hash__(self):
 #       return hash(self.subs)
#



#SUBSUMPTION----------------------------------


class Subsumption(Binary):
    """ Class for Subsumptions """
    signature = "Subsum"   #used for the "__repr__" function
    connective = "→"     #used for "__str__" and "formula_string" functions
    #connective_latex = r"\sqsubseteq"  

    def __init__(self, sub1: Formula, sub2: Formula):
        self.subs = (sub1, sub2)


    #FUNCTIONS FOR EQUALITY
    
    def __eq__(self,other):
        return (self.subs[0] == other.subs[0] and self.subs[1] == other.subs[1] if isinstance(other, Subsumption) else False)

    def __hash__(self):
        return hash(self.subs)



#GLOBAL DEFINITE DESCRIPTION------------------------


class Description_Global(Binary):
    """ Class for Global descriptions """
    signature = "Desc_Glob"   #used for the "__repr__" function
    connective = "i "         #used for "__str__" and "formula_string" functions
    #connective_latex = r"\iota"

    def __init__(self, sub1: Formula, sub2: Formula):
        self.subs = (sub1, sub2)



    #FUNCTIONS RELATED TO FORMULA REPRESENTATION

    def __str__(self) -> str:
        return self.connective + (
            f"({self.subs[0]})"
            if isinstance(self.subs[0], Binary)
            else f"{self.subs[0]}"
            ) + "." + (
            f"({self.subs[1]})"
            if isinstance(self.subs[1], Binary)
            else f"{self.subs[1]}"
        )

    def formula_string(self) -> str:
        return self.connective + (
            f"({self.subs[0]})"
            if isinstance(self.subs[0], Binary)
            else f"{self.subs[0]}"
            ) + "." + (
            f"({self.subs[1]})"
            if isinstance(self.subs[1], Binary)
            else f"{self.subs[1]}"
        )
                
    def __repr__(self) -> str:
        return "{}[{}]".format(
            self.signature, ", ".join(map(lambda x: repr(x), self.subs))
        )


#    def latex(self):
#        return f"{self.connective_latex} " + (
#            f"({self.subs[0].latex()})"
#            if isinstance(self.subs[0], Binary)
#            else f"{self.subs[0].latex()}"
#            ) + "." + (
#            f"({self.subs[1].latex()})"
#            if isinstance(self.subs[1], Binary)
#            else f"{self.subs[1].latex()}"
#        )



    #FUNCTIONS FOR EQUALITY

    def __eq__(self,other):
        return(self.subs[0] == other.subs[0] and self.subs[1] == other.subs[1] if isinstance(other, Description_Global) else False)

    def __hash__(self):
        return hash(self.subs)



    #FUNCTIONS REFLECTING STRUCTURAL PROPERTIES

    def binary_count(self) -> int:
        return self.subs[0].binary_count() + self.subs[1].binary_count()

    def descr_global_count(self) -> int:
        return self.subs[0].descr_global_count() + self.subs[1].descr_global_count() + 1








####################################
#additional functions - transformations on formulas


#unfold a concjunction (with potentially many sub-conjunctions) in a set
def unfold_conjunction(conj):
    out = {conj.subs[0], conj.subs[1]}
    set = out
    for form in set:
        if isinstance(form, Conjunction):
            out = (out-{form}) | unfold_conjunction(form)
    return(out)

#fold a set of formulas/concepts (implicitely forming a conjunction) back into a conjunction object
def fold_into_conjunction(conj_set):
    
    if len(conj_set) ==1:
        return(conj_set.pop())    
        
    conj1 = conj_set.pop()
    conj2 = conj_set.pop()
    conj_out = Conjunction(conj1, conj2)

    if len(conj_set) < 1:
        return(conj_out)
    else:
        for i in range(len(conj_set)):
            conj_out = Conjunction(conj_out, conj_set.pop())
    
    return(conj_out)


def negate_formula(form):
    if isinstance(form, Negation):
        return(form.sub)
    else:
        return(Negation(form))



#unfold a concjunction (with potentially many sub-conjunctions) in a set of alternatives (clause)
def unfold_neg_conj_into_set_of_alt(neg_conj):
    out = {negate_formula(neg_conj.sub.subs[0]), negate_formula(neg_conj.sub.subs[1])}
    set = out
    for form in set:
        if isinstance(form, Negation) and isinstance(form.sub, Conjunction):
            out = (out-{form}) | unfold_neg_conj_into_set_of_alt(form)
    return(out)



