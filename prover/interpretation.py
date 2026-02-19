
class World:
    """Class for individuals/ Kripke worlds"""
    __slots__ = '_formulas','_world_name_str', '_box_subformulas', '_candidates_blocking', '_Tbox_unfold_list_alt'

    def __init__ (self, x):
        #Do not call constructor directly. Use Interpretations' add_world(x).”””
        self._formulas = x   #set (or list) of formulas satisfied in the world
        self._world_name_str = None    #world name as a string object - serves to identify the world
        self._box_subformulas = {} #a dictionary with modality types 'r' as keys; values are sets of formulas A, such that ~*E r A are satisfied in this world
        self._candidates_blocking = {} #a dictionary with worlds as keys; values are dictionaries with roles as keys, and as values - the blocked formulas of type *E r A, where r is the role in the key; the world in the primary key is a 'candidate' world with respect to all of the corresponding formulas
        self._Tbox_unfold_list_alt = list()                        
                        
    def formulas(self):
        """Return formulas associated with this world."""
        return (set.union(*self._formulas.values()) if isinstance(self._formulas, dict) else self._formulas) 

    def __hash__ (self): # will allow worlds to be a map/set key
        return hash(id(self))



class Interpretation:
    """Class for the whole Interpretation (Kripke structure). Each interpretation corresponds to a branch of the tableau"""
    def __init__ (self):
        #Create an empty Interpretation.
        self._outgoing = {} #a dictionary with worlds as keys; values are dictionairies with world as keys and sets of strings indicating modality types of outgoing edges as values
        self._incoming = {} #a dictionary with worlds as keys; values are dictionairies with world as keys and sets of strings indicating modality types of incoming edges as values
        self._world_names_str  = set()   #set of all world names  in the interpretation
        self._GlDesc_rule3_fml_set = set()   #set of formulas C, such that the tableua rule for the negation of a global description has been applied to a some formula iC.D in this interpretation 
        self._LocDesc_rule3_list = [list(), list()]  ##set of formulas C, such that the tableua rule for the negation of a local description has been applied to a some formula i.C in this interpretation
        self._optimisations = tuple() #choice of optimisations used by the prover will be also saved as an attribute of the interpretation
        self._Tbox_unfold_subs = set()
        self._Tbox_fold_subs = set()
        self._Tbox_fold_eq = set()
        self._Tbox_fold_subs_conj = list()
        self._Tbox_fold_subs_neg = set()
        self._Tbox_fold_subs_ex_restr = set()
        self._Tbox_unfold_global = list()
        self._worlds_to_unify = list()


    def worlds(self):
        """Return an iteration of all worlds of the Interpretation."""
        return self._outgoing.keys()

    def add_world(self, x: list):
        """Insert and return a new world with element x.
        
        Argument: auxilliary element - list of formulas satisfied in the world
        
        Output: the world object itself
        """
        w = World(x)
        self._outgoing[w] = {}
        self._incoming[w] = {} # need distinct map for incoming edges
        return w  

    def add_edge(self, u, w, x: str):
        """Insert and return a new world with element x.
        
        Arguments:
            u: origin world of the edge
            w: destination world of the edge
            x: auxilliary element - modality type associated with the edge (given as a string)
        
        Output: the world object itself
        """
        self._outgoing[u][w] = {x} if w not in self._outgoing[u] else self._outgoing[u][w].union({x})
        self._incoming[w][u] = {x} if u not in self._incoming[w] else self._incoming[w][u].union({x})

    def edge_exists(self, w: World, x: str):
        """Check if there exists any edge of modality type x outgoing from the world w.
        
        Arguments:
            w: origin world for which we check, if edges of modality type x exist
            x: modality type (given as a string)
        
        Output: True if any edge exists, False otherwise
        """
        return any({x in i for i in self._outgoing[w].values()})

    def related_worlds(self, w: World, x: str):
        """Which worlds are connected with with the given world w (as origin) with the modality type x
        
        Arguments:
            w: origin world 
            x: modality type (given as a string)
        
        Output: List of world connected with the world w (as origin) with the modality type r 
        """
        worlds = list() 
        for world, edge_types in self._outgoing[w].items():
            if x in edge_types:
                worlds.append(world)
        return(worlds)


    def unrelated_worlds(self, w: World, x: str):
        """Which worlds are not connected with with the given world w (as origin) with the modality type x
        
        Arguments:
            w: origin world
            x: modality type (given as a string)
        
        Output: List of world not connected with the world w (as origin) with the modality type r 
        """
        return(list(set(self._outgoing.keys()) - set(self.related_worlds(w,x))))

                

