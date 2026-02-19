import forms


def absorb_unfolded_Tbox(Tbox_unfold_subs,
                         Tbox_fold_subs,
                         Tbox_fold_eq,
                         Tbox_fold_subs_conj,
                         Tbox_fold_subs_neg,
                         Tbox_fold_subs_ex_restr,
                         graph_Tbox_atoms):
    """ applies absorption optimalisation to TBox

        Argument:
            Tbox_unfold_subs: working data structure representing unfoldable Tbox
            Tbox_fold_subs:  working data structure representing subsumptions in foldable Tbox
            Tbox_fold_eq: working data structure representing equivalences in foldable Tbox
            Tbox_fold_subs_conj:  working data structure representing subsumptions in foldable Tbox, with conjunctions of atoms on the left side of the axiom
            Tbox_fold_subs_neg:  working data structure representing subsumptions in foldable Tbox, with negation of an atom on the left side of the axiom
            Tbox_fold_subs_ex_restr:  working data structure representing subsumptions in foldable Tbox, with existential restriction on the left side of the axiom
            graph_Tbox_atoms:  working data structure representing the dependency graph used to check if Tbox is acyclic

        Output:
            the output is the same set of objects as in the input, modified
    """    
    
    for pair in list(Tbox_unfold_subs):

        
        #1. conjunctions: binary absorption

        if isinstance(pair[0], forms.Conjunction):
            conj_set = forms.unfold_conjunction(pair[0]) #unfold the Conjunction into set of its elements
            conj_set_atoms = {x for x in conj_set if isinstance(x, forms.Atom)}
            conj_set_non_atoms = {x for x in conj_set if not isinstance(x, forms.Atom)}

            #creating sets of string representations of atoms (for the dependency graph)
            conj_set_atoms_str = {atom.formula_string() for atom in conj_set_atoms}
            conj_set_non_atoms_str = set()
            for form in conj_set_non_atoms:
                x = set(form.atom_symbols) 
                conj_set_non_atoms_str.update(x)

            if len(conj_set_atoms)==0:
                continue
            elif len(conj_set_atoms)==1:
                Tbox_fold_subs.update({(conj_set_atoms.pop(),
                                        forms.Negation(forms.Conjunction(forms.fold_into_conjunction(conj_set_non_atoms),
                                                                         forms.Negation(pair[1]))))})

                Tbox_unfold_subs.remove(pair)
                
            elif len(conj_set_atoms)>1:
                if len(conj_set_non_atoms)==0:
                    Tbox_fold_subs_conj.append((conj_set_atoms, pair[1]))
                else:
                    Tbox_fold_subs_conj.append((conj_set_atoms,
                                                 forms.Negation(forms.Conjunction(forms.fold_into_conjunction(conj_set_non_atoms),
                                                                                  forms.Negation(pair[1])))))
                Tbox_unfold_subs.remove(pair)
                    
            #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
            for atom_str in conj_set_atoms_str:
                if atom_str in graph_Tbox_atoms.keys():
                    graph_Tbox_atoms[atom_str] = graph_Tbox_atoms[atom_str].union(conj_set_non_atoms_str | set(pair[1].atom_symbols))
                else:
                    graph_Tbox_atoms.update({atom_str: conj_set_non_atoms_str | set(pair[1].atom_symbols)})


        #2. negations: negative absorption 
        elif isinstance(pair[0], forms.Negation) and isinstance(pair[0].sub, forms.Atom):
            Tbox_fold_subs_neg.update({(pair[0], pair[1])})

            #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
            if pair[0].sub.formula_string() in graph_Tbox_atoms.keys():
                graph_Tbox_atoms[pair[0].sub.formula_string()] = graph_Tbox_atoms[pair[0].sub.formula_string()].union(set(pair[1].atom_symbols))
            else:
                graph_Tbox_atoms.update({pair[0].sub.formula_string(): set(pair[1].atom_symbols)})


            Tbox_unfold_subs.remove(pair)


        #3. existential restriction: role absorption
        
        elif isinstance(pair[0], forms.Diamond):
            
            #top is represented by a special atom 
            if pair[0].sub2.formula_string() == "Spec_atom_top":
                Tbox_fold_subs_ex_restr.update({(pair[0].role,
                                                 pair[1])})
                
            else:
                Tbox_fold_subs_ex_restr.update({(pair[0].role,
                                                 forms.Negation(forms.Conjunction(forms.Negation(pair[1]),
                                                                                  pair[0])))})

            Tbox_unfold_subs.remove(pair)
    

    return(Tbox_unfold_subs,
           Tbox_fold_subs,
           Tbox_fold_eq,
           Tbox_fold_subs_conj,
           Tbox_fold_subs_neg,
           Tbox_fold_subs_ex_restr,
           graph_Tbox_atoms)






def ensure_uniqueness(Tbox_fold_eq,
                      Tbox_unfold_subs,
                      graph_Tbox_atoms):
    """ ensures that no atoms appears twice on the left hand side of an equivalence axiom

        Argument:
            Tbox_unfold_subs: working data structure representing unfoldable Tbox
            Tbox_fold_eq: working data structure representing equivalences in foldable Tbox
            graph_Tbox_atoms:  working data structure representing the dependency graph used to check if Tbox is acyclic

        Output:
            the output is the same set of objects as in the input, modified
    """        

    atoms_in_eq = set()
    
    
    for pair in list(Tbox_fold_eq):
        if pair[0] in atoms_in_eq:
            Tbox_fold_eq.remove(pair)

            #splitting the equivalence in two subsumptions and moving to the unfoldadable part
            Tbox_unfold_subs.update({(pair[0], pair[1]), (pair[1], pair[0])})

            graph_Tbox_atoms[pair[0].formula_string()] = graph_Tbox_atoms[pair[0].formula_string()].difference(set(pair[1].atom_symbols))
            
        else:
            atoms_in_eq.update({pair[0]})
        
    return(Tbox_fold_eq,
           Tbox_unfold_subs,
           graph_Tbox_atoms)






def ensure_Tbox_acyclic(Tbox_unfold_subs,
                        Tbox_fold_subs,
                        Tbox_fold_eq,
                        Tbox_fold_subs_conj,
                        Tbox_fold_subs_neg,
                        Tbox_fold_subs_ex_restr,
                        graph_Tbox_atoms):
    """ checks if the Tbox contains cycles

        Argument:
            Tbox_unfold_subs: working data structure representing unfoldable Tbox
            Tbox_fold_subs:  working data structure representing subsumptions in foldable Tbox
            Tbox_fold_eq: working data structure representing equivalences in foldable Tbox
            Tbox_fold_subs_conj:  working data structure representing subsumptions in foldable Tbox, with conjunctions of atoms on the left side of the axiom
            Tbox_fold_subs_neg:  working data structure representing subsumptions in foldable Tbox, with negation of an atom on the left side of the axiom
            Tbox_fold_subs_ex_restr:  working data structure representing subsumptions in foldable Tbox, with existential restriction on the left side of the axiom
            graph_Tbox_atoms:  working data structure representing the dependency graph used to check if Tbox is acyclic

        Output:
            the output is the same set of objects as in the input, modified
    """        
    #first, for the functions defined on the dependency graph to work correctly, we need to make sure all the atoms in a graph has a key in the dictionary graph_Tbox_atoms

    if len(graph_Tbox_atoms.keys()) == 0:
        return(Tbox_unfold_subs,
               Tbox_fold_subs,
               Tbox_fold_eq,
               Tbox_fold_subs_conj,
               Tbox_fold_subs_neg,
               Tbox_fold_subs_ex_restr,
               graph_Tbox_atoms,
               0)
        

    all_atoms_in_graph = set.union(*graph_Tbox_atoms.values())
    for atom in all_atoms_in_graph:
        if atom not in graph_Tbox_atoms.keys():
            graph_Tbox_atoms[atom] = set()
    
    #set of atoms to delete from left side of axioms, in order to make the Tbox acyclic
    atoms_in_cycles = atoms_to_delete(graph_Tbox_atoms)

    no_atoms_in_cycles = len(atoms_in_cycles)

    if no_atoms_in_cycles == 0:
        return(None)

    for axiom in list(Tbox_fold_subs):
        if axiom[0].formula_string() in atoms_in_cycles:
            Tbox_fold_subs.remove(axiom)
            Tbox_unfold_subs.update({axiom})
            
    for axiom in list(Tbox_fold_eq):
        if axiom[0].formula_string() in atoms_in_cycles:
            Tbox_fold_eq.remove(axiom)
            Tbox_unfold_subs.update({(axiom[0], axiom[1]), (axiom[1], axiom[0])})
    
    Tbox_fold_subs_conj_copy = Tbox_fold_subs_conj
    for axiom in Tbox_fold_subs_conj_copy:
        if len(atoms_in_cycles.intersection(axiom[0]))>0:
            Tbox_fold_subs_conj.remove(axiom)
            Tbox_unfold_subs.update({axiom})
    del Tbox_fold_subs_conj_copy
    
    for axiom in list(Tbox_fold_subs_neg):
        if axiom[0].sub.formula_string() in atoms_in_cycles:
            Tbox_fold_subs.remove(axiom)
    
            Tbox_unfold_subs.update({axiom})
    
    
    return(Tbox_unfold_subs,
           Tbox_fold_subs,
           Tbox_fold_eq,
           Tbox_fold_subs_conj,
           Tbox_fold_subs_neg,
           Tbox_fold_subs_ex_restr,
           graph_Tbox_atoms,
           no_atoms_in_cycles)
    
    


def find_cycle_node(graph):
    """
    Detects a cycle in a directed graph.
 
    Argument:
        graph: dependency graph
        
    Output:
        Returns a node that belongs to a cycle, or None if no cycle exists.
   """
    visited = set()
    in_stack = set()

    def dfs(node):
        visited.add(node)
        in_stack.add(node)

        for neigh in graph[node]:
            if neigh not in visited:
                result = dfs(neigh)
                if result is not None:
                    return result
            elif neigh in in_stack:
                # Found a back edge → neigh is part of a cycle
                return neigh

        in_stack.remove(node)
        return None

    # Graph may be disconnected
    for node in graph:
        if node not in visited:
            cycle_node = dfs(node)
            if cycle_node is not None:
                return cycle_node

    return None




def reduced_graph(graph, cycle_node):
    """
    Generates an updated dependency graph, with specific nodes not connected by a (directed) edge
 
    Argument:
        graph: dependency graph
        cycle_node: a node, represented by a string
        
    Output:
        updated dependeny graph
   """
   
   
    del graph[cycle_node]
    
    for x, y  in graph.items():        
        graph[x] = y.difference({cycle_node})

    return(graph)




def atoms_to_delete(graph):
    """
    finds a node, which is responsible for a cycle
 
    Argument:
        graph: dependency graph
        
    Output:
        Returns a list of atoms (strings representing them) that need to be deleted from the dependency graph to avoid cycles
   """
    cycle_nodes_all = set()

    def list_of_atoms_to_delete(graph):
        cycle_node = find_cycle_node(graph)
        
        if cycle_node is None:
            return cycle_nodes_all
        else:
            cycle_nodes_all.update({cycle_node})
            return(list_of_atoms_to_delete(reduced_graph(graph, cycle_node)))

    return(list_of_atoms_to_delete(graph))
