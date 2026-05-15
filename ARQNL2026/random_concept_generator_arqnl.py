import random
import numpy as np


# no_atoms = 10
# no_diff_atoms = 5
# no_modal = 4
# no_LD = 10
# GD_chance = 0.3
# GD_count = 3
# #modal_depth



#PREPARATION
def random_ALCi_concept_str(no_atoms, 
                             no_diff_atoms,
                             no_modal,
                             no_LD,
                             GD_chance = None,
                             GD_count = None,
                             neg_chance = 0.5):
    """ This is the main function of the generator, it creates a random formula with the geven parameters
    
    Arguments:
        no_atoms: number of occurrences of atoms
        no_diff_atoms: number of different atoms
        no_modal: number of modal operators
        no_LD: number of local descriptions
        GD_count: number of global descriptions
        GD_chance: a chance of a binary connective being a global description (can be used instead of GD_count, if both are filled, only GD_count is used)
        neg_chance: chance of any subformula being a negation

    Output: 
        a string representation of a formula
    
    """

    
    #either GD_chance or GD_count is to be used; we assume GD_count is the default. Thus if both are set to None - GD_count is set to 1. If both are filled - only GD_count is used
    if GD_chance is None and GD_count is None:
        GD_count = 1
    elif GD_chance is not None and GD_count is not None:
        GD_chance = None
        
        
    no_inn_nodes = no_atoms - 1

    
    #creating the list of atoms
    aval_atoms = ["A"+ str(k) for k in range(1, no_diff_atoms+1) ] #available atom symbols
    atoms = aval_atoms + random.choices(aval_atoms, k= no_atoms - no_diff_atoms)
    random.shuffle(atoms)
    atoms = np.array(atoms)

    negations_atoms = [random.choice([True, False]) for _ in range(no_atoms)]    
    negations_atoms = np.array(["~" if k else "" for k in negations_atoms])
    atoms_final = np.char.add(negations_atoms, atoms)


    #creating the list of modalities
    modalities = np.full(no_modal, "*E r ")
    local_desc = np.full(no_LD, "i.")
    one_arg_conns = np.concatenate([modalities, local_desc])
    random.shuffle(one_arg_conns)
    one_arg_conns = np.array(one_arg_conns)

    one_arg_conns_negations = [random.choice([True, False]) for _ in range(no_modal + no_LD)]    
    one_arg_conns_negations = np.array(["~" if k else "" for k in one_arg_conns_negations])
    one_arg_conns_final = np.char.add(one_arg_conns_negations, one_arg_conns)


    #preparing the redistribution of 1-arg connectives between the atoms and the 2-arg connectives
    one_arg_conns_distr = random.choices(range(1, no_atoms + no_inn_nodes + 1), k=len(one_arg_conns_final))
    
    one_arg_string_list = list()
    
    #create a list of pairs (2-element lists), one for each leaf (=for each 1-argument connective), with strings to attach to the right and left to create a subformula
    for i in range(1, no_atoms + no_inn_nodes+1):
    
        indexes = []
        for index, value in enumerate(one_arg_conns_distr):
            if value == i:
                indexes.append(index)
    
        ind = one_arg_conns_final[indexes]
        ind_len = len(one_arg_conns_final[indexes])
    
        if ind_len==0:
            left = ""
            right = ""
        else:
            left = "".join([item for pair in zip(ind, "("*ind_len) for item in pair])
            right = ")"*ind_len
        
        one_arg_string_list.append([left,right])
    
    
    #creating final strings for leaves of the tree
    atoms_final = list(atoms_final)
    
    for i in range(0, len(atoms_final)):
        atoms_final[i] = one_arg_string_list[i][0] + atoms_final[i] + one_arg_string_list[i][1]
    
    #cutting the list of strings to those that we need for the 2-arg connectives
    one_arg_string_list_2arg = one_arg_string_list[len(atoms_final):no_atoms + no_inn_nodes+1]


    if GD_count is not None:
        two_arg_conn_list = ["global_desc"]*GD_count + ["conjunction"]*(no_inn_nodes - GD_count)
        random.shuffle(two_arg_conn_list)
        two_arg_conn_list = np.array(two_arg_conn_list)
        two_arg_negations = [random.choice([True, False]) for _ in range(no_inn_nodes)]
        two_arg_negations = np.array(["_neg" if k else "" for k in two_arg_negations])
        two_arg_conns_final = np.char.add(two_arg_conn_list, two_arg_negations)
        two_arg_conns_final = list(two_arg_conns_final)
    else:
        two_arg_conns_final= list()
        for i in range(1, no_inn_nodes+1):
            two_arg_conns_final.append(two_arg_conn_type_random(GD_chance=GD_chance, neg_chance=neg_chance))

    
    rb_tree = random_bin_formula_tree(no_inn_nodes, atoms_final, two_arg_conns_final)

    return(create_formula_string(rb_tree, one_arg_string_list_2arg))


    


class TreeNode: 
    """ Class of a tree node - used in building the random syntax tree, that is the base for the random formula"""
    def __init__(self, value, left=None, right=None): 
        self.value = value 
        self.left = left
        self.right = right


def random_bin_formula_tree(no_inn_nodes, atoms_final, two_arg_conns_final):     
    """ Builds a random binary tree, with nodes filled with string values, that are to be become parts of the string object - formula
    
    Arguments:
        no_inn_nodes: number of inner nodes of the binary tree
        atoms_final: prepared strings that represent atoms (possibly precede by unary operators), to be placed in tree leaves
        two_arg_conns_final: prepared strings that represent two-argument connectives, to be placed in the inner nodes of the tree
    
    Output:
        binary tree with string values representing subformulas in all nodes      
    """
    # Choose random sizes for left and right subtrees 
    left_size = random.randint(0, no_inn_nodes-1) 
    right_size = no_inn_nodes - 1 - left_size 

    root = TreeNode(value = two_arg_conns_final.pop()) 

    if left_size == 0:
        root.left = TreeNode(value = atoms_final.pop())
    elif left_size == 1:
        root.left = TreeNode(value = two_arg_conns_final.pop(), 
                             left = TreeNode(value = atoms_final.pop()),
                             right = TreeNode(value = atoms_final.pop()))
    else:
        root.left = random_bin_formula_tree(left_size, atoms_final, two_arg_conns_final)

    if right_size ==0:
        root.right = TreeNode(value = atoms_final.pop())
    elif right_size == 1:
        root.right = TreeNode(value = two_arg_conns_final.pop(), 
                              left = TreeNode(value = atoms_final.pop()),
                              right = TreeNode(value = atoms_final.pop()))
    else:
        root.right = random_bin_formula_tree(right_size, atoms_final, two_arg_conns_final)        


    return root 



def create_formula_string(root, one_arg_string_list_2arg):
    """ creates a string representing a formula, given a binary tree and list of unary operators to be placed befoe the binary operators
    
    Arguments:
        root: this is a TreeNode object linked with other TreeNodes objects, that together form the binary tree created in the function random_bin_formula_tree
        one_arg_string_list_2arg: strings representing the unary operators to be placed befoe the binary operators
    
    Outputs:
        the random formula in the form of a string
    """
    if root.value == "global_desc":
        pair = one_arg_string_list_2arg.pop()
        root.value = root.value + pair[0] #for calculating the modal depth on a branch
        return(pair[0] + "(i (" + create_formula_string(root.left, one_arg_string_list_2arg)+").(" + create_formula_string(root.right, one_arg_string_list_2arg) + "))" + pair[1])
    elif root.value == "conjunction":
        pair = one_arg_string_list_2arg.pop()
        root.value = root.value + pair[0]  #for calculating the modal depth on a branch
        return(pair[0] + "((" + create_formula_string(root.left, one_arg_string_list_2arg)+")&(" + create_formula_string(root.right, one_arg_string_list_2arg) + "))" + pair[1])
    elif root.value == "global_desc_neg":
        pair = one_arg_string_list_2arg.pop()
        root.value = root.value + pair[0]  #for calculating the modal depth on a branch
        return(pair[0] + "(~i (" + create_formula_string(root.left, one_arg_string_list_2arg)+").(" + create_formula_string(root.right, one_arg_string_list_2arg) + "))" + pair[1])
    elif root.value == "conjunction_neg":
        pair = one_arg_string_list_2arg.pop()
        root.value = root.value + pair[0]   #for calculating the modal depth on a branch
        return(pair[0] + "~((" + create_formula_string(root.left, one_arg_string_list_2arg)+")&(" + create_formula_string(root.right, one_arg_string_list_2arg) + "))" + pair[1])
    else:
        return(root.value)





def two_arg_conn_type_random(GD_chance, neg_chance):
    """ output a string name for a binary connective
        used instead of GD_count - only if GD_count is set to None    
    
    Arguments:
        GD_chance: chance of a binary connective connective being a global description
        neg_chance: chance of a binary connective being negated
    
    Outpus: 
        Either of the string values:"global_desc", "global_desc_neg", "conjunction", "conjunction_neg", later used in building the random formula
    """
    p_GD = random.random()
    p_neg = random.random()
    if p_GD < GD_chance and p_neg < neg_chance:
        return("global_desc")
    elif p_GD < GD_chance and p_neg >= neg_chance:
        return("global_desc_neg")
    elif p_GD >= GD_chance and p_neg < neg_chance:
        return("conjunction")
    elif p_GD >= GD_chance and p_neg >= neg_chance:
        return("conjunction_neg")

