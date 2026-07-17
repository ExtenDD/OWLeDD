import forms
from copy import deepcopy
import add_functions


def relocate_to_new_fml_sets(formulas_dict, new_fml):
    """ Place each new formula, that appeared in a given world as a result of applying a rule, in one of the subsets: 
    "new_fml_posit" of "new_fml_negat" - depending on whether it is a negation. This is done to limit applying the 
    clash rule to comparing those new formulas to all the others, already present in the world before applyting the 
    rule (this way we avoid repeating the same checks in the clash rule all over again)

    Arguments: 
        new_fml: a new formula, that appears in the world as an effect of applying a given rule    
        formulas_dict: an object of the form "w._formulas", where "w" is the world in which the new formula appears
            and "_formulas" is its attribute containing the dictionary of formulas
            
    Output:
        The set formulas_dict['new_fml_negat'] or formulas_dict['new_fml_posit'] is updated with the new concepts/formulas, 
        i.e. those that appeared on the branch as an effect of applying the current rule

    """
    if isinstance(new_fml, forms.Negation):
        formulas_dict['new_fml_negat'].update({new_fml}) 
    else:
        formulas_dict['new_fml_posit'].update({new_fml}) 



def choose_fml_to_branch_on(interpretation, w, fml1, fml2):
    """ Choose a concept/formula to place on a branch first, if the rule is non-deterministic (and so there is more than one choice)

    Arguments: 
        interpretation: current interpretation
        w: current world/individual
        fml1: first formula (option one in the non-deterministic rule)
        fml2: second formula (option two in the non-deterministic rule) 
    
    """
    
    if isinstance(fml1, forms.Negation) and isinstance(fml1.sub, forms.Diamond) and len(interpretation.related_worlds(w, fml1.sub.role))==0: #if a concept/formula is an universal restriction ("box"), and there are no world/individuals connected by the associated role, put this concept/formula on the branch first
        first_formula = fml1
        second_formula = fml2
    elif isinstance(fml2, forms.Negation) and isinstance(fml2.sub, forms.Diamond) and len(interpretation.related_worlds(w, fml2.sub.role))==0:
        first_formula = fml2
        second_formula = fml1
    elif fml2.complexity_score() > fml1.complexity_score():  #otherwise, use the complexity score (as defined in the script "forms") to decide which concept/formula should be put on the branch first
        first_formula = fml1
        second_formula = fml2
    elif fml1.complexity_score() > fml2.complexity_score():
        first_formula = fml2
        second_formula = fml1
    elif fml2.complexity_score() == fml1.complexity_score():
        first_formula = fml1
        second_formula = fml2
    
    
    return(first_formula, second_formula)





"""
All the functions below implement rules of the calculus TAB(ALCi). Each function takes an interpretation as an 
argument, and outpus 4 elements:

[0] the modified interpretation (Intepretation object)
[1] True if inconsistency was found (can happen only for the Clash rule), False otherwise
[2] True if the rule has been applied, False otherwise
[3] list of "alternative interpretations" that correspond to new branches of the tableau; for deterministic rules, this list is empty
    
"""




#CLASH RULE -------------------------------------------------


def clash_rule(interpretation):
    """ Function implementing the Clash rule"""
    
    
    for w in interpretation.worlds():
        
        #number of new formulas
        no_new_fmls = len(w._formulas['new_fml_posit'] | w._formulas['new_fml_negat'])

        
        if no_new_fmls == 0:
            continue #no new formulas, pass to the next world        

        else:
            #FIRST STEP
            #apply additional rules for foldable part of TBox
            if interpretation._optimisations[1] == True:  #apply if split between foldable and unfoldable TBox is used
                
                new_atoms = {atom for atom in w._formulas['new_fml_posit'] if isinstance(atom, forms.Atom)}
                new_neg_atoms = {natom for natom in w._formulas['new_fml_negat'] if isinstance(natom.sub, forms.Atom)}

                for pair in interpretation._Tbox_fold_subs:
                    for form in new_atoms:

                        if form == pair[0]:
                            if isinstance(pair[1], forms.Negation):
                                w._formulas['new_fml_negat'].update({pair[1]})
                            else:
                                w._formulas['new_fml_posit'].update({pair[1]})

            
                for pair in interpretation._Tbox_fold_subs_neg:
                    for form in new_neg_atoms:
                        if form == pair[0]:
                            if isinstance(pair[1], forms.Negation):
                                w._formulas['new_fml_negat'].update({pair[1]})
                            else:
                                w._formulas['new_fml_posit'].update({pair[1]})
                                
                                
                for pair in interpretation._Tbox_fold_eq:
                    for form in new_atoms:
                        if form == pair[0]:
                            if isinstance(pair[1], forms.Negation):
                                w._formulas['new_fml_negat'].update({pair[1]})
                            else:
                                w._formulas['new_fml_posit'].update({pair[1]})
                    
                    for form in new_neg_atoms:  #w._formulas['new_fml_negat']:
                        if form.sub == pair[0]:
                            if isinstance(pair[1], forms.Negation):
                                w._formulas['new_fml_negat'].update({pair[1]})
                            else:
                                w._formulas['new_fml_posit'].update({pair[1]})
                            
                            
                for pair in interpretation._Tbox_fold_subs_conj:
                    if pair[0] <= (new_atoms | w._formulas['atoms']):
                        if isinstance(pair[1], forms.Negation):
                            w._formulas['new_fml_negat'].update({pair[1]})
                        else:
                            w._formulas['new_fml_posit'].update({pair[1]})
            
            #SECOND STEP
            #here the clash rule is applied - search for pairs of contradictory formulas
            if no_new_fmls>1:   #check for consistency among the new formulas         
                fml_pairs_generator = ((new_posit_fml, new_negat_fml) for new_posit_fml in w._formulas['new_fml_posit'] for new_negat_fml in w._formulas['new_fml_negat'])         
    
                for pair in fml_pairs_generator:
                    if pair[0] == pair[1].sub:
                        return(interpretation, True, True, [])
            
            #positive new formulas vs negative formulas
            fml_pairs_generator = ((new_posit_fml, neg_fml) for new_posit_fml in w._formulas['new_fml_posit'] for neg_fml in (w._formulas['neg_atoms'] | w._formulas['neg_conjunction'] | w._formulas['neg_diamond'] | w._formulas['neg_global_desc'] | w._formulas['neg_local_desc'] | w._formulas['proc_negat']) )        

            for pair in fml_pairs_generator:
                if pair[0] == pair[1].sub:
                    return(interpretation, True, True, [])
                
            #negative new formulas vs positive formulas            
            fml_pairs_generator = ((new_negat_fml, pos_fml) for new_negat_fml in w._formulas['new_fml_negat']  for pos_fml in (w._formulas['atoms'] | w._formulas['conjunction'] | w._formulas['diamond'] | w._formulas['global_desc'] | w._formulas['local_desc'] | w._formulas['proc_posit'] | w._formulas['proc_global_desc'] | w._formulas['proc_local_desc']) )  

            for pair in fml_pairs_generator:
                if pair[0].sub == pair[1]:
                    return(interpretation, True, True, [])
            
            
            #THIRD STEP
            #this step is done only if SAT-inspired optimisations are used
            
            if interpretation._optimisations[2] == True:
                #the new negated conjunctions on the branch are turned into clauses (sets of formulas/concepts)
                new_neg_conjunctions = {nnc for nnc in w._formulas['new_fml_negat'] if isinstance(nnc.sub, forms.Conjunction)}
            
                #w._formulas['new_fml_negat'] = w._formulas['new_fml_negat'] - new_neg_conjunctions

                w._Tbox_unfold_list_alt.extend([forms.unfold_neg_conj_into_set_of_alt(neg_con) for neg_con in new_neg_conjunctions])

                #optimisation 1: 
                #e.g. if A on the branch, and {A, X} is a clause on the branch, delete {A, X} from the branch 
                for form in (w._formulas['new_fml_posit'] | w._formulas['new_fml_negat']):
                    w._Tbox_unfold_list_alt = [alt for alt in w._Tbox_unfold_list_alt if form not in alt]


                #optimisation 2: 
                #e.g. if ~A on the branch, and {A, X} is a clause on the branch, delete A from {A, X} 
                if w._formulas['new_fml_posit'] | w._formulas['new_fml_negat']:
                    
                    Tbox_unfold_new = list()
                    for alt in w._Tbox_unfold_list_alt:
                        
                        new_alt = alt
                        for pform in w._formulas['new_fml_posit']:
                            new_alt = {form for form in new_alt if pform != forms.negate_formula(form)}
                            
                        for nform in w._formulas['new_fml_negat']:
                            new_alt = {form for form in new_alt if nform.sub != form}
    
                        if len(new_alt) ==0:  #if a clause is empty - the branch is inconsistent!
                            return(interpretation, True, True, [])
                        else:
                            Tbox_unfold_new.append(alt)
    
                    w._Tbox_unfold_list_alt = Tbox_unfold_new

                    del(Tbox_unfold_new)


            #FOURTH STEP
            #update sets of formulas with the new formulas, and empty the "new formula sets"
            
            for new_fml in w._formulas['new_fml_negat']:
                if isinstance(new_fml.sub, forms.Negation):
                    w._formulas['double_neg'].update({new_fml}) 
                elif isinstance(new_fml.sub, forms.Atom):
                    w._formulas['neg_atoms'].update({new_fml}) 
                elif isinstance(new_fml.sub, forms.Conjunction):
                    w._formulas['neg_conjunction'].update({new_fml})
                elif isinstance(new_fml.sub, forms.Diamond):
                    w._formulas['neg_diamond'].update({new_fml})              
                elif isinstance(new_fml.sub, forms.Description_Global):
                    w._formulas['neg_global_desc'].update({new_fml})              
                elif isinstance(new_fml.sub, forms.Description_Local):
                    w._formulas['neg_local_desc'].update({new_fml})              
                        
            for new_fml in w._formulas['new_fml_posit']:                
                if isinstance(new_fml, forms.Atom):
                    w._formulas['atoms'].update({new_fml}) 
                elif isinstance(new_fml, forms.Conjunction):
                    w._formulas['conjunction'].update({new_fml}) 
                elif isinstance(new_fml, forms.Diamond):
                    w._formulas['diamond'].update({new_fml})              
                elif isinstance(new_fml, forms.Description_Global):
                    w._formulas['global_desc'].update({new_fml})              
                elif isinstance(new_fml, forms.Description_Local):
                    w._formulas['local_desc'].update({new_fml})              

            w._formulas['new_fml_negat'] = set()
            w._formulas['new_fml_posit'] = set()


    return (interpretation, False, False, [])            



#RULE DOUBLE NEGATION ----------------------------


def double_neg_rule(interpretation):
    """ Function implementing the propositional rule for double negation"""


    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['double_neg'])

        for fml in fml_set_copy:        

            if fml.sub.sub in set.union(*w._formulas.values()):
                w._formulas['double_neg'].remove(fml) 
                w._formulas['proc_negat'].update({fml}) 
                continue
            else:

                relocate_to_new_fml_sets(w._formulas, fml.sub.sub)
                w._formulas['double_neg'].remove(fml) 
                w._formulas['proc_negat'].update({fml}) 

            return(interpretation, False, True, [])
            
    return(interpretation, False, False, [])



#RULE CONJUNCTION ----------------------------

def conjunction_rule(interpretation):
    """ Function implementing the propositional rule for conjunction"""
    
    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['conjunction'])

        for fml in fml_set_copy:        

            v0 = fml.subs[0] in set.union(*w._formulas.values())
            v1 = fml.subs[1] in set.union(*w._formulas.values())

            if v0 and v1:
                w._formulas['conjunction'].remove(fml) 
                w._formulas['proc_posit'].update({fml}) 
                continue
            
            if not v0:
                relocate_to_new_fml_sets(w._formulas, fml.subs[0])
                
            if not v1:
                relocate_to_new_fml_sets(w._formulas, fml.subs[1])

            w._formulas['conjunction'].remove(fml) 
            w._formulas['proc_posit'].update({fml}) 
            
            return(interpretation, False, True, [])

    return(interpretation, False, False, [])



#RULE NEGATED CONJUNCTION ----------------------------


def negated_conjunction_rule(interpretation):
    """ Function implementing the propositional rule for conjunction"""

    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_conjunction'])

        for fml in fml_set_copy:        

            #if any of X and Y from ~(X & Y) are satisfied, pass to the next formula            
            if (forms.Negation(fml.sub.subs[0]) in set.union(*w._formulas.values())) or (forms.Negation(fml.sub.subs[1]) in set.union(*w._formulas.values())):
                continue
                
            else:
                #create a copy of the interpretation as an alternative branch and preparing for creating the interpration for the second branch
                alt_interpretation = deepcopy(interpretation)

                
                first_formula, second_formula = choose_fml_to_branch_on(interpretation,
                                                                        w,
                                                                        forms.Negation(fml.sub.subs[0]),
                                                                        forms.Negation(fml.sub.subs[1]))

                
                #updating current interpretation
                #relocate_to_new_fml_sets(w._formulas, forms.Negation(fml.sub.subs[0]))
                relocate_to_new_fml_sets(w._formulas, first_formula)
            
                w._formulas['neg_conjunction'].remove(fml) 
                w._formulas['proc_negat'].update({fml}) 
            
                #updating the "alternative interpretation"
                for w_alt in alt_interpretation.worlds():
                    if w_alt._world_name_str == w._world_name_str:
                        relocate_to_new_fml_sets(w_alt._formulas, second_formula)
                        w_alt._formulas['neg_conjunction'].remove(fml) 
                        w_alt._formulas['proc_negat'].update({fml}) 
                        
                return(interpretation, False, True, [alt_interpretation])

    return(interpretation, False, False, [])                   




#RULE NEGATED CONJUNCTION - VERSION FOR SAT-BASED OPTIMISATION ----------------------------


def negated_conjunction_rule_SAT(interpretation):
    """ Function implementing the propositional rule for conjunction in the version that performs SAT-based optimisations"""

    for w in interpretation.worlds():

        if len(w._Tbox_unfold_list_alt) == 0:
            continue

        #finding the smallest clauses and creating a set of such clauses
        min_clause_length = min({len(clause) for clause in w._Tbox_unfold_list_alt})
        clauses = [clause for clause in w._Tbox_unfold_list_alt if len(clause) == min_clause_length]

        #choosing the clauses with minimal complexity (calculated as minimum of complexities of constituent formulas/concepts)
        complexity_values = list()
        for i in range(len(clauses)):
            cl_compl = min([fml.complexity_score() for fml in clauses[i]])
            complexity_values.append(cl_compl) 
                    
        min_compl_clause = clauses[complexity_values.index(min(complexity_values))]

        #removing the clause from the set of clauses
        w._Tbox_unfold_list_alt.remove(min_compl_clause)

        if min_clause_length ==1:  #if there was one element in a clause - just add it to the branch
            form = min_compl_clause.pop()
            relocate_to_new_fml_sets(w._formulas, form)
            return(interpretation, False, True, [])
            
        elif min_clause_length >1:
            
            #find formula/concept with minimal complexity value
            alternative_forms = set()
            form_min_compl = min_compl_clause.pop()
            form_min_compl_score = form_min_compl.complexity_score()
            
            for form in min_compl_clause:
                if form.complexity_score() < form_min_compl_score:
                    alternative_forms.update({form_min_compl})
                    form_min_compl = form
                    form_min_compl_score = form_min_compl.complexity_score()
                else:
                    alternative_forms.update({form})
            
            
        #create a copy of the interpretation as an alternative branch and prepare for creating the interpration for the second branch
        alt_interpretation = deepcopy(interpretation)
        
        #updating current interpretation
        relocate_to_new_fml_sets(w._formulas, form_min_compl)
    
        #updating the "alternative interpretation" (according to semantic branching)
        for w_alt in alt_interpretation.worlds():
            if w_alt._world_name_str == w._world_name_str:
                relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(form_min_compl))
                w_alt._Tbox_unfold_list_alt.append(alternative_forms)            
                    
        return(interpretation, False, True, [alt_interpretation])

    return(interpretation, False, False, [])                   



# ROLE RULE 1  ----------------------------


def role_rule_1(interpretation):
    """ Function implementing the role rule for "Ǝr" """
    
    for w in interpretation.worlds():

        #updating the list of 'candidate worlds/individuals' and (within it) - blocked diamond formulas (concepts that are existential restrictions) 
        if bool(w._candidates_blocking) and bool(w._box_subformulas):
            
            cand_blocking_new = {}
            
            for cand_world, roles_dict in w._candidates_blocking.items():
                cand_blocking_new[cand_world] = {}
                for role, blocked_forms in roles_dict.items():
                    cand_blocking_new[cand_world][role] = blocked_forms
                    if role in w._box_subformulas.keys():
                        if w._box_subformulas[role] <= set.union(*cand_world._formulas.values()): #if for all formulas X such that box(X) are in world w, X is in the candidate world
                            pass
                        else:
                            for bfml in blocked_forms: #the blocked formula is removed from the 'processed' set - it will have to be analysed again
                                w._formulas['proc_posit'].remove(bfml) 
                                w._formulas['diamond'].update({bfml})
                            
                            del cand_blocking_new[cand_world][role] 
                
                if not bool(cand_blocking_new[cand_world]):
                    del cand_blocking_new[cand_world]
                          
            w._candidates_blocking = cand_blocking_new
            
        
        fml_set_copy = list(w._formulas['diamond'])

        for fml in fml_set_copy:        

           
            #Options 1 and 2 implement the blocking mechanism described in the paper

            #Option1 - looking for a related world/individual
            rel_worlds_list = interpretation.related_worlds(w, fml.role) #list of worlds related with w by role indicated in the "diamond" formula
            if len(rel_worlds_list)>0:   #if any world is related to w, with the relation role  
               if any({fml.sub2 in set.union(*rel_w._formulas.values()) for rel_w in rel_worlds_list}): #does any of the related worlds contain the formula indicated in the "diamond" formula?
                  
                   #mark the analysed formula fml as processed
                   w._formulas['diamond'].remove(fml) 
                   w._formulas['proc_posit'].update({fml}) 
                    
                   return(interpretation, False, True, []) #rule applied, exit
                  
           
            #Option 2 - looking for a "candidate world/individual"
            for unrel_v in interpretation.unrelated_worlds(w, fml.role):
                if (fml.sub2 in set.union(*unrel_v._formulas.values())) and (fml.role not in w._box_subformulas.keys() or w._box_subformulas[fml.role] <= set.union(*unrel_v._formulas.values())):
                    if unrel_v in w._candidates_blocking.keys():
                        w._candidates_blocking[unrel_v][fml.role].update({fml})
                    else:
                        w._candidates_blocking[unrel_v] = {fml.role: {fml}}

                    w._formulas['diamond'].remove(fml) 
                    w._formulas['proc_posit'].update({fml}) 

                    return(interpretation, False, True, [])



            #Option3 - creating new world/individual (this option directly applies the rule, if the "candidate" world has not been found)                               
            new_world = interpretation.add_world({'atoms': set(),
                                                  'neg_atoms': set(),
                                                  'double_neg': set(),
                                                  'conjunction': set(),
                                                  'neg_conjunction': set(),
                                                  'diamond': set(),
                                                  'neg_diamond': set(),
                                                  'global_desc': set(),
                                                  'neg_global_desc': set(),
                                                  'local_desc': set(),
                                                  'neg_local_desc': set(),
                                                  'proc_posit': set(),
                                                  'proc_negat': set(),
                                                  'proc_global_desc': set(),
                                                  'proc_local_desc': set(),
                                                  'new_fml_posit': set(),
                                                  'new_fml_negat': set()})
    
    
            new_world._world_name_str = add_functions.new_world_name(interpretation)

            #adding Tbox to the new world/individual 
            if interpretation._optimisations[2] == True:
                new_world._Tbox_unfold_list_alt.extend(interpretation._Tbox_unfold_global)
            else:
                new_world._formulas['neg_conjunction'] = set(interpretation._Tbox_unfold_global)

            #place the concept in the new world/individual
            relocate_to_new_fml_sets(new_world._formulas, fml.sub2)                

            interpretation.add_edge(w, new_world, fml.role)    
            
            #applying lazy unfolding for role absorption
            for pair in interpretation._Tbox_fold_subs_ex_restr:
                if pair[0] == fml.role:
                    relocate_to_new_fml_sets(w._formulas, pair[1])
            
            
            #moving concepts ~X, such that ~*E (role) X to the new world
            for box_fml in w._formulas['proc_negat']:
                if isinstance(box_fml.sub, forms.Diamond) and (box_fml.sub.role == fml.role):
                    relocate_to_new_fml_sets(new_world._formulas, forms.Negation(box_fml.sub.sub2))
           
            #mark the analysed formula fml as processed
 #           w._formulas['diamond'].remove(fml) 
  #          w._formulas['proc_posit'].update({fml}) 
            
            del new_world 
           
            return(interpretation, False, True, [])

    return(interpretation, False, False, [])                   




# ROLE RULE 2  ----------------------------


def role_rule_2(interpretation):
    """ Function implementing the role rule for "~Ǝr" """
    
    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_diamond'])

        for fml in fml_set_copy:        

            #updating the list of concepts X, such that ~*E role X is a concept
            if fml.sub.role in w._box_subformulas.keys():
                #w._box_subformulas[fml.sub.role].update({fml})
                if isinstance(fml.sub.sub2, forms.Negation):
                    w._box_subformulas[fml.sub.role].update({fml.sub.sub2.sub})
                else:
                    w._box_subformulas[fml.sub.role].update({fml.sub.sub2})                    
            else:
                #w._box_subformulas[fml.sub.role] = {fml}
                if isinstance(fml.sub.sub2, forms.Negation):
                    w._box_subformulas[fml.sub.role] = {fml.sub.sub2.sub}
                else:
                    w._box_subformulas[fml.sub.role] = {fml.sub.sub2}               
            
            #add the formula to all the related worlds                
            for v in interpretation.related_worlds(w, fml.sub.role):
                relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub.sub2))

            w._formulas['neg_diamond'].remove(fml) 
            w._formulas['proc_negat'].update({fml})  
                                 
            return(interpretation, False, True, [])
    
    return(interpretation, False, False, [])                   
                                    



# GLOBAL DESCRIPTION RULE 1  ----------------------------


def global_description_rule_1(interpretation):
    """ Function implementing the first rule for global descriptions: i(g,1) """

    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['global_desc'])

        for fml in fml_set_copy:        

            continue_to_next_formula = False #working variable for Option 1 below           

            #Global description i C.D found

            #Option 1 - are i.C and D satisfied in some world/individual?
            for v in interpretation.worlds():
                if {forms.Description_Local(fml.subs[0]), fml.subs[1]} <= set.union(*v._formulas.values()):
                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  
                    continue_to_next_formula = True
                    break

            if continue_to_next_formula:
                continue


            #Option 2 - is i.C satisfied in some world/individual (but not D)?
            for v in interpretation.worlds():
                if forms.Description_Local(fml.subs[0]) in set.union(*v._formulas.values()):
                    relocate_to_new_fml_sets(v._formulas, fml.subs[1])

                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  

                    return(interpretation, False, True, [])


            #Option 3 - are C and D satisfied in some world/individual?
            for v in interpretation.worlds():
                if {fml.subs[0], fml.subs[1]} <= set.union(*v._formulas.values()):
                    relocate_to_new_fml_sets(v._formulas, forms.Description_Local(fml.subs[0]))

                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  

                    return(interpretation, False, True, [])


            #Option 4 - is C satisfied in some world (but not D)?
            for v in interpretation.worlds():
                if fml.subs[0] in  set.union(*v._formulas.values()):
                    relocate_to_new_fml_sets(v._formulas, forms.Description_Local(fml.subs[0]))
                    relocate_to_new_fml_sets(v._formulas, fml.subs[1])
                    
                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  

                    return(interpretation, False, True, [])


            #Option 5 - else - add a new world/individual with both formulas from the description
            new_world = interpretation.add_world({'atoms': set(),
                                                  'neg_atoms': set(),
                                                  'double_neg': set(),
                                                  'conjunction': set(),
                                                  'neg_conjunction': set(),
                                                  'diamond': set(),
                                                  'neg_diamond': set(),
                                                  'global_desc': set(),
                                                  'neg_global_desc': set(),
                                                  'local_desc': set(),
                                                  'neg_local_desc': set(),
                                                  'proc_posit': set(),
                                                  'proc_negat': set(),
                                                  'proc_global_desc': set(),
                                                  'proc_local_desc': set(),
                                                  'new_fml_posit': set(),
                                                  'new_fml_negat': set()})
            
            new_world._world_name_str = add_functions.new_world_name(interpretation)

            #adding Tbox to the new world/individual 
            if interpretation._optimisations[2] == True:
                new_world._Tbox_unfold_list_alt.extend(interpretation._Tbox_unfold_global)
            else:
                new_world._formulas['neg_conjunction'] = set(interpretation._Tbox_unfold_global)


            relocate_to_new_fml_sets(new_world._formulas, forms.Description_Local(fml.subs[0]))
            relocate_to_new_fml_sets(new_world._formulas, fml.subs[1])

            w._formulas['global_desc'].remove(fml) 
            w._formulas['proc_global_desc'].update({fml})  
            
            del new_world            

            return(interpretation, False, True, [])

    return(interpretation, False, False, [])                   





# GLOBAL DESCRIPTION RULE 2  ----------------------------


def global_description_rule_2(interpretation):
    """ Function implementing the rule for negated global descriptions: ~i(g) """
    
    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_global_desc'])
        
        for fml in fml_set_copy:

            #blocking condition (for ~i.C.D, the rule has already been applied to some ~i.C, using the second "alternative option" of the rule)           
            if fml.sub.subs[0] in interpretation._LocDesc_rule3_block_cond_set:
                w._formulas['neg_global_desc'].remove(fml) 
                w._formulas['proc_negat'].update({fml})
                continue


            for v in interpretation.worlds():

                #if negation of any of the two formulas in the global description is satisfied in the world/individual:
                if forms.Negation(forms.Description_Local(fml.sub.subs[0])) in set.union(*v._formulas.values()) or forms.Negation(fml.sub.subs[1]) in set.union(*v._formulas.values()):
                    continue #pass to the next world v

                else:
                    alt_interpretation1 = deepcopy(interpretation)


                    first_formula, second_formula = choose_fml_to_branch_on(interpretation, w, forms.Negation(fml.sub.subs[0]), forms.Negation(fml.sub.subs[1]))

                    if first_formula == forms.Negation(fml.sub.subs[0]):
                        first_formula = forms.Negation(forms.Description_Local(fml.sub.subs[0]))
                        second_formula = forms.Negation(fml.sub.subs[1])
                    elif first_formula == forms.Negation(fml.sub.subs[1]):
                        second_formula = forms.Negation(forms.Description_Local(fml.sub.subs[0]))
                        first_formula = forms.Negation(fml.sub.subs[1])

                        
                    #1. updating current interpretation --
                    #relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub.subs[1]))
                    relocate_to_new_fml_sets(v._formulas, first_formula)
                    

                    #2. updating the "alternative interpretation 1" --
                    for w_alt in alt_interpretation1.worlds():
                        if w_alt._world_name_str == v._world_name_str:
                            #relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(forms.Description_Local(fml.sub.subs[0])))
                            relocate_to_new_fml_sets(w_alt._formulas, second_formula)
                            
                    return(interpretation, False, True, [alt_interpretation1])

    return(interpretation, False, False, [])



# LOCAL DESCRIPTION RULE 1  ----------------------------


def local_description_rule_1(interpretation):
    """ Function implementing the first rule for local descriptions: i(l,1) """

    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['local_desc'])

        for fml in fml_set_copy:        

            relocate_to_new_fml_sets(w._formulas, fml.sub)
            w._formulas['local_desc'].remove(fml) 
            w._formulas['proc_local_desc'].update({fml})  

            return(interpretation, False, True, [])
            
    return(interpretation, False, False, [])



# LOCAL DESCRIPTION RULE 2  ----------------------------


def local_description_rule_2(interpretation):
    """ Function implementing the second rule for local descriptions: i(l,1) """
    
    for w in interpretation.worlds():

        #here we need to iterate over all concepts/formulas, to make sure each formula in each world is checked, before "rule not applied" is returned
        for fml in (w._formulas['local_desc'] | w._formulas['proc_local_desc']):
        #in case of GDR2, we consider both processed and unprocessed concepts/formulas, and do not modify any of them in course of applying the rule

            worlds_to_be_unified_names = set()
            worlds_to_be_unified_world_copies = list()

            #create working copies of the worlds to be unified            
            for v in interpretation.worlds():
                if fml.sub in set.union(*v._formulas.values()):
                    worlds_to_be_unified_names.update({v._world_name_str})
                    worlds_to_be_unified_world_copies.append(v)

            if len(worlds_to_be_unified_names) < 2:
                continue #to the next formula - rule not applied
            elif all([set.union(*z._formulas.values())==set.union(*worlds_to_be_unified_world_copies[0]._formulas.values()) for z in worlds_to_be_unified_world_copies[1:]]):
                continue #to the next formula - rule not applied (all the worlds have the same sets of formulas)
            else:
                formulas_sum = set.union(*[set.union(*z._formulas.values()) for z in worlds_to_be_unified_world_copies])

                for v in interpretation.worlds():
                    if v._world_name_str in worlds_to_be_unified_names:
                        for form in formulas_sum - set.union(*v._formulas.values()):
                            relocate_to_new_fml_sets(v._formulas, form)


                #updating the global data structure that store information about which worlds/individuals should be "unified" 
                if len(interpretation._worlds_to_unify) == 0:
                    interpretation._worlds_to_unify.append(worlds_to_be_unified_names)
                
                else:
                    working_var = False
                    for world_set in interpretation._worlds_to_unify:
                        if not world_set.isdisjoint(worlds_to_be_unified_names):
                            world_set.update(worlds_to_be_unified_names)
                            working_var = True
                        
                    if working_var == False:
                        interpretation._worlds_to_unify.append(worlds_to_be_unified_names)
                
                del worlds_to_be_unified_names
                del worlds_to_be_unified_world_copies
                
                
                return(interpretation, False, True, [])
                
    return(interpretation, False, False, [])
                    



# LOCAL DESCRIPTION RULE 3  ----------------------------


def local_description_rule_3(interpretation):
    """ Function implementing the rule for negated local descriptions: ~i(l) """
    
    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_local_desc'])

        for fml in fml_set_copy:        
            
            #blocking condition (for ~i.C, the rule has already been applied to another ~i.C, using the second "alternative option" of the rule)           
            if fml.sub.sub in interpretation._LocDesc_rule3_block_cond_set:
                w._formulas['neg_local_desc'].remove(fml) 
                w._formulas['proc_negat'].update({fml})
                continue

            #if for ~i.C, ~C is already in the world/individual
            if forms.Negation(fml.sub.sub) in set.union(*w._formulas.values()):
                w._formulas['neg_local_desc'].remove(fml) 
                w._formulas['proc_negat'].update({fml})
                continue

            #creating the alternative interpretation for Option 2
            alt_interpretation = deepcopy(interpretation)

            #Option 1 - for i.C, add ~C
            #updating the current interpretation            
            relocate_to_new_fml_sets(w._formulas, forms.Negation(fml.sub.sub)) 
            w._formulas['neg_local_desc'].remove(fml) 
            w._formulas['proc_negat'].update({fml})


            #Option 2 
            #creating new fresh atom name
            fresh_atom_str = add_functions.new_fresh_atom(alt_interpretation)

            #parsing the new fresh atom as formula object    
            parser_tree = forms.parser_DL.parse(fresh_atom_str) 
            fresh_atom = forms.ToFml().transform(parser_tree)

            #updating the current world in the "alternative interpretation" with new concepts/formulas
            for w_alt in alt_interpretation.worlds():
                if w_alt._world_name_str == w._world_name_str:
                    relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fresh_atom))
                    relocate_to_new_fml_sets(w_alt._formulas, fml.sub.sub)
                    w_alt._formulas['neg_local_desc'].remove(fml) 
                    w_alt._formulas['proc_negat'].update({fml})


            #new world/individual
            new_world = alt_interpretation.add_world({'atoms': set(),
                                                       'neg_atoms': set(),
                                                       'double_neg': set(),
                                                       'conjunction': set(),
                                                       'neg_conjunction': set(),
                                                       'diamond': set(),
                                                       'neg_diamond': set(),
                                                       'global_desc': set(),
                                                       'neg_global_desc': set(),
                                                       'local_desc': set(),
                                                       'neg_local_desc': set(),
                                                       'proc_posit': set(),
                                                       'proc_negat': set(),
                                                       'proc_global_desc': set(),
                                                       'proc_local_desc': set(),
                                                       'new_fml_posit': set(),
                                                       'new_fml_negat': set()})
            
            new_world._world_name_str = add_functions.new_world_name(alt_interpretation)
            
            #adding Tbox to the new world/individual 
            if alt_interpretation._optimisations[2] == True:
                new_world._Tbox_unfold_list_alt.extend(alt_interpretation._Tbox_unfold_global)
            else:
                new_world._formulas['neg_conjunction'] = set(alt_interpretation._Tbox_unfold_global)
                
            #adding new concepts/formulas to the new world/individual
            relocate_to_new_fml_sets(new_world._formulas, fml.sub.sub)
            relocate_to_new_fml_sets(new_world._formulas, fresh_atom)
            
            
            del new_world    

            #updating the special set of formulas C, such that the tableua rule for the negation of a local description has been applied to a some formula i.C in this interpretation
            alt_interpretation._LocDesc_rule3_block_cond_set.update({fml.sub.sub})
                
            return(interpretation, False, True, [alt_interpretation]);

    return(interpretation, False, False, [])





# LOCAL DESCRIPTION CUT RULE  ----------------------------



def local_description_cut_rule(interpretation):
    """ Function implementing the cut rule for local descriptions"""
    
    for w in interpretation.worlds():
 
        for fml in (w._formulas['local_desc'] | w._formulas['proc_local_desc']):   
                
            for v in interpretation.worlds():
                if (fml.sub not in set.union(*v._formulas.values())) and (forms.Negation(fml.sub) not in set.union(*v._formulas.values())):
                    
                    alt_interpretation = deepcopy(interpretation)

                    first_formula, second_formula = choose_fml_to_branch_on(interpretation, w, fml.sub, forms.Negation(fml.sub))
                    
                    #updating current interpretation
                    #relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub))
                    #relocate_to_new_fml_sets(v._formulas, fml.sub)
                    relocate_to_new_fml_sets(v._formulas, first_formula)

                    #updating the "alternative interpretation"
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == v._world_name_str:

                            #relocate_to_new_fml_sets(w_alt._formulas, fml.sub) 
                            #relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fml.sub))
                            relocate_to_new_fml_sets(w_alt._formulas, second_formula)

                    return(interpretation, False, True, [alt_interpretation])


    return(interpretation, False, False, [])

