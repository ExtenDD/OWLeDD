import forms
from copy import deepcopy
import generators


def relocate_to_new_fml_sets(formulas_dict, new_fml):
    """ Place each new formula, that appeared in a given world as a result of applying a rule, in one of the subsets: 
    "new_fml_posit" of "new_fml_negat" - depending on whether it is a negation. This is done to limit applying the 
    clash rule to comparing those new formulas to all the others, already present in the world before applyting the 
    rule (this way we avoid repeating the same checks in the clash rule all over again)

    Arguments: 
        new_fml: a new formula, that appears in the world as an effect of applying a given rule    
        formulas_dict: an object of the form "w._formulas", where "w" is the world in which the new formula appears
            and "_formulas" is its attribute containing the dictionary of formulas
    
    """
    if isinstance(new_fml, forms.Negation):
        formulas_dict['new_fml_negat'].update({new_fml}) 
    else:
        formulas_dict['new_fml_posit'].update({new_fml}) 



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

        #print(no_new_fmls)
        
      #  print(w._formulas['new_fml_posit'])
       # print(w._formulas['new_fml_negat'])
        
        
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

#                        print("form", form)
 #                       print("p0", pair[0])                        
  #                      print("p1", pair[1])
                        
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
                    
                    for form in new_neg_atoms:  #w._formulas['new_fml_negat']:  ZMIANA
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
                new_neg_conjunctions = {nnc for nnc in w._formulas['new_fml_negat'] if isinstance(nnc.sub, forms.Conjunction)}
            
                w._formulas['new_fml_negat'] = w._formulas['new_fml_negat'] - new_neg_conjunctions

                w._Tbox_unfold_list_alt.extend([forms.unfold_neg_conj_into_set_of_alt(neg_con) for neg_con in new_neg_conjunctions])

                #optimisation 1: 
                #e.g. if A on the branch, and {A, X} is a clause on the branch, delete {A, X} from the branch 
                for form in (w._formulas['new_fml_posit'] | w._formulas['new_fml_negat']):
                    w._Tbox_unfold_list_alt = [alt for alt in w._Tbox_unfold_list_alt if form not in alt]

                #optimisation 2: 
                #e.g. if ~A on the branch, and {A, X} is a clause on the branch, delete A from {A, X} 
                
                if w._formulas['new_fml_posit'] | w._formulas['new_fml_negat']:
                #    print("!!!!!!!!!!", w._formulas['new_fml_posit'])
                 #   print("???????", w._formulas['new_fml_negat'])
                  #  print("#########", w._Tbox_unfold_list_alt)
                    
                    Tbox_unfold_new = list()
                    for alt in w._Tbox_unfold_list_alt:
                        
                        new_alt = alt
                        for pform in w._formulas['new_fml_posit']:
                            new_alt = {form for form in new_alt if pform != forms.negate_formula(form)}
                   #         print("$$$$$$$$$$", new_alt)
                            
                        for nform in w._formulas['new_fml_negat']:
                            new_alt = {form for form in new_alt if nform.sub != form}
    
                        if len(new_alt) ==0:  #if a clause is empty - the branch is inconsistent!
                    #        print("zzzzzzzzzzzzzz")
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

        # if len(w._formulas['double_neg']) == 0:
        #     continue
        # else:
        #     fml = w._formulas['double_neg'].pop()
        #     w._formulas['proc_negat'].update({fml})

                #print("fml for double neg", w._world_name_str, fml)
                relocate_to_new_fml_sets(w._formulas, fml.sub.sub)
                w._formulas['double_neg'].remove(fml) 
                w._formulas['proc_negat'].update({fml}) 
        
            #test
            # print(w._world_name_str)
            # print('double neg rule applied')
            # print("doubneg:", w._formulas['double_neg'])
            # print("pnf:", w._formulas['proc_negat'])

            return(interpretation, False, True, [])
            
    return(interpretation, False, False, [])



#RULE CONJUNCTION ----------------------------

def conjunction_rule(interpretation):
    """ Function implementing the propositional rule for conjunction"""
    
    for w in interpretation.worlds():

#        print(w._world_name_str, " ", set.union(*w._formulas.values()))        
        

        #print ("len1:", len(w._formulas['conjunction']))        


        fml_set_copy = list(w._formulas['conjunction'])

        for fml in fml_set_copy:        

        # if len(w._formulas['conjunction']) == 0:
        #     continue
        # else:
        #     fml = w._formulas['conjunction'].pop()
        #     w._formulas['proc_posit'].update({fml})

            #print ("len2:", len(w._formulas['conjunction']))        


            v0 = fml.subs[0] in set.union(*w._formulas.values())
            v1 = fml.subs[1] in set.union(*w._formulas.values())

            #print("first conjunct ", fml.subs[0], v0, v1)

            if v0 and v1:
                w._formulas['conjunction'].remove(fml) 
                w._formulas['proc_posit'].update({fml}) 
                continue
            
            #print("fml for conjunction", w._world_name_str, fml)
            
            if not v0:
                relocate_to_new_fml_sets(w._formulas, fml.subs[0])
                
            if not v1:
                relocate_to_new_fml_sets(w._formulas, fml.subs[1])


            w._formulas['conjunction'].remove(fml) 
            w._formulas['proc_posit'].update({fml}) 


            #test
#            print(w._world_name_str)
#            print('conjunction rule applied')
#            print("conjunct:", w._formulas['conjunction'])
            #print("ppf:", w._formulas['proc_posit']) 

            #print ("len3:", len(w._formulas['conjunction']))        

            
            return(interpretation, False, True, [])

    return(interpretation, False, False, [])



#RULE NEGATED CONJUNCTION ----------------------------


def negated_conjunction_rule(interpretation):
    """ Function implementing the propositional rule for conjunction"""

    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_conjunction'])

       # print("TTTTT", fml_set_copy)            

        for fml in fml_set_copy:        

            #if any of X and Y from ~(X & Y) are satisfied, pass to the next formula            
            if (forms.Negation(fml.sub.subs[0]) in set.union(*w._formulas.values())) or (forms.Negation(fml.sub.subs[1]) in set.union(*w._formulas.values())):
                continue
                
            else:
                #create a copy of the interpretation as an alternative branch and preparing for creating the interpration for the second branch
                alt_interpretation = deepcopy(interpretation)
                
                #updating current interpretation
                relocate_to_new_fml_sets(w._formulas, forms.Negation(fml.sub.subs[0]))
            
                w._formulas['neg_conjunction'].remove(fml) 
                w._formulas['proc_negat'].update({fml}) 
            
                #updating the "alternative interpretation"
                for w_alt in alt_interpretation.worlds():
                    if w_alt._world_name_str == w._world_name_str:
                        relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fml.sub.subs[1]))
                        w_alt._formulas['neg_conjunction'].remove(fml) 
                        w_alt._formulas['proc_negat'].update({fml}) 
                        
                return(interpretation, False, True, [alt_interpretation])

    return(interpretation, False, False, [])                   




#RULE NEGATED CONJUNCTION ----------------------------


def negated_conjunction_rule_SAT(interpretation):
    """ Function implementing the propositional rule for conjunction"""

    for w in interpretation.worlds():

        if len(w._Tbox_unfold_list_alt) == 0:
            continue


        #finding the smallest clauses and creating a set of such clauses
        min_clause_length = min({len(clause) for clause in w._Tbox_unfold_list_alt})
        clauses = [clause for clause in w._Tbox_unfold_list_alt if len(clause) == min_clause_length]


        #choosing the clauses with minimal complexity (calculated as minimum of complexities of constituent formulas)
        complexity_values = list()
        for i in range(len(clauses)):
            cl_compl = min([fml.complexity_score() for fml in clauses[i]])
           # print(cl_compl)
            complexity_values.append(cl_compl) 
                    
        min_compl_clause = clauses[complexity_values.index(min(complexity_values))]

        #removing the clause from the set of clauses
        w._Tbox_unfold_list_alt.remove(min_compl_clause)

        if min_clause_length ==1:  #if there was one element in a clause - just add it to the branch
            form = min_compl_clause.pop()
            relocate_to_new_fml_sets(w._formulas, form)
            return(interpretation, False, True, [])
            
        elif min_clause_length >1:
            
            #find formula with minimal complexity value
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
            
            
            #create a copy of the interpretation as an alternative branch and preparing for creating the interpration for the second branch
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

        cand_blocking_new = {}        

        #updating the list of 'candidate worlds' and (within it) - blocked diamond formulas 
        if bool(w._candidates_blocking) and bool(w._box_subformulas):
            for cand_world, roles_dict in w._candidates_blocking.items():
                cand_blocking_new[cand_world] = {}
                for role, blocked_forms  in roles_dict.items():
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

            #Option1 - looking for a related world
            rel_worlds_list = interpretation.related_worlds(w, fml.role) #list of worlds related with w by role indicated in the "diamond" formula
            if len(rel_worlds_list)>0:   #if any world is related to w, with the relation role  
               if any({fml.sub2 in set.union(*rel_w._formulas.values()) for rel_w in rel_worlds_list}): #does any of the related worlds contain the formula indicated in the "diamond" formula?
                  
                   #mark the analysed formula fml as processed
                   w._formulas['diamond'].remove(fml) 
                   w._formulas['proc_posit'].update({fml}) 

                   return(interpretation, False, True, []) #rule applied, exit
                  
           
            #Option 2 - looking for a "candidate world"
            for unrel_v in interpretation.unrelated_worlds(w, fml.role):
                if (fml.sub2 in set.union(*unrel_v._formulas.values())) and (fml.role not in w._box_subformulas.keys() or w._box_subformulas[fml.role] <= set.union(*unrel_v._formulas.values())):
                    if unrel_v in w._candidates_blocking.keys():
                        w._candidates_blocking[unrel_v][fml.role].update({fml})
                    else:
                        w._candidates_blocking[unrel_v] = {fml.role: {fml}}

                    w._formulas['diamond'].remove(fml) 
                    w._formulas['proc_posit'].update({fml}) 

                    return(interpretation, False, True, [])




            #Option3 - creating new world (this option directly applies the rule, if the "candidate" world has not been found)                               
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
    
    
            new_world._world_name_str = generators.new_world_name(interpretation)

            #adding Tbox to the new world/individual 
            if interpretation._optimisations[2] == True:
                new_world._Tbox_unfold_list_alt.extend(interpretation._Tbox_unfold_global)
            else:
                new_world._formulas['neg_conjunction'] = set(interpretation._Tbox_unfold_global)

            #place the concept in the new world
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
           
            del new_world 
           
            return(interpretation, False, True, [])

    return(interpretation, False, False, [])                   




# ROLE RULE 2  ----------------------------


def role_rule_2(interpretation):
    """ Function implementing the role rule for "~Ǝr" """
    
    
    # for w in interpretation.worlds():
 
    #     print("!!!???????")
    #     print(w._world_name_str, set.union(*w._formulas.values()))       

    
    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['neg_diamond'])

        for fml in fml_set_copy:        

           # print("rr2 fml found", w._world_name_str, fml)
        # if len(w._formulas['neg_diamond']) == 0:
        #     continue
        # else:
        #     fml = w._formulas['neg_diamond'].pop()
        #     w._formulas['proc_negat'].update({fml})

#            print("role rule 2 ", w, len(w._formulas['negat']))
        
     #               if fml in w._formulas['proc_negat']:  #if formula already processed, remove it from the "unprocessed" set
     #                   w._formulas['negat'].remove(fml)
     #                   print("repeating box formula removed")
     #                   continue #...and pass to the next formula                     
                    
                #updating the list of concepts X, such that ~*E role X is a concept
            if fml.sub.role in w._box_subformulas.keys():
                w._box_subformulas[fml.sub.role].update({fml})
            else:
                w._box_subformulas[fml.sub.role] = {fml}
            
            #print(w._box_subformulas)
            
            #add the formula to all the related worlds                
            for v in interpretation.related_worlds(w, fml.sub.role):
                relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub.sub2))
           #     print("rr2 will be applied to", v._world_name_str)
                # if isinstance(fml.sub.sub2, forms.Negation) and isinstance(fml.sub.sub2.sub, forms.Atom):
                #     v._formulas['proc_posit'].update({fml.sub.sub2.sub})
                # elif isinstance(fml.sub.sub2, forms.Negation):
                #     v._formulas['negat'].update({forms.Negation(fml.sub.sub2)})
                # elif isinstance(fml.sub.sub2, forms.Atom):
                #     v._formulas['proc_negat'].update({forms.Negation(fml.sub.sub2)})                    
                # else:
                #     v._formulas['negat'].update({forms.Negation(fml.sub.sub2)})


            w._formulas['neg_diamond'].remove(fml) 
            w._formulas['proc_negat'].update({fml})  
        #    print(w._world_name_str)
         #   print("neg_diamond:", w._formulas['neg_diamond'])
          #  print("pnf:", w._formulas['proc_negat'])            
                                 
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

            #Option 1 - are i.C and D satisfied in some world?
            for v in interpretation.worlds():
                if {forms.Description_Local(fml.subs[0]), fml.subs[1]} <= set.union(*v._formulas.values()):
                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  
                    #print("gd1 rule applied, option 1", w._world_name_str, fml)
                    continue_to_next_formula = True
                    break
                    #return(interpretation, False, True, [])

            if continue_to_next_formula:
                continue


            #Option 2 - is i.C satisfied in some world (but not D)?
            for v in interpretation.worlds():
                if forms.Description_Local(fml.subs[0]) in set.union(*v._formulas.values()):
                    relocate_to_new_fml_sets(v._formulas, fml.subs[1])

                    w._formulas['global_desc'].remove(fml) 
                    w._formulas['proc_global_desc'].update({fml})  

                    return(interpretation, False, True, [])


            #Option 3 - are C and D satisfied in some world?
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


            #Option 3 - else - add a new world with both formulas from the description
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
            
            new_world._world_name_str = generators.new_world_name(interpretation)

            #adding Tbox to the new world/individual 
            if interpretation._optimisations[2] == True:
                new_world._Tbox_unfold_list_alt.extend(interpretation._Tbox_unfold_global)
            else:
                new_world._formulas['neg_conjunction'] = set(interpretation._Tbox_unfold_global)


            relocate_to_new_fml_sets(new_world._formulas, forms.Description_Local(fml.subs[0]))
            relocate_to_new_fml_sets(new_world._formulas, fml.subs[1])

            w._formulas['global_desc'].remove(fml) 
            w._formulas['proc_global_desc'].update({fml})  
            
            #print("gd1 rule applied, option 3", w._world_name_str, fml)
 #           print("forms in the new world")
  #          print("new_pos_forms:", new_world._formulas['new_fml_posit'])
            #print("ppf:", new_world._formulas['proc_posit']) 
   #         print("new neg forms:", new_world._formulas['new_fml_negat'])
            
            del new_world            

            return(interpretation, False, True, [])

    return(interpretation, False, False, [])                   





# GLOBAL DESCRIPTION RULE 2  ----------------------------


def global_description_rule_3(interpretation):
    """ Function implementing the rule for negated global descriptions: ~i(g) """

    
    for w in interpretation.worlds():
        
        for fml in w._formulas['neg_global_desc']:

            for v in interpretation.worlds():

                #if negation of any of the two formulas in the global description is satisfied in the world:
                if forms.Negation(forms.Description_Local(fml.sub.subs[0])) in set.union(*v._formulas.values()) or forms.Negation(fml.sub.subs[1]) in set.union(*v._formulas.values()):
                    continue #pass to the next world v

                else:
                    alt_interpretation1 = deepcopy(interpretation)
                    
                    #1. updating current interpretation --
                    relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub.subs[1]))


                    #2. updating the "alternative interpretation 1" --
                    for w_alt in alt_interpretation1.worlds():
                        if w_alt._world_name_str == v._world_name_str:
                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(forms.Description_Local(fml.sub.subs[0])))
           
                    return(interpretation, False, True, [alt_interpretation1])

    return(interpretation, False, False, [])





# GLOBAL DESCRIPTION CUT RULE  ----------------------------



def global_description_cut_rule(interpretation):
    """ Function implementing the cut rule for global descriptions: cut(g,i) """
    
    for w in interpretation.worlds():
 
        # print("!!!???????")
        # print(w._world_name_str, set.union(*w._formulas.values()))       
 
        for fml in (w._formulas['global_desc'] | w._formulas['proc_global_desc']):   
            #print("GD cut rule: gd found: ", w._world_name_str, fml)
                
            for v in interpretation.worlds():
                #print("!!!???????")
                #print(v._world_name_str, set.union(*v._formulas.values()))
                #print(fml.subs[0])
                #print(set.union(*v._formulas.values()))
                #print((fml.subs[0] not in set.union(*v._formulas.values())))
                if (fml.subs[0] not in set.union(*v._formulas.values())) and (forms.Negation(fml.subs[0]) not in set.union(*v._formulas.values())):
                    
                   # print("cut_rule world without p and ~p for @pq found: ", v._world_name_str)
                    # print("pf:", v._formulas['posit'])
                    # print("ppf:", v._formulas['proc_posit']) 
                    # print("nf:", v._formulas['negat'])
                    # print("pnf:", v._formulas['proc_negat'])            
                    
                    alt_interpretation = deepcopy(interpretation)
                    
                    #updating current interpretation
                    relocate_to_new_fml_sets(v._formulas, fml.subs[0])

                    # if isinstance(fml.subs[0], forms.Negation) and isinstance(fml.subs[0].sub, forms.Atom):
                    #     v._formulas['proc_negat'].update({fml.subs[0]})
                    # elif isinstance(fml.subs[0], forms.Negation):
                    #     v._formulas['negat'].update({fml.subs[0]})
                    # elif isinstance(fml.subs[0], forms.Atom):
                    #     v._formulas['proc_posit'].update({fml.subs[0]})                    
                    # else:
                    #     v._formulas['posit'].update({fml.subs[0]})  
                
                 #   print("!!!!!!")
                  #  print(v._world_name_str, v._formulas)
                
                    #updating the "alternative interpretation"
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == v._world_name_str:
#                            print("analysing updated world in GDcut alternative model")

                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fml.subs[0]))

                            # if isinstance(fml.subs[0], forms.Atom):
                            #     w_alt._formulas['proc_negat'].update({forms.Negation(fml.subs[0])})
                            # else:
                            #     w_alt._formulas['negat'].update({forms.Negation(fml.subs[0])})

 #                           print("alt int 1, world:", w_alt._world_name_str, "adding ", forms.Negation(fml.subs[0]))
                            # print("pf:", w_alt._formulas['posit'])
                            # print("ppf:", w_alt._formulas['proc_posit']) 
                            # print("nf:", w_alt._formulas['negat'])
                            # print("pnf:", w_alt._formulas['proc_negat'])    

                    return(interpretation, False, True, [alt_interpretation])


    return(interpretation, False, False, [])





# LOCAL DESCRIPTION RULE 1  ----------------------------


def local_description_rule_1(interpretation):
    """ Function implementing the first rule for local descriptions: i(l,1) """

    for w in interpretation.worlds():

        fml_set_copy = list(w._formulas['local_desc'])

        for fml in fml_set_copy:        

  #          print("LD1", fml, w._world_name_str, w._formulas['local_desc'], w._formulas['proc_local_desc'])
            
            #print("fml for local desc", w._world_name_str, fml)
            relocate_to_new_fml_sets(w._formulas, fml.sub)
            w._formulas['local_desc'].remove(fml) 
            w._formulas['proc_local_desc'].update({fml})  

            return(interpretation, False, True, [])
            
    return(interpretation, False, False, [])



# LOCAL DESCRIPTION RULE 2  ----------------------------


def local_description_rule_2(interpretation):
    """ Function implementing the second rule for local descriptions: i(l,1) """
    
    for w in interpretation.worlds():

#        if len(w._formulas['global_desc'] | w._formulas['proc_global_desc']) == 0:
#            continue
#        else:
            
            #here we need to iterate over all formulas, to make sure each formula in each world is checked, before "rule not applied" is returned
        for fml in (w._formulas['local_desc'] | w._formulas['proc_local_desc']):
        #in case of GDR2, we consider both processed and unprocessed formulas, and do not modify any of them in course of applying the rule

 #           print("LD2", fml, w._world_name_str)
                
            worlds_to_be_unified_names = set()
            worlds_to_be_unified_world_copies = list()

            #create working copies of the worlds to be unified            
            for v in interpretation.worlds():
                if fml.sub in set.union(*v._formulas.values()):
                    worlds_to_be_unified_names.update({v._world_name_str})
                    worlds_to_be_unified_world_copies.append(v)

            
           # print("no of worlds to be unified", len(worlds_to_be_unified_names))
           # print("worlds to be unified", worlds_to_be_unified_names)
            
            if len(worlds_to_be_unified_names) < 2:
                continue #to the next formula - rule not applied
            elif all([set.union(*z._formulas.values())==set.union(*worlds_to_be_unified_world_copies[0]._formulas.values()) for z in worlds_to_be_unified_world_copies[1:]]):
               # print("all worlds to be unified are equal - continue to next formula")
                continue #to the next formula - rule not applied (all the worlds have the same sets of formulas)
            else:
                formulas_sum = set.union(*[set.union(*z._formulas.values()) for z in worlds_to_be_unified_world_copies])
                #print("sum of all formulas: ", formulas_sum)

                for v in interpretation.worlds():
                    if v._world_name_str in worlds_to_be_unified_names:
                        for form in formulas_sum - set.union(*v._formulas.values()):
                            relocate_to_new_fml_sets(v._formulas, form)



                #updating the global data structure that store information about which worlds/individuals should be "united" 
                if len(interpretation._worlds_to_unify) == 0:
                    interpretation._worlds_to_unify.append(worlds_to_be_unified_names)
                
                else:
                    working_var = False
                    for world_set in interpretation._worlds_to_unify:
                        if not world_set.isdisjoint(worlds_to_be_unified_names):
                            world_set.update(worlds_to_be_unified_names)
                            working_var = True
                        
                    if working_var == False:
                        interpretation._worlds_to_unify.update(worlds_to_be_unified_names)
                
                
#                print("XXXXX", interpretation._worlds_to_unify)
                    
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

            #if for i.C, ~C is already on the branch
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



            #create working variables before exploring different options            
            if fml.sub.sub in alt_interpretation._LocDesc_rule3_list[0]:
                fr_atom_set = alt_interpretation._LocDesc_rule3_list[1][alt_interpretation._LocDesc_rule3_list[0].index(fml.sub.sub)]
                fr_atom = next(iter(fr_atom_set))
                fr_atom_set_len = len(fr_atom_set)
            else:
                fr_atom_set = {1,2,3}
                fr_atom_set_len = 3


            #Option 1: there are already 2 special "fresh" atoms connected with C (for ~i.C)            
            if fr_atom_set_len == 2:
                
                fr_atom_set_copy = list(fr_atom_set)
                
                #one of the special atoms is on the branch
                if fr_atom_set_copy[0] in set.union(*w._formulas.values()):
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == w._world_name_str:
                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fr_atom_set_copy[0]))
                            w_alt._formulas['neg_local_desc'].remove(fml) 
                            w_alt._formulas['proc_negat'].update({fml})
                        return(interpretation, False, True, [alt_interpretation])
                
                elif fr_atom_set_copy[1] in set.union(*w._formulas.values()):
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == w._world_name_str:
                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fr_atom_set_copy[1]))
                            w_alt._formulas['neg_local_desc'].remove(fml) 
                            w_alt._formulas['proc_negat'].update({fml})
                        return(interpretation, False, True, [alt_interpretation])

                else:
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == w._world_name_str:
                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fr_atom_set_copy[0]))
                            relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fr_atom_set_copy[1]))
                            w_alt._formulas['neg_local_desc'].remove(fml) 
                            w_alt._formulas['proc_negat'].update({fml})
                        return(interpretation, False, True, [alt_interpretation])
                    
            #Option 2: there is already 1 special "fresh" atom connected with C (for ~i.C) but it is not on the branch
            elif fr_atom_set_len ==1 and fr_atom not in set.union(*w._formulas.values()):
                for w_alt in alt_interpretation.worlds():
                    if w_alt._world_name_str == w._world_name_str:
                        relocate_to_new_fml_sets(w._formulas, forms.Negation(fr_atom))
                        w_alt._formulas['neg_local_desc'].remove(fml) 
                        w_alt._formulas['proc_negat'].update({fml})
                    return(interpretation, False, True, [alt_interpretation])
                

            #Option 3. The rule is applied "normally" (no blocking is applied)
            elif fr_atom_set_len ==3 or (fr_atom_set_len ==1 and fr_atom in set.union(*w._formulas.values())):
                fresh_atom_str = generators.new_fresh_atom(alt_interpretation)
        
                parser_tree = forms.parser_DL.parse(fresh_atom_str)
                fresh_atom = forms.ToFml().transform(parser_tree)

                for w_alt in alt_interpretation.worlds():
                    if w_alt._world_name_str == w._world_name_str:
                        relocate_to_new_fml_sets(w_alt._formulas, forms.Negation(fresh_atom))
                        w_alt._formulas['neg_local_desc'].remove(fml) 
                        w_alt._formulas['proc_negat'].update({fml})


                #new world
                new_world = alt_interpretation.add_world({'atoms': set(),
                                                           'neg_atoms': set(),
                                                           'double_neg': set(),
                                                           'conjunction': set(),
                                                           'neg_conjunction': interpretation.TBox_formulas,
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
                
                new_world._world_name_str = generators.new_world_name(alt_interpretation)
                
                #adding Tbox to the new world/individual 
                if alt_interpretation._optimisations[2] == True:
                    new_world._Tbox_unfold_list_alt.extend(alt_interpretation._Tbox_unfold_global)
                else:
                    new_world._formulas['neg_conjunction'] = set(alt_interpretation._Tbox_unfold_global)
                    

                relocate_to_new_fml_sets(new_world._formulas, fml.sub.sub)
                relocate_to_new_fml_sets(new_world._formulas, fresh_atom)
                
                
                del new_world    

                #updating the special list related to fresh atoms and associated concepts
                if fr_atom_set_len ==3:
                    alt_interpretation._LocDesc_rule3_list[0].append(fml.sub.sub)
                    alt_interpretation._LocDesc_rule3_list[1].append({fresh_atom})
                elif fr_atom_set_len ==1:
                    alt_interpretation._LocDesc_rule3_list[1][alt_interpretation._LocDesc_rule3_list[0].index(fml.sub.sub)].update({fresh_atom})
                    
                return(interpretation, False, True, [alt_interpretation]);

    return(interpretation, False, False, [])






# LOCAL DESCRIPTION CUT RULE  ----------------------------



def local_description_cut_rule(interpretation):

    for w in interpretation.worlds():
 
        for fml in (w._formulas['local_desc'] | w._formulas['proc_local_desc']):   
           # print("LD cut rule: gd found: ", w._world_name_str, fml)
                
            for v in interpretation.worlds():
                #print("!!!???????")
                #print(v._world_name_str, set.union(*v._formulas.values()))
                #print(fml.subs[0])
                #print(set.union(*v._formulas.values()))
                #print((fml.subs[0] not in set.union(*v._formulas.values())))
                if (fml.sub not in set.union(*v._formulas.values())) and (forms.Negation(fml.sub) not in set.union(*v._formulas.values())):
                    
                  #  print("cut_rule world without p and ~p for @pq found: ", v._world_name_str)
                    # print("pf:", v._formulas['posit'])
                    # print("ppf:", v._formulas['proc_posit']) 
                    # print("nf:", v._formulas['negat'])
                    # print("pnf:", v._formulas['proc_negat'])            
                    
                    alt_interpretation = deepcopy(interpretation)
                    
                    #updating current interpretation
#                    relocate_to_new_fml_sets(v._formulas, fml.sub)
                    relocate_to_new_fml_sets(v._formulas, forms.Negation(fml.sub)) #NEW2026!!!!!!!!!!!!!!


                    # if isinstance(fml.subs[0], forms.Negation) and isinstance(fml.subs[0].sub, forms.Atom):
                    #     v._formulas['proc_negat'].update({fml.subs[0]})
                    # elif isinstance(fml.subs[0], forms.Negation):
                    #     v._formulas['negat'].update({fml.subs[0]})
                    # elif isinstance(fml.subs[0], forms.Atom):
                    #     v._formulas['proc_posit'].update({fml.subs[0]})                    
                    # else:
                    #     v._formulas['posit'].update({fml.subs[0]})  
                
                 #   print("!!!!!!")
                  #  print(v._world_name_str, v._formulas)
                
                    #updating the "alternative interpretation"
                    for w_alt in alt_interpretation.worlds():
                        if w_alt._world_name_str == v._world_name_str:
                          #  print("analysing updated world in GDcut alternative model")

                            relocate_to_new_fml_sets(w_alt._formulas, fml.sub) #NEW2026!!!!!!!!!!!!!!

                            # if isinstance(fml.subs[0], forms.Atom):
                            #     w_alt._formulas['proc_negat'].update({forms.Negation(fml.subs[0])})
                            # else:
                            #     w_alt._formulas['negat'].update({forms.Negation(fml.subs[0])})

                           # print("alt int 1, world:", w_alt._world_name_str, "adding ", forms.Negation(fml.sub))
                            # print("pf:", w_alt._formulas['posit'])
                            # print("ppf:", w_alt._formulas['proc_posit']) 
                            # print("nf:", w_alt._formulas['negat'])
                            # print("pnf:", w_alt._formulas['proc_negat'])    

                    return(interpretation, False, True, [alt_interpretation])


    return(interpretation, False, False, [])

