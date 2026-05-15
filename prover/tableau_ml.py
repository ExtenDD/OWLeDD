import forms
import interpretation
import rules


from copy import deepcopy
import time


class ML_Tableau:
    """Class for tableau"""
    
    #initialize the intepretation with input containing formulas, ABox, RBox and TBox    
    def __init__(self,
                 formula,
                 #use_SAT_optimisations = False,    #disabled here for now
                 time_out_limit = None):
        
        self.interpretation = interpretation.Interpretation()  #we initialize the interpretation object
        world_names_str = set()   #set of strings containing world names - a working variable
        self.time_out = False     #attribute that stores the information, if creating the tableau using a function "build_tableu" took more time than the defined limit
        self.parsing_time = 0

        #saving the optimisation choices as attrivutes of the interpretation (the first two are only used for description logics)
        self.interpretation._optimisations = (False, False, False)

        start_time_parsing = time.time()


        #1. READ IN AND PARSE THE MAIN ARGUMENTS

        
        
        #1 formula argument --
        if formula == None:
            pass
        else:
            #parse the formula(s)            
            if isinstance(formula, str):
                parser_tree = forms.parser_ML.parse(formula)
                fml_parsed = forms.ToFml().transform(parser_tree)
                fmls_parsed = [fml_parsed]
            elif isinstance(formula, list):
                fmls_parsed = []
                for fml in formula:
                    parser_tree = forms.parser_ML.parse(fml)
                    fml_parsed = forms.ToFml().transform(parser_tree)
                    fmls_parsed.append(fml_parsed)
            else:
                raise TypeError("Please insert a correctly built formula or list of formulas in the argument 'formula'")


            #formulas introduced in the "formula" argument are placed in a new individual
            #name the world "w0"; if this name already appearad in ABox or RBox, choose the first availabe from: {"w00", "w000",...}
            if not 'w0' in world_names_str:
                base_world_name = 'w0'
            else:
                for i in range(2, len(world_names_str) + 2):
                    if 'w'+i*'0' in world_names_str:
                        continue
                    
                    base_world_name = 'w'+i*'0'
                    break

    
            #add the formulas from the argument "formula" to the interpetation
            x = self.interpretation.add_world(fmls_parsed)
            x._world_name_str = base_world_name
            world_names_str.update({base_world_name}) 
        
        

        end_time_parsing = time.time()
        self.parsing_time = end_time_parsing - start_time_parsing 

            
        #2.7. setting additional attributes of the interpretation object
            
        #store the world names in an attribute of the interpretation
        self.interpretation._world_names_str = world_names_str

        #creating a set of all atom symbols occurring in the interpretation        
        self.interpretation._all_atoms_in_interpretation = set()

        #keeping the initial interpretation (before applying any rules)
        self.initial_interpretation = deepcopy(self.interpretation)  
        
        
        
        #3. SOLVE - NOW THE TABLEAU WILL BE CONSTRUCTED ----------------------------------

        #initializing a list of all "alternative" interpretations to be explored on branches of the tableau         
        alternative_interpretations = []
                
        #the rule for negated conjunction has 2 forms, depending on whether the "use_SAT_optimisations" is set to True or False
        #if use_SAT_optimisations == True:
        #    neg_conj_rule = rules.negated_conjunction_rule_SAT
        #else:
        #    neg_conj_rule = rules.negated_conjunction_rule
        
        rules_to_apply = [rules.clash_rule,
                          rules.double_neg_rule,
                          rules.conjunction_rule,
                          rules.role_rule_2,
                          rules.negated_conjunction_rule,    
                          rules.local_description_rule_1,
                          rules.local_description_rule_2,
                          rules.local_description_rule_3,
                          rules.local_description_cut_rule,
                          rules.global_description_rule_1,
                          rules.global_description_rule_2,
                          rules.role_rule_1]
        
        rules_to_apply = tuple(rules_to_apply)

        no_rules_to_apply = len(rules_to_apply)
        
        #initializing the counter of applied rules
        self.no_rules_applied = 0 
        
        #initializing the variable storing the satifiability status
        self.is_satisfiable = None

        #initializing the counter of closed branches of the tableau (in which an inconsistency has been found)        
        self.closed_branches_count = 0

        #initializing the runtime counter of the prover
        self.runtime = 0
        
        #division of formulas in the formula list in each world of the interpretation into sets of subtypes of formulas
        #note - the attribute "_formulas" of each world will be a dictionary, composed of sets of formulas as values from now on (not a list, as it was the case in the input)
        for w in self.interpretation.worlds():
            
            new_fml_posit = set()
            new_fml_negat = set()
            
            for fml in w._formulas:
                if isinstance(fml, forms.Negation):
                    new_fml_negat.update({fml})
                else:
                    new_fml_posit.update({fml})                        

            w._formulas = {'atoms': set(),
                           'neg_atoms': set(),
                           'double_neg': set(),
                           'conjunction': set(),
                           'neg_conjunction': set(),  #TU LISTA PAR??
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
                           'new_fml_posit': new_fml_posit,
                           'new_fml_negat': new_fml_negat}


            del new_fml_negat, new_fml_posit


        start_time_tableau = time.time()


        #initialize the iterator of rules
        rules_iterator = 0

        while rules_iterator < no_rules_to_apply:

            runtime_sofar = time.time() - start_time_tableau
            if time_out_limit != None and runtime_sofar > time_out_limit:
                self.time_out = True
                self.runtime = runtime_sofar 
                break
            


            #reset the iterator after any rule has been applied
            rules_iterator = 0
            

            for rule in rules_to_apply:  #iterate over the rules 
                
                #results of applying the rule: interpretation, True/False, True/False, list of alternative interpretations (possibly empty)
                new_interpretation, inconsistency_found, rule_applied, new_alt_interpretations = rule(self.interpretation)  
                
                if inconsistency_found:
                    self.closed_branches_count += 1
                    self.no_rules_applied += 1
                    
                    if len(alternative_interpretations) == 0: #no more "alternative interpretations" - stop building the tableau - it is not satisfiable
                        self.is_satisfiable = False
                        break
                    else:
                        self.interpretation = alternative_interpretations.pop() #pick the first available interpretation from a list, if a branch has been closed
                        break

                elif rule_applied: #rule has been applied
                    self.interpretation = new_interpretation
                    self.no_rules_applied += 1
                    alternative_interpretations.extend(new_alt_interpretations)  #add new "alternative interpretations" to the list - if there are any to add
                    #print(rule)
                    #breakpoint()
                    break  
                else:
                    rules_iterator += 1    #rule has not been applied
                        
            if self.is_satisfiable == False:
                break  #out of the whole while loop


        #if there are no more rules to apply and the formula is not a time out - it is satisfiable 
        if self.is_satisfiable is None and self.time_out is False and rules_iterator == no_rules_to_apply:
            self.is_satisfiable = True
        elif self.time_out is True:
            self.is_satisfiable = None
            
        
        end_time_tableau = time.time()
        self.runtime = end_time_tableau - start_time_tableau 

#Other functions to apply on the DL_Tableau object (after applying the rules) ------------------------


    def print_interpretation(self):
        """print interpretation in a text form - this version prints only atoms satisfied in the worlds/individuals"""
        #note - the interpretation should not be considered as a proper model 
        
        #print world/individuals names and atoms satisfied in them
        for w in self.interpretation.worlds():
            
            print(f"World name: {w._world_name_str} \n formulas:")
            
            for fml in (w._formulas['atoms']):
                print("  ", fml)  #print the formulas in "nice" looking form
                    
            for fml in (w._formulas['neg_atoms']):
                print("  ", fml)  #print the formulas in "nice" looking form
                
            print("\n")

       
        #print relations between worlds
        for v1, w  in self.interpretation._outgoing.items():
            if bool(w): #don't take into account worlds with no outging edges (bool(w) = dictionary w is not empty)
                for v2, roles in w.items():
                    for role in roles:
                        print(f"Relation type: {role} \n Source World: {v1._world_name_str} \n Target World: {v2._world_name_str} \n")

        #print roles that were "frozen" due to the blocking rule for existential restriction
        for w in self.interpretation.worlds():
            #print(w._candidates_blocking)
            if bool(w._candidates_blocking):
                for cand_world, roles_dict in w._candidates_blocking.items():
                    for role in roles_dict.keys():
                        print(f"Relation type: {role} \n Source World: {w._world_name_str} \n Target World: {cand_world._world_name_str} \n")
                

        #print which individuals/world should be unified (as a consequence of using local_description_rule_2)      
        if len(self.interpretation._worlds_to_unify) >0:
            print("Sets of worlds to unify:")
            for world_set in self.interpretation._worlds_to_unify:
                print(world_set, "\n")



    def nodes_count(self):
        """ print the number of nodes in the tableau"""
        return(self.no_rules_applied + 1)

    def branches_count(self):
        """ print the number of branches in the tableau"""
        if self.is_satisfiable == True or self.time_out == True:
            return (self.closed_branches_count + 1)
        elif self.is_satisfiable == False: 
            return (self.closed_branches_count)

    def satisfiability_check(self):
        if self.is_satisfiable == True:
            return ("Input satisfiable")
        elif self.time_out == True:
            return ("Time out: satisfiability not determined")
        elif self.is_satisfiable == False: 
            return ("Input unsatisfiable")

    def execution_time(self):
        print(f"Tableau runtime: {self.runtime} \n Parsing time: {self.parsing_time} \n")
    




    


