import os

os.chdir('C:\\projekt_UŁ\\python\\FLOC_2026')

import forms
#import rules
import interpretation
import add_functions
import TBox_optimisations
import rules

import re
import time
import pandas as pd
from copy import deepcopy
from itertools import combinations



class DL_Tableau:
    """Class for tableau"""
    
    #initialize the intepretation with input containing concepts, ABox, RBox and TBox    
    def __init__(self,
                 ontology_file_funct_syntax = None,
                 concept = None,
                 ABox = None, 
                 RBox = None,
                 TBox = None,
                 flexible_syntax = True,
                 use_absorption = True,
                 use_foldable_TBox  = True,
                 use_SAT_optimisations = False,
                 use_add_disj_optimisations = False,
                 runtime_limit_s = None):
                 #NEW15 dodajemy ontology = None 
                 #NEW15 ew time_out jako ustawialny tutaj
                 #NEW15 ew dodac argument modal_formula? wtedy automatycznie uruchamiamy inny parser i mamy modal prover
                     #jesli tak będzie, trzeba podać odpowiednie warunki - jesli jest podane modal_formula, to inne nie moga i na odwrót
        
        self.interpretation = interpretation.Interpretation()  #we initialize the interpretation object
        world_names_str = set()   #set of strings containing world names - a working variable
        self.time_out = False     #attribute that stores the information, if creating the tableau using a function "build_tableu" took more time than the defined limit


        if use_absorption == True and use_foldable_TBox == False:
            raise TypeError("Absorption cannot be enabled while division into foldable and unfoldable KBs is disabled")
            
        if use_add_disj_optimisations == True and use_SAT_optimisations == False:
            raise TypeError("Additional optimisations for disjunctions cannot be enabled while SAT-based optimisations are disabled ")


        #saving the optimisation choices as attrivutes of the interpretation
        self.interpretation._optimisations = (use_absorption, use_foldable_TBox, use_SAT_optimisations, use_add_disj_optimisations)

        #this object will represent a dependency graph, used to check if TBox is acyclic
        self.graph_Tbox_atoms = dict()




        #1. Ontology 
        
        #NEW15 najpierw deklaracje i wstępna struktura
            #w międzyczasie SED w poczekalni w odpowiedniej reprezentacji
            #potem odpowiednio traktujemy SED
            #ew tworzymy listy związane z dodatkowymi regułami dla implikacji

        if ontology_file_funct_syntax == None:
            pass
        #jakas obsulga bledu? dopuszczalne typy plików
#        elif not isinstance(ABox, dict):
#            raise TypeError("ABox argument was not properly introduced. Please use Python dictionary syntax, with keys corresponding to individuals and values corresponding to a concept or list of concepts")
        else:    
        #    ontology_file_funct_syntax = "ore_ont_580.owl"
    
            self.ont_concepts_df = pd.DataFrame({"source_iri": pd.Series(dtype="string"),
                                             "concept_name": pd.Series(dtype="string"),
                                             "if_declared": pd.Series(dtype="bool")})

            self.ont_roles_df = pd.DataFrame({"source_iri": pd.Series(dtype="string"),
                                          "role_name": pd.Series(dtype="string"),
                                          "if_declared": pd.Series(dtype="bool")})

            self.ont_individuals_df = pd.DataFrame({"source_iri": pd.Series(dtype="string"),
                                                    "if_declared": pd.Series(dtype="bool")})

           # self.ont_Tbox_atoms = pd.DataFrame({"source_iri": pd.Series(dtype="string"),  #do wywalenia???????
            #                                    "atom_name": pd.Series(dtype="string")})



            #TYCH CHYBA NIE TRZEBA TUTAJ WPROWADZAĆ! 
            #initializing data structures that will contain elements of TBox, used throughout the tableaux
            #they will be used as attributes of the interpretation object
            
#            self.interpretation._Tbox_fold_subs = set()

 #           self.interpretation._Tbox_unfold_subs = set()
#
 #           self.interpretation._Tbox_fold_eq = set()

            #this will contain subsumption axioms with conjunction of atoms on the left side. 
            #it contains pairs, in which the first element is a set of concepts (forming the conjunction), and the second a concept
            #for formal reasons this needs to be a list rather than a set
  #          self.interpretation._Tbox_fold_subs_conj = list()

   #         self.interpretation._Tbox_fold_subs_neg = set()
            
            #this is a set of pairs (role, concept) representing the outcome of role absorption. If this role appears between individuals X and Y, the concept should be satisfied in X
    #        self.interpretation._Tbox_fold_subs_ex_restr = set()

#            self.Tbox_unfold_eq = set()   #jednak niepotrzebne (raczej)

#            self.Tbox_fold_atoms_all = set()  #jednak niepotrzebne



            def read_lines():
                with open(ontology_file_funct_syntax) as ont_file:
                    for line in ont_file:
                        yield(line)

            i = 1
            for line in read_lines():

                statement = add_functions.read_until_string(line, "(")    

                if statement == "Declaration":
                    substatement = add_functions.read_until_string(line[len(statement)+1:], "(") 
                    declared_object = add_functions.read_until_string(line[line.find("(",line.find("(")+1)+1:], ")", " ")
                    
                    if substatement == "Class":
                        #tu ew dodac warunek - w zal od tego czy pozwalamy na dowolny tekst w klas-def
                        
                        proxy_concept_name = "C"+str(len(self.ont_concepts_df) + 1) if flexible_syntax == True else None
    
                        self.ont_concepts_df.loc[len(self.ont_concepts_df)] = [declared_object,
                                                                               proxy_concept_name,
                                                                               True]
                    elif substatement == "ObjectProperty":
                        
                        proxy_role_name = "r"+str(len(self.ont_roles_df) + 1) if flexible_syntax == True else None

                        self.ont_roles_df.loc[len(self.ont_roles_df)] = [declared_object,
                                                                         proxy_role_name,
                                                                         True]
                        
                    elif substatement == "NamedIndividual":
                        
                        self.ont_individuals_df.loc[len(self.ont_individuals_df)] = [declared_object,
                                                                                     True]
                        
                        locals()[declared_object] = x = self.interpretation.add_world([])
                        x._world_name_str = declared_object
                        world_names_str.update({declared_object})
                        
                    else:
                       # print("line number", i)
                        raise TypeError("Declaration in the ontology is not properly defined or contains DataProperties (not supported)")                        
                    
                         
                elif statement == "ClassAssertion":
                    #substatement = add_functions.read_until_string(line[len(statement)+1:], ")")                    
                    #substatement = substatement.lstrip().rstrip()
                    #substatements = substatement.split(" ")
                    #ŹLE - w concepcie mogą być jakies spacje.
                    #trzeba wczytać najpierw concept, zamkniety miedzy nawiasami
                    concept_owl_str = add_functions.get_OWL_concept_expression(line[len(statement)+1:]) #get the OWL expression that represents a DL concept/OWL class
#                    fml_parsed = forms.parser_DL(add_functions.text_for_Lark_parsing(concept_owl_str)) #create the prover's concept/formula object based on concept_owl_text
                    fml_parsed = add_functions.parse_concept_from_ont(concept_owl_str,
                                                                      self.ont_concepts_df,
                                                                      self.ont_roles_df,
                                                                    #  self.ont_Tbox_atoms,
                                                                      flexible_syntax)
                    individual = line[len(statement)+1 + add_functions.count_leading_spaces(line[len(statement)+1:])+len(concept_owl_str):]
                    individual = add_functions.read_until_string(individual, ")").lstrip().rstrip()

                    if individual in world_names_str: #check if the individual named in ClassAssertion statement has already been created
                        for w in self.interpretation.worlds():
                            if w._world_name_str == individual:
                                w._formulas.append(fml_parsed)
                        
                    else:
                        locals()[individual] = x = self.interpretation.add_world([fml_parsed]) 
                        x._world_name_str = individual
                        world_names_str.update({individual})
                        self.ont_individuals_df.loc[len(self.ont_individuals_df)] = [individual,
                                                                                     False]
                    
            
                elif statement == "ObjectPropertyAssertion":
                    substatement = add_functions.read_until_string(line[len(statement)+1:], ")")                    
                    substatement = substatement.lstrip().rstrip()
                    substatements = substatement.split(" ")

                    if flexible_syntax == True:
                        try: #first check if the class/concept has already appeared in declarations or otherwise in the ontology; if so - parse it
                            role = self.ont_roles_df.loc[self.ont_roles_df.source_iri==substatements[0],
                                                         "role_name"].iloc[0]
                        except:
                            #nc = new_concept_name(self.concepts_df)
                            nr = add_functions.new_role_name(self.ont_roles_df)
                            self.ont_roles_df.loc[len(self.ont_roles_df)] = [substatements[0],
                                                                             nr,
                                                                             False]
                            role = nr
                    else:
                        role = substatements[0]


                    if len(substatements) != 3: 
                        raise TypeError("ClassAssertion not properly defined (three expressions divided by spaces are expected")                        

                    #add an individual if it is not already in the interpretation
                    for i in (1,2):
                        if not substatements[i] in world_names_str: #check if the world has already been created in ABox
                            locals()[substatements[i]] = x = self.interpretation.add_world([])
                            x._world_name_str = substatements[i]
                            world_names_str.update({substatements[i]})
                    
                    #add an edge between the individuals        
                    self.interpretation.add_edge(locals()[substatements[1]],locals()[substatements[2]], role)    


                elif statement == "SubClassOf":
                    concept_owl_str_1 = add_functions.get_OWL_concept_expression(line[len(statement)+1:]) #get the OWL expression that represents a DL concept/OWL class
                    fml_parsed_1 = add_functions.parse_concept_from_ont(concept_owl_str_1,
                                                                        self.ont_concepts_df,
                                                                        self.ont_roles_df,
                                                                   #     self.ont_Tbox_atoms,
                                                                        flexible_syntax,
                                                                        if_Tbox_concept = True)
                    concept_owl_str_2 = add_functions.get_OWL_concept_expression(line[len(statement)+1 + add_functions.count_leading_spaces(line[len(statement)+1:])+len(concept_owl_str_1):])
                    fml_parsed_2 = add_functions.parse_concept_from_ont(concept_owl_str_2,
                                                                        self.ont_concepts_df,
                                                                        self.ont_roles_df,
                                                                     #   self.ont_Tbox_atoms,
                                                                        flexible_syntax,
                                                                        if_Tbox_concept = True)
            
            
                    if isinstance(fml_parsed_1, forms.Atom):
                        self.interpretation._Tbox_fold_subs.update({(fml_parsed_1, fml_parsed_2)})
                        left_atom_str = fml_parsed_1.formula_string()
                        right_atoms_str = fml_parsed_2.atom_symbols

                        #self.Tbox_fold_atoms_all.update({left_atom_str})
                        #self.Tbox_fold_atoms_all.update(set(right_atoms_str))
                        
                        #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
                        if left_atom_str in self.graph_Tbox_atoms.keys():
                            self.graph_Tbox_atoms[left_atom_str] = self.graph_Tbox_atoms[left_atom_str].union(set(right_atoms_str))
                        else:
                            self.graph_Tbox_atoms.update({left_atom_str: set(right_atoms_str)})

                    else:
                        self.interpretation._Tbox_unfold_subs.update({(fml_parsed_1, fml_parsed_2)})


                elif statement == "EquivalentClasses":
                    concept_owl_str_1 = add_functions.get_OWL_concept_expression(line[len(statement)+1:]) #get the OWL expression that represents a DL concept/OWL class
                    fml_parsed_1 = add_functions.parse_concept_from_ont(concept_owl_str_1,
                                                                        self.ont_concepts_df,
                                                                        self.ont_roles_df,
                                                                       # self.ont_Tbox_atoms,
                                                                        flexible_syntax,
                                                                        if_Tbox_concept = True)
                    concept_owl_str_2 = add_functions.get_OWL_concept_expression(line[len(statement)+1 + add_functions.count_leading_spaces(line[len(statement)+1:])+len(concept_owl_str_1):])
                    fml_parsed_2 = add_functions.parse_concept_from_ont(concept_owl_str_2,
                                                                        self.ont_concepts_df,
                                                                        self.ont_roles_df,
                                                                        #self.ont_Tbox_atoms,
                                                                        flexible_syntax,
                                                                        if_Tbox_concept = True)


                    if isinstance(fml_parsed_1, forms.Atom):
                        self.interpretation._Tbox_fold_eq.update({(fml_parsed_1, fml_parsed_2)})
                        left_atom_str = fml_parsed_1.formula_string()
                        right_atoms_str = fml_parsed_2.atom_symbols

                        #self.Tbox_fold_atoms_all.update({left_atom_str})
                        #self.Tbox_fold_atoms_all.update(set(right_atoms_str))

                        #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
                        if left_atom_str in self.graph_Tbox_atoms.keys():
                            self.graph_Tbox_atoms[left_atom_str] = self.graph_Tbox_atoms[left_atom_str].union(set(right_atoms_str))
                        else:
                            self.graph_Tbox_atoms.update({left_atom_str: set(right_atoms_str)})

                    else:
                        #self.Tbox_unfold_eq.update({(fml_parsed_1, fml_parsed_2)})
                        self.interpretation._Tbox_unfold_subs.update({(fml_parsed_1, fml_parsed_2)})
                        self.interpretation._Tbox_unfold_subs.update({(fml_parsed_2, fml_parsed_1)})
                        


                elif statement == "DisjointClasses":
                    concept_list_str = list() #list of class/concept strings that corresponds to arguments of DisjointClasses 
                    
                    txt_to_parse = line[len(statement)+1:]
                    
                    while not txt_to_parse in {")", " )", ")\n", " )\n"}:
                        next_concept_str = add_functions.get_OWL_concept_expression(txt_to_parse) #read in the next concept-string in the intersection/conjunction
                        concept_list_str.append(next_concept_str)  
                        txt_to_parse = txt_to_parse[(add_functions.count_leading_spaces(txt_to_parse)+len(next_concept_str)):]
                    
                    concept_list = list()
                    for concept_str in concept_list_str:
                        concept_list.append(add_functions.parse_concept_from_ont(concept_str,
                                                                                 self.ont_concepts_df,
                                                                                 self.ont_roles_df,
                                                                               #  self.ont_Tbox_atoms,
                                                                                 flexible_syntax))
            
                    concept_pairs = list(combinations(concept_list, 2))
            
                    for pair in concept_pairs: 

                        subsumptions = [(pair[0], forms.Negation(pair[1])),
                                        (pair[1], forms.Negation(pair[0]))]                        

                        left_concept = pair[0]
                        right_concept = forms.Negation(pair[1])

                        for left_concept, right_concept in subsumptions:                        
                            if isinstance(left_concept, forms.Atom):
                                self.interpretation._Tbox_fold_subs.update({(left_concept, right_concept)})
                                left_atom_str = left_concept.formula_string()
                                right_atoms_str = right_concept.atom_symbols
        
                                #self.Tbox_fold_atoms_all.update({left_atom_str})
                                #self.Tbox_fold_atoms_all.update(set(right_atoms_str))
        
                                #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
                                if left_atom_str in self.graph_Tbox_atoms.keys():
                                    self.graph_Tbox_atoms[left_atom_str] = self.graph_Tbox_atoms[left_atom_str].union(set(right_atoms_str))
                                else:
                                    self.graph_Tbox_atoms.update({left_atom_str: set(right_atoms_str)})
        
                            else:
                                self.interpretation._Tbox_unfold_subs.update({(left_concept, right_concept)})
        

                    
                    #parsujemy teksty
                    #tworzymy tuple konceptów
                    #jesli lewy to atom - do Tfold
                    #jesli nie - Tunfold
                        #po prostu dwa zbiory tuplów? czy więcej info potrzebne?







        #creating a replacement map for concepts
        if ontology_file_funct_syntax != None and flexible_syntax == True:
            #replacement map for the concepts:
            replacements_map = dict(zip(self.ont_concepts_df.source_iri, self.ont_concepts_df.concept_name))
            pattern_concepts = re.compile("|".join(re.escape(key) for key in sorted(replacements_map.keys(), key=len, reverse=True)))

            #replacement map for the roles:
            replacements_map_r = dict(zip(self.ont_roles_df.source_iri, self.ont_roles_df.role_name))
            pattern_roles = re.compile("|".join(re.escape(key) for key in sorted(replacements_map_r.keys(), key=len, reverse=True)))



        #1. ABox argument-----
        
        if ABox == None:
            pass
        elif not isinstance(ABox, dict):
            raise TypeError("ABox argument was not properly introduced. Please use Python dictionary syntax, with keys corresponding to individuals and values corresponding to a concept or list of concepts")
        else:    
            for world, formulas in ABox.items():
                
                world = world.replace(" ", "")   #white spaces have to be removed

                if bool(re.match(r"i.[A-Z]\w*", world)): #if the world is a local description in the form of the world name, we automatically pass the local description formula to the formula list
                    if isinstance(formulas,list):
                        formulas.append(world) 
                    elif isinstance(formulas,str):
                        formulas = [world] + [formulas]
                

                #for the flexibale_syntax option: replace the "arbitrary string" with simplified one (to be readable by the parser) 
                if ontology_file_funct_syntax != None and flexible_syntax == True:
                    if isinstance(formulas, str):
                        formulas = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], formulas)
                    elif isinstance(formulas, list):
                        for fml in formulas:
                            fml = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], fml)


                #parsing    
                if isinstance(formulas, str):
                    parser_tree = forms.parser_DL.parse(formulas)
                    fml_parsed = forms.ToFml().transform(parser_tree)
                    fmls_parsed = [fml_parsed]
                elif isinstance(formulas, list):
                    fmls_parsed = []
                    for fml in formulas:
                        parser_tree = forms.parser_DL.parse(fml)
                        fml_parsed = forms.ToFml().transform(parser_tree)
                        fmls_parsed.append(fml_parsed)

                    
                #check if the individual was already created in an ontology
                if ontology_file_funct_syntax != None and world in world_names_str:
                    for w in self.interpretation.worlds():
                        if w == world:
                            w._formulas.append(fml_parsed)

                else:
                    locals()[world] = x = self.interpretation.add_world(fmls_parsed)
                    x._world_name_str = world
                    world_names_str.update({world})
                    

            
        #2. RBox argument --
      
        if RBox == None:
            pass
        elif not isinstance(RBox, dict):
            raise TypeError("RBox argument was not properly introduced. Please use Python dictionary syntax, with keys corresponding to relations (roles) and values corresponding to lists, with each of its elements being a list of two related worlds (individuals)")
        else:
            for role, pairs_of_worlds in RBox.items():

                role = role.replace(" ", "")   #white spaces have to be removed


                #for the flexibale_syntax option: replace the "arbitrary string" with simplified one (to be readable by the parser) 
                if ontology_file_funct_syntax != None and flexible_syntax == True and len(self.ont_roles_df)>0:
                    role = pattern_roles.sub(lambda match: replacements_map_r[match.group(0)], role)


                #if the first argument (pair of worlds) is of the form ['w1','w2'] we have to trasform it into [['w1','w2']] for the rest of the code to work properly
                if isinstance(pairs_of_worlds, list) and len(pairs_of_worlds)==2 and isinstance(pairs_of_worlds[0],str):
                    y = list()
                    y.append(pairs_of_worlds)
                    pairs_of_worlds=y

                if not isinstance(pairs_of_worlds, list):
                    raise TypeError("Please insert the information about related worlds as lists of lists of pairs of worlds")  #ERROR!!!!!
                else:
                    for pair in pairs_of_worlds:
                        if not (isinstance(pair, list) and len(pair)==2 and isinstance(pair[0],str) and isinstance(pair[1],str)):
                            raise TypeError("Each pair of worlds should be a separate list composed of two strings") #ERROR

                        pair[0] = pair[0].replace(" ", "")   #white spaces have to be removed
                        pair[1] = pair[1].replace(" ", "")   #white spaces have to be removed
                        
                         
                        for i in (0,1):
                            if not pair[i] in world_names_str: #check if the world has already been created in ABox or in the ontology
                                if bool(re.match(r"i.[A-Z]\w*", pair[i])): #if the world is a local description in the form of the world name, we automatically pass the local description formula to the formula list
                                    parser_tree = forms.parser_DL.parse(pair[i])
                                    fml_parsed = forms.ToFml().transform(parser_tree)
                                    locals()[pair[i]] = x = self.interpretation.add_world([fml_parsed]) 
                                else:
                                    locals()[pair[i]] = x = self.interpretation.add_world([])
                                x._world_name_str = pair[i]
                                world_names_str.update({pair[i]})

                        self.interpretation.add_edge(locals()[pair[0]],locals()[pair[1]], role)    

        
        
        
        #3. concept argument --
        
        #create a concept object
        if concept == None:
            pass
        else:
            #for the flexibale_syntax option: replace the "arbitrary string" with simplified one (to be readable by the parser) 
            if ontology_file_funct_syntax != None and flexible_syntax == True:
                if isinstance(concept, str):
                    concept = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], concept)
                elif isinstance(concept, list):
                    for fml in concept:
                        fml = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], fml)


            #parse the concept(s)            
            if isinstance(concept, str):
                parser_tree = forms.parser_DL.parse(concept)
                fml_parsed = forms.ToFml().transform(parser_tree)
                fmls_parsed = [fml_parsed]
            elif isinstance(concept, list):
                fmls_parsed = []
                for fml in concept:
                    parser_tree = forms.parser_DL.parse(fml)
                    fml_parsed = forms.ToFml().transform(parser_tree)
                    fmls_parsed.append(fml_parsed)
            else:
                raise TypeError("Please insert a correctly built concept or list of concepts in the argument 'concept'")
    

            #name the world "w0"; if this name already appearad in ABox or RBox, choose the first availabe from: {"w00", "w000",...}
            if not 'w0' in world_names_str:
                base_world_name = 'w0'
            else:
                for i in range(2, len(world_names_str) + 2):
                    if 'w'+i*'0' in world_names_str:
                        continue
                    
                    base_world_name = 'w'+i*'0'
                    break

    
            #add the concepts from the argument "concept" to the interpetation
            locals()[base_world_name] = x = self.interpretation.add_world(fmls_parsed)
            x._world_name_str = base_world_name
            world_names_str.update({base_world_name}) 
        
        
        
        #4. TBox argument  --
        
        if TBox == None:
            pass
        else:
            if isinstance(TBox, str):  #single subsumption in the TBox argument
                parser_tree = forms.parser_DL.parse(TBox)
                fml_parsed = forms.ToFml().transform(parser_tree)
                if not isinstance(fml_parsed, forms.Subsumption): 
                    raise TypeError("Please enter only subsumptions in the TBox!")
                fmls_parsed = [fml_parsed]
            elif isinstance(TBox, list):  #list of subsumptions in the TBox argument
                fmls_parsed = []
                for fml in TBox:
                    parser_tree = forms.parser_DL.parse(fml)
                    fml_parsed = forms.ToFml().transform(parser_tree)
                    if not isinstance(fml_parsed, forms.Subsumption):#ERROR!!!!!
                        raise TypeError("Please enter only subsumptions in the TBox!")                    
                    fmls_parsed.append(fml_parsed)
            else:
                raise TypeError("Please insert a subsumption or a list of subsumptions in the TBox argument")    

            #NEW15 do tego momentu stworzylismy listę fml_parsed sparsowanych formul
                #teraz trzeba ew potraktowac je tak samo je te z ontologii


            #we're applying the TBox rule - changing implications to negation of conjunction
            fmls_pairs = [(fml.subs[0], fml.subs[1]) for fml in fmls_parsed]


            for pair in fmls_pairs:                
                if isinstance(pair[0], forms.Atom):
                    self.interpretation._Tbox_fold_subs.update({(pair[0], pair[1])})
                    left_atom_str = pair[0].formula_string()
                    right_atoms_str = pair[1].atom_symbols

                   # self.Tbox_fold_atoms_all.update({left_atom_str})
                   # self.Tbox_fold_atoms_all.update(set(right_atoms_str))
                    
                    #update the graph of Tbox atoms to be used in checking if Tbox is cyclic
                    if left_atom_str in self.graph_Tbox_atoms.keys():
                        self.graph_Tbox_atoms[left_atom_str] = self.graph_Tbox_atoms[left_atom_str].union(set(right_atoms_str))
                    else:
                        self.graph_Tbox_atoms.update({left_atom_str: set(right_atoms_str)})

                else:
                    self.interpretation._Tbox_unfold_subs.update({(pair[0], pair[1])})
            
            del fmls_pairs
            
            
            #OLD VERSION
            #we're applying the TBox rule - changing implications to negation of conjunction
            #fmls_parsed = [forms.Negation(forms.Conjunction(fml.subs[0], forms.Negation(fml.subs[1]))) for fml in fmls_parsed]

            #adding the parsed formulas to all the worlds
            #if len(self.interpretation.worlds())>0:
            #    for w in self.interpretation.worlds():
            #        w._formulas = w._formulas + fmls_parsed 
            #else: #that's when the TBox is the only "source of worlds"
            #    self.w0 = self.interpretation.add_world(fmls_parsed) #world label
            #    self.w0._world_name_str = "w0"
            #    world_names_str.update({"w0"})           

            #self.interpretation.TBox_formulas = set(fmls_parsed)  #saving the TBox (parsed and converted to neg. conjuction) formulas for later (will be placed in every newly created world)
            
            
            
        #ABSORPTION
        #note - the functions used for absorption are contained in the script "TBox_optimisations.py"        
        
        if use_absorption == True:


            #return elements of the TBox transformed by the absorption procedure 
            results = TBox_optimisations.absorb_unfolded_Tbox(self.interpretation._Tbox_unfold_subs,
                                                              self.interpretation._Tbox_fold_subs,
                                                              self.interpretation._Tbox_fold_eq,
                                                              self.interpretation._Tbox_fold_subs_conj,
                                                              self.interpretation._Tbox_fold_subs_neg,
                                                              self.interpretation._Tbox_fold_subs_ex_restr,
#                                                              self.Tbox_fold_atoms_all,
                                                              self.graph_Tbox_atoms)

            self.interpretation._Tbox_unfold_subs = results[0]
            self.interpretation._Tbox_fold_subs = results[1]
            self.interpretation._Tbox_fold_eq = results[2]
            self.interpretation._Tbox_fold_subs_conj = results[3]
            self.interpretation._Tbox_fold_subs_neg = results[4]
            self.interpretation._Tbox_fold_subs_ex_restr = results[5]
 #           self.Tbox_fold_atoms_all = results[6]
            self.graph_Tbox_atoms  = results[6]


        if use_foldable_TBox  == True:

            #function to ensure uniqueness of Tbox
            results = TBox_optimisations.ensure_uniqueness(self.interpretation._Tbox_fold_eq,
                                                           self.interpretation._Tbox_unfold_subs,
                                              #             self.Tbox_fold_atoms_all,
                                                           self.graph_Tbox_atoms)


            self.interpretation._Tbox_fold_eq = results[0]
            self.interpretation._Tbox_unfold_subs = results[1]
#            self.Tbox_fold_atoms_all = results[2]
            self.graph_Tbox_atoms = results[2]
            
            #function to check if Tbox is cyclic, and if so - transform it to an acyclic Tbox            
            results = TBox_optimisations.ensure_Tbox_acyclic(self.interpretation._Tbox_unfold_subs,
                                                             self.interpretation._Tbox_fold_subs,
                                                             self.interpretation._Tbox_fold_eq,
                                                             self.interpretation._Tbox_fold_subs_conj,
                                                             self.interpretation._Tbox_fold_subs_neg,
                                                             self.interpretation._Tbox_fold_subs_ex_restr,
                                             #                self.Tbox_fold_atoms_all,
                                                             self.graph_Tbox_atoms)

            
            if results == None:
                pass
            else:
                self.interpretation._Tbox_unfold_subs = results[0]    
                self.interpretation._Tbox_fold_subs = results[1]
                self.interpretation._Tbox_fold_eq = results[2]
                self.interpretation._Tbox_fold_subs_conj = results[3]
                self.interpretation._Tbox_fold_subs_neg = results[4]
                self.interpretation._Tbox_fold_subs_ex_restr = results[5]
#                self.Tbox_fold_atoms_all = results[6]
                self.graph_Tbox_atoms  = results[6]
                self.no_atoms_in_cycles = results[7]
                



        elif use_foldable_TBox == False and use_absorption == False:
            self.interpretation._Tbox_unfold_subs = self.interpretation._Tbox_unfold_subs | self.interpretation._Tbox_fold_subs  
            del self.interpretation._Tbox_fold_subs
            
        elif use_foldable_TBox == False and use_absorption == True:
            raise TypeError("If the parameter use_absorption is True, use_foldable_TBox cannot be false")
            


            #PRZEFORMUŁOWAĆ I DODAĆ WSZYSTKIE ALTERNATYWY Z UNFOLDABLE TBOX DO SWIATÓW W RAMACH TBOXA
        #adding the parsed formulas to all the worlds

#        fmls_parsed = [forms.Negation(forms.Conjunction(fml.subs[0], forms.Negation(fml.subs[1]))) for fml in fmls_parsed]


        #Add empty world, if there are none
        if len(self.interpretation.worlds()) == 0:
            self.w0 = self.interpretation.add_world(["*T"]) #world label
            self.w0._world_name_str = "w0"
            world_names_str.update({"w0"})

        neg_conjs = [forms.Negation(forms.Conjunction(pair[0], forms.Negation(pair[1]))) for pair in self.interpretation._Tbox_unfold_subs]
#            print(neg_conjs)
#        print(neg_conjs, type(neg_conjs))
     
        if use_SAT_optimisations == True:
            #here, the interpretation._Tbox_unfold_global object will be a list of clauses - sets of disjuncts 
            self.interpretation._Tbox_unfold_global = [forms.unfold_neg_conj_into_set_of_alt(neg_con) for neg_con in neg_conjs]               
#               print(self.interpretation._Tbox_unfold_global)
 
            for w in self.interpretation.worlds():
                w._Tbox_unfold_list_alt.extend(self.interpretation._Tbox_unfold_global)
            
#            print(self.interpretation._Tbox_unfold_global)

        else:
            self.interpretation._Tbox_unfold_global = neg_conjs               

            for w in self.interpretation.worlds():
                 w._formulas = w._formulas + neg_conjs 
                 
                # print("len forms", len(w._formulas))
            
         #       print(w._world_name_str)
#                print("wwwwww", w._formulas, type(w._formulas))
 #               print(neg_conjs, type(neg_conjs))

#        else: #if no individuals/worlds have been declared yet - only Tbox statements were considered
        #    print("no worlds declared")

 #           neg_conjs = [forms.Negation(forms.Conjunction(pair[0], forms.Negation(pair[1]))) for pair in self.interpretation._Tbox_unfold_subs]



  #          self.w0 = self.interpretation.add_world(neg_conjs) #world label
   #         self.w0._world_name_str = "w0"
    #        world_names_str.update({"w0"})           

        #    if use_SAT_optimisations == True:
                #here, the interpretation._Tbox_unfold_global object will be a list of clauses - sets of disjuncts 
       #         self.interpretation._Tbox_unfold_global = [forms.unfold_neg_conj_into_set_of_alt(neg_con) for neg_con in neg_conjs]               
 #               print(self.interpretation._Tbox_unfold_global)

      #          for w in self.interpretation.worlds():
     #               w._Tbox_unfold_list_alt.extend(self.interpretation._Tbox_unfold_global)





            #MAMY INITIAL INTERPERATIAON. TRZEBA SPRAWDZIC CZY SA JAKIES RELACJE WYMINIONE W FOLD_EX_RESTR
        
        
        for pair in self.interpretation._Tbox_fold_subs_ex_restr:
            for w in self.interpretation.worlds():
                if self.interpretation.edge_exists(w, pair[0]):
                    w._formulas.append(pair[1])
                    

                    


            #self.interpretation.TBox_formulas = set(fmls_parsed)  #saving the TBox (parsed and converted to neg. conjuction) formulas for later (will be placed in every newly created world)


            
            #OLD VERSION
            #we're applying the TBox rule - changing implications to negation of conjunction
            #fmls_parsed = [forms.Negation(forms.Conjunction(fml.subs[0], forms.Negation(fml.subs[1]))) for fml in fmls_parsed]

            #adding the parsed formulas to all the worlds
            #if len(self.interpretation.worlds())>0:
            #    for w in self.interpretation.worlds():
            #        w._formulas = w._formulas + fmls_parsed 
            #else: #that's when the TBox is the only "source of worlds"
            #    self.w0 = self.interpretation.add_world(fmls_parsed) #world label
            #    self.w0._world_name_str = "w0"
            #    world_names_str.update({"w0"})           

            #self.interpretation.TBox_formulas = set(fmls_parsed)  #saving the TBox (parsed and converted to neg. conjuction) formulas for later (will be placed in every newly created world)
            








        #DELETING UNNECESSARY OBJECTS
        #del self.graph_Tbox_atoms
        del neg_conjs

            
        #SETTING ADDITIONAL PARAMETERS
            
        #store the world names in an attribute of the interpretation
        self.interpretation._world_names_str = world_names_str


        #?????????????????????????CZY BĘDZIE POTRZEBNE??
        #creating a set of all atom symbols occurring in the interpretation        
        self.interpretation._all_atoms_in_interpretation = set()
#
        #keeping the initial interpretation (before applying any rules)
        self.initial_interpretation = deepcopy(self.interpretation)  
        
        
        #self.file_name = ontology_file_funct_syntax
        
        
        
        ##################################################################
        #5. Solver - we build the tableau ----------------------------------
        #this is the main function to apply on the DL_Tableau object

    def build_tableau(self):
        """Build the tableau by applying the rules from the script "rules".
        
        Argument: the tableau object
        
        Output: a tuple consisting of four objects:
            [0]: True, if the formula is a time-out, False otherwise
            [1]: True, if the formula is satisfiable, False otherwise
            [2]: Number of closed branches
            [3]: Number of applied rules
        """
        


        #initializing a list of all "alternative" interpretations to be explored on branches of the tableau         
        alternative_interpretations = []
                
        #list of rules to applied; the rules will be applied in the order defined in this list

#        if use_SAT_optimisations == True:

        rules_to_apply = [rules.clash_rule,
                          rules.double_neg_rule,
                          rules.conjunction_rule,
                          rules.role_rule_2,
                          rules.negated_conjunction_rule,    #_SAT,   #SAT-inspired conjunction rule
                          rules.local_description_rule_1,
                          rules.local_description_rule_2,
                          rules.local_description_rule_3,
                          rules.local_description_cut_rule,
                          rules.global_description_rule_1,
                       #   rules.global_description_rule_2,
                          rules.global_description_rule_3,
                          rules.global_description_cut_rule,
                          rules.role_rule_1]
 #       else: 
            
  #          rules_to_apply = [rules.clash_rule,
   #                           rules.double_neg_rule,
    #                          rules.conjunction_rule,   
     #                         rules.role_rule_2,
      #                        rules.negated_conjunction_rule,   #regular negated conjunction rule
       #                       rules.local_description_rule_1,
        #                      rules.local_description_rule_2,
         #                     rules.local_description_rule_3,
          #                    rules.local_description_cut_rule,
           #                   rules.global_description_rule_1,
            #                  rules.global_description_rule_2,
             #                 rules.global_description_rule_3,
              #                rules.global_description_cut_rule,
               #               rules.role_rule_1]
            
        
        rules_to_apply = tuple(rules_to_apply)

        no_rules_to_apply = len(rules_to_apply)
        
        #initializing the counter of applied rules
        self.no_rules_applied = 0 
        
        #initializing the variable storing the satifiability status
        self.is_satisfiable = None

        #initializing the counter of closed branches of the tableau (in which an inconsistency has been found)        
        self.closed_branches_count = 0
        
        #division of formulas in the formula list in each world of the interpretation into sets of subtypes of formulas
        #note - the attribute "_formulas" of each world will be a dictionary, composed of sets of formulas as values from now on (not a list, as it was the case in the input)
        for w in self.interpretation.worlds():
            
            new_fml_posit = set()
            new_fml_negat = set()
            
            #TUTAJ ZMIENIC NEGACJE KONIUNKCJI NA PARY, I WLACZYC UNFOLD_TBOX?
            #ALBO NIE RUSZAC JEDNAK TYCH NEGACJI, TYLKO UTRZYMYWAC TEN UNFODL TBOX, JAK ROBILES ZRESTZA WCZESNIEJ
            
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

        #start measuring the time in order to stop proceeding if the prover works too long (if a given time litmit has been crossed; the limit is given below in the while loop)
        start_time = time.time()

        #initialize the iterator of rules
        rules_iterator = 0


        while rules_iterator < no_rules_to_apply:

            #here we set the time limit; if it is exceeded, formula is considered a time-out 
            
#            if runtime_limit_s is not None:
 #               if time.time() - start_time > runtime_limit_s:
  #                  self.time_out = True
   #                 break
            
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
                    #print(rule)
                    self.interpretation = new_interpretation
                    self.no_rules_applied += 1
                    alternative_interpretations.extend(new_alt_interpretations)  #add new "alternative interpretations" to the list - if there are any to add
                    break  
                else:
                    rules_iterator += 1    #rule has not been applied
                        
            if self.is_satisfiable == False:
                break  #out of the whole while loop


        #if there are no more rules to apply and the formula is not a time out - it is satisfiable 
        if self.is_satisfiable is None and self.time_out is False and rules_iterator == no_rules_to_apply:
            self.is_satisfiable = True
            
            
        return(self.time_out, self.is_satisfiable, self.closed_branches_count, self.no_rules_applied)
    


#Other functions to apply on the DL_Tableau object (after applying the rules) ------------------------


    def print_interpretation(self):
        """print interpretation in a text form"""
        #note - the interpretation should not be considered as a proper model 
        
        #print world names and formulas satisfied in the worlds
        for w in self.interpretation.worlds():
            
           # print(f"World name: {w._world_name_str} \n Concepts:")
            for fml in set.union(*w._formulas.values()):
                print("  ", fml)  #print the formulas in "nice" looking form
            print("\n")

        #print relations between worlds
        for v1, w  in self.interpretation._outgoing.items():
            if bool(w): #don't take into account worlds with no outging edges (bool(w) = dictionary w is not empty)
                for v2, mod_types in w.items():
                    for mod_type in mod_types:
                        print(f"Modality type: {mod_type} \n Source world: {v1._world_name_str} \n Target world: {v2._world_name_str} \n")


    def print_interpretation_atoms(self):
        """print interpretation in a text form - this version prints only atoms satisfied in the worlds"""
        #note - the interpretation should not be considered as a proper model 
        
        #print world names and atoms satisfied in the worlds
        for w in self.interpretation.worlds():
            
            print(f"World name: {w._world_name_str} \n Concepts:")
            for fml in (w._formulas['atoms'] | w._formulas['neg_atoms']):
                print("  ", fml)  #print the formulas in "nice" looking form
            print("\n")
       
        #print relations between worlds
        for v1, w  in self.interpretation._outgoing.items():
            if bool(w): #don't take into account worlds with no outging edges (bool(w) = dictionary w is not empty)
                for v2, mod_types in w.items():
                    for mod_type in mod_types:
                        print(f"Modality type: {mod_type} \n Source world: {v1._world_name_str} \n Target world: {v2._world_name_str} \n")



    def print_initial_interpretation(self):
        """print ""initial"" interpretation (before applying the rules) in a text form"""
        #note - the interpretation should not be considered as a proper model 

        
        #print world names and formulas satisfied in the worlds
        for w in self.initial_interpretation.worlds():
            
            print(f"World name: {w._world_name_str} \n Concepts:")
            for fml in w._formulas:
                print("  ", fml)  #print the formulas in "nice" looking form
            print("\n")

        #print relations between worlds       
        for v1, w  in self.initial_interpretation._outgoing.items():
            if bool(w): #don't take into account worlds with no outging edges (bool(w) = dictionary w is not empty)
                for v2, mod_types in w.items():
                    for mod_type in mod_types:
                        print(f"Modality type: {mod_type} \n Source world: {v1._world_name_str} \n Target world: {v2._world_name_str} \n")



    def nodes_count(self):
        """ print the number of nodes in the tableau"""
        return(self.no_rules_applied + 1)

    def branches_count(self):
        """ print the number of branches in the tableau"""
        return(self.closed_branches_count + 1 if self.is_satisfiable else self.closed_branches_count)

    def satisfiability_check(self):
        return("Input satisfiable" if self.is_satisfiable else "Input unsatisfiable")
    
    
    
#    def tabelaric_model_representation(self):
        #upewnić się, że w liscie interpretation._worlds_to_unify nie ma duplikatów




    


