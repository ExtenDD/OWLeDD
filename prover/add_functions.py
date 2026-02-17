import forms

#1. World names generator -------------

"""
The three functions below, combined, generate new world names, making sure that the new name has not been used so far
"""

#generator
def world_names():
    """ a generator of world names of the form w1, w2, w3,... """
    a = 'w'
    n = 1
    while True:
        yield a + str(n) 
        n += 1 

# Function that uses the generator
def get_next_world_name(world_names):
    return next(world_names)

def new_world_name(interpretation):
    """ outputs a new world name, checking if it has not been used so far"""
    worlds_counter = world_names()
    
    x = get_next_world_name(worlds_counter)
    while True:
        if x in interpretation._world_names_str:
            x = get_next_world_name(worlds_counter)
        else:
            break
    
    interpretation._world_names_str.update({x})
    return(x)



#2. Fresh atom names generator -------------

"""
The three functions below, combined, generate new atom names, making sure that the new name has not been used so far
"""


#generator
def fresh_atom_names():
    """ a generator of atom names of the form Fresh_Atom_1, Fresh_Atom_2, Fresh_Atom_3,... """
    a = 'Fresh_Atom_'
    n = 1
    while True:
        yield a + str(n)
        n += 1 

# Function that uses the generator
def get_next_fresh_atom(fresh_atom_names):
    return next(fresh_atom_names)

def new_fresh_atom(interpretation):
    """ outputs a new atom name, checking if it has not been used so far"""
    fresh_atoms_counter = fresh_atom_names()
    
    x = get_next_fresh_atom(fresh_atoms_counter)

    while True:
        if x in interpretation._all_atoms_in_interpretation:
            x = get_next_fresh_atom(fresh_atoms_counter)
        else:
            break
    
    interpretation._all_atoms_in_interpretation.update({x})
    return(x)
        


#3. Concept names generator (for classes from ontologies, turned into DL concepts) -------------

"""
The three functions below, combined, generate new concept names, which is useful when concept names appear, that are not declared in the ontology or contain characters problematic for the parser
"""

#generator
def concept_names():
    """ a generator of world names of the form w1, w2, w3,... """
    a = 'C'
    n = 1
    while True:
        yield a + str(n) 
        n += 1 

# Function that uses the generator
def get_next_concept_name(concept_names):
    return next(concept_names)

def new_concept_name(concept_data_frame):
    """ outputs a new world name, checking if it has not been used so far"""
    concepts_counter = concept_names()
  
    x = get_next_concept_name(concepts_counter)
    while True:
        if x in concept_data_frame.concept_name.values:
           # print("yes")
            x = get_next_concept_name(concepts_counter)
        else:
            break
    
    return(x)


#4. Role names generator (for properties from ontologies, turned into DL roles) -------------

"""
The three functions below, combined, generate new role names, which is useful when role names appear, that are not declared in the ontology or contain characters problematic for the parser
"""

#generator
def role_names():
    """ a generator of world names of the form w1, w2, w3,... """
    a = 'r'
    n = 1
    while True:
        yield a + str(n) 
        n += 1 

# Function that uses the generator
def get_next_role_name(role_names):
    return next(role_names)

def new_role_name(role_data_frame):
    """ outputs a new world name, checking if it has not been used so far"""
    roles_counter = role_names()
  
    x = get_next_role_name(roles_counter)
    while True:
        if x in role_data_frame.role_name.values:
            #print("yes")
            x = get_next_role_name(roles_counter)
        else:
            break
    
    return(x)





#5. Functions for for strings (for parsing the ontologies in functional syntax) -----------------------------

def get_OWL_concept_expression(string):
    string = string.lstrip()
    counter = 0
    i = 0
    concept_string = str()
#    ls = len(string)

    if string[0]== "(":
        raise TypeError("An OWL expression representing a class/concept cannot start with parenthesis")

    while string[i] != "(":
        concept_string = concept_string + string[i]
        i += 1
        if string[i] == " " or string[i] == ")":
            return(concept_string)

    while True:
        if string[i] == "(":
            counter += 1
        elif string[i] == ")":
            counter -= 1
        
        concept_string = concept_string + string[i]
        
        if counter == 0:
            break

        i += 1

    return(concept_string)



#first strips the leading spaces reads a string until a "limit_string" character is met 
#if the "limit_string_alt" is also given, reads a string until either of the given limit strings are met
def read_until_string(string, limit_string, limit_string_alt = None):
    
    string = string.lstrip()
    
    ls_pos = string.find(limit_string)
        
    if limit_string_alt == None:
        limit_string_pos = ls_pos
    else:
        ls_alt_pos = string.find(limit_string_alt)

        if ls_pos == -1:
            limit_string_pos = ls_alt_pos
        elif ls_alt_pos==-1:
            limit_string_pos = ls_pos
        else:
            limit_string_pos = min(ls_pos, ls_alt_pos)
        
    return(string if limit_string_pos==-1 else string[0:limit_string_pos])


    


def count_leading_spaces(str):
    return len(str) - len(str.lstrip(' '))





def parse_concept_from_ont(concept_owl_str,
                           ont_concepts_df,
                           ont_roles_df,
                           #ont_Tbox_atoms,
                           flexible_syntax,
                           if_Tbox_concept = False):
    
 #   print("1 ", concept_owl_str)
 #   len_total = len(concept_owl_str)
    start = read_until_string(concept_owl_str, "(", " ")
    txt_to_parse = concept_owl_str[len(start)+1:]
#    len_txt_to_parse = len_total - len(start) -1    
#    len_txt_to_parse = len(txt_to_parse)
#    print("2 ", start)
 #   print("3 ", txt_to_parse)
    
    if start == "ObjectIntersectionOf":
        concept_list = list() #list of class/concept strings that corresponds to arguments of ObjectIntersectionOf 
        
        while not txt_to_parse in {")", " )"}:
            next_concept_str = get_OWL_concept_expression(txt_to_parse) #read in the next concept-string in the intersection/conjunction
            concept_list.append(next_concept_str)  
            txt_to_parse = txt_to_parse[(count_leading_spaces(txt_to_parse)+len(next_concept_str)):]
  #          print(concept_list)
  #          print(txt_to_parse)

        no_concepts = len(concept_list)
        if no_concepts<2:
            raise TypeError("ObjectIntersectionOf needs to be have at least two classes/concepts as arguments")                        

        concept_out = forms.Conjunction(parse_concept_from_ont(concept_list[0],
                                                               ont_concepts_df,
                                                               ont_roles_df,
                                                             #  ont_Tbox_atoms,
                                                               flexible_syntax), parse_concept_from_ont(concept_list[1],
                                                                                                        ont_concepts_df,
                                                                                                        ont_roles_df,
                                                                                                        #ont_Tbox_atoms,
                                                                                                        flexible_syntax))
        
        i = no_concepts-2
        while i > 0:
            concept_out = forms.Conjunction(concept_out,
                                            parse_concept_from_ont(concept_list[no_concepts - i],
                                                                   ont_concepts_df,
                                                                   ont_roles_df,
                                                               #    ont_Tbox_atoms,
                                                                   flexible_syntax))
            i -= 1                                

        return(concept_out)

    if start == "ObjectUnionOf":
        concept_list = list() #list of class/concept strings that corresponds to arguments of ObjectIntersectionOf 
        
        while not txt_to_parse in {")", " )"}:
            next_concept_str = get_OWL_concept_expression(txt_to_parse) #read in the next concept-string in the intersection/conjunction
            concept_list.append(next_concept_str)  
            txt_to_parse = txt_to_parse[(count_leading_spaces(txt_to_parse)+len(next_concept_str)):]
   #         print(concept_list)
   #         print(txt_to_parse)

        no_concepts = len(concept_list)
        if no_concepts<2:
            raise TypeError("ObjectUnionOf needs to be have at least two classes/concepts as arguments")                        

        concept_out = forms.Negation(forms.Conjunction(forms.Negation(parse_concept_from_ont(concept_list[0],
                                                                                             ont_concepts_df,
                                                                                             ont_roles_df,
                                                                                           #  ont_Tbox_atoms,
                                                                                             flexible_syntax)),
                                                       forms.Negation(parse_concept_from_ont(concept_list[1],
                                                                                             ont_concepts_df,
                                                                                             ont_roles_df,
                                                                                            # ont_Tbox_atoms,
                                                                                             flexible_syntax))))
        
        i = no_concepts-2
        while i > 0:
            concept_out = forms.Negation(forms.Conjunction(concept_out.sub,
                                                           forms.Negation(parse_concept_from_ont(concept_list[no_concepts - i],
                                                                                                 ont_concepts_df,
                                                                                                 ont_roles_df,
                                                                                             #    ont_Tbox_atoms,
                                                                                                 flexible_syntax))))
            i -= 1                                

        return(concept_out)


    elif start == "ObjectComplementOf":
        concept_out = forms.Negation(parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
                                                            ont_concepts_df,
                                                            ont_roles_df,
                                                        #    ont_Tbox_atoms,
                                                            flexible_syntax))
        return(concept_out)


#forms.parser_DL.parse(ont_concepts_df.loc[ont_concepts_df.source_iri==start, "concept_name"].iloc[0])

    elif start == "ObjectSomeValuesFrom":
        role = read_until_string(txt_to_parse, " ")
        txt_to_parse = txt_to_parse[(count_leading_spaces(txt_to_parse)+len(role)):]

        if flexible_syntax == True:
           try: #first check if the class/concept has already appeared in declarations or otherwise in the ontology; if so - parse it
               role = ont_roles_df.loc[ont_roles_df.source_iri==role, "role_name"].iloc[0]
           except:
               #nc = new_concept_name(self.concepts_df)
               nr = new_role_name(ont_roles_df)
               ont_roles_df.loc[len(ont_roles_df)] = [role,
                                                      nr,
                                                      False]
               role = nr
               
           concept_out = forms.Diamond(role,
                                       parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
                                                              ont_concepts_df,
                                                              ont_roles_df,
                                                            #  ont_Tbox_atoms,
                                                              flexible_syntax))
           return(concept_out)

        else:
#            if not ont_concepts_df['source_iri'].isin(['concept_owl_str'])
            if role not in set(ont_roles_df.source_iri):            
                ont_roles_df.loc[len(ont_roles_df)] = [role,
                                                       None,
                                                       False]

            concept_out = forms.Diamond(role,
                                       parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
                                                              ont_concepts_df,
                                                              ont_roles_df,
                                                         #     ont_Tbox_atoms,
                                                              flexible_syntax))
            return(concept_out)
 
 

    elif start == "ObjectAllValuesFrom":
        role = read_until_string(txt_to_parse, " ")
        txt_to_parse = txt_to_parse[(count_leading_spaces(txt_to_parse)+len(role)):]

        if flexible_syntax == True:
            try: #first check if the class/concept has already appeared in declarations or otherwise in the ontology; if so - parse it
                role = ont_roles_df.loc[ont_roles_df.source_iri==role, "role_name"].iloc[0]
            except:
                #nc = new_concept_name(self.concepts_df)
                nr = new_role_name(ont_roles_df)
                ont_roles_df.loc[len(ont_roles_df)] = [role,
                                                      nr,
                                                      False]
                role = nr
               
            concept_out = forms.Negation(forms.Diamond(role,
                                       forms.Negation(parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
                                                                             ont_concepts_df,
                                                                             ont_roles_df,
                                                                            # ont_Tbox_atoms,
                                                                             flexible_syntax))))
            return(concept_out)

        else:
#            if not ont_concepts_df['source_iri'].isin(['concept_owl_str'])
            if role not in set(ont_roles_df.source_iri):            
                ont_roles_df.loc[len(ont_roles_df)] = [role,
                                                       None,
                                                       False]

            concept_out = forms.Negation(forms.Diamond(role,
                                       forms.Negation(parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
                                                                             ont_concepts_df,
                                                                             ont_roles_df,
                                                                          #   ont_Tbox_atoms,
                                                                             flexible_syntax))))
            return(concept_out)
    



#        concept_out = forms.Negation(forms.Diamond(role,
 #                                                  forms.Negation(parse_concept_from_ont(get_OWL_concept_expression(txt_to_parse),
  #                                                                                       ont_concepts_df,
   #                                                                                      ont_roles_df,
    #                                                                                     flexible_syntax))))
     #   return(concept_out)

                            
    elif start == "owl:Thing":
        parser_tree = forms.parser_ONT.parse("*T")
        return(forms.ToFml().transform(parser_tree))

        
    elif start == "owl:Nothing":  
        parser_tree = forms.parser_ONT.parse("*F")
        return(forms.ToFml().transform(parser_tree))
    

    else: #this option corresponds to an atomic class/concept
        if flexible_syntax == True:
            try: #first check if the class/concept has already appeared in declarations or otherwise in the ontology; if so - parse it
                parser_tree = forms.parser_ONT.parse(ont_concepts_df.loc[ont_concepts_df.source_iri==start, "concept_name"].iloc[0])
                return(forms.ToFml().transform(parser_tree))
            except:
                #nc = new_concept_name(self.concepts_df)
                nc = new_concept_name(ont_concepts_df)
                ont_concepts_df.loc[len(ont_concepts_df)] = [concept_owl_str,
                                                             nc,
                                                             False]
                #updating the table with names of atomic concepts occuring in the TBox
          #      if if_Tbox_concept == True:
          #          if nc in set(ont_Tbox_atoms.atom_name):
          #              pass
          #          else:
          #              ont_Tbox_atoms.loc[len(ont_Tbox_atoms)] = [concept_owl_str,
          #                                                          nc]

                parser_tree = forms.parser_ONT.parse(nc)
                return(forms.ToFml().transform(parser_tree))

        else:
#            if not ont_concepts_df['source_iri'].isin(['concept_owl_str'])
            if concept_owl_str not in set(ont_concepts_df.source_iri):            
                ont_concepts_df.loc[len(ont_concepts_df)] = [concept_owl_str,
                                                             None,
                                                             False]

            #updating the table with names of atomic concepts occuring in the TBox
           # if if_Tbox_concept == True:
           #     if concept_owl_str in set(ont_Tbox_atoms.atom_name):
           #         pass
           #     else:
           #         ont_Tbox_atoms.loc[len(ont_Tbox_atoms)] = [concept_owl_str,
           #                                                     None]

            parser_tree = forms.parser_ONT.parse(concept_owl_str)
            return(forms.ToFml().transform(parser_tree))
            

            

