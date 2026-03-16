#This script can be used to perform some experiments on ontologies of ALC expressivity (in functional syntax), by outputing selected information about the tableau procedure, such as runtim, number of applied rules, etc.
#In particular, it can be used to repeat the experiments that were performed for our submission to IJCAR 2026 conference


###############
#PART 1 --- the first part of the script can be used to find runtimes for parsing and consistency check for selected ontologies

import os

#set the folder path in which all the prover scripts are contained as well as the ontologies and the "ont_metadata.csv" file
#NOTE: as we are not entitled to put ontology files on our github, please download them using http://owl.cs.manchester.ac.uk/publications/supporting-material/ore-2015-report/

#folder path = .....
os.chdir(folder_path)

import numpy as np
import pandas as pd
import re
import timeit
import time
import forms
import tableau

results = pd.read_csv('ont_metadata.csv', sep=';')

results["total_runtime"] = pd.Series(dtype="float64")
results["pars_runtime"] = pd.Series(dtype="float64")
results["tab_runtime"] = pd.Series(dtype="float64")
results["is_sat"] = False
results['no_rules_applied'] = pd.Series(dtype="float64")
results['no_branches_explored'] = pd.Series(dtype="float64")

#loop over the ontologies, by names of the files that contain them (contained in the column ")
for row in results.itertuples():

    #measuring parsing time
    start_time = time.time()
    #create tableau
    tab = tableau.DL_Tableau(ontology = row.ore2015_filename,
                                  flexible_syntax = True,
                                  measure_time = True)
    end_time = time.time()

    results.loc[row.Index, 'is_sat'] = tab.is_satisfiable
    results.loc[row.Index, 'no_branches_explored'] = tab.branches_count()
    results.loc[row.Index, 'no_rules_applied'] = tab.nodes_count()
    results.loc[row.Index, "total_runtime"] = end_time - start_time
    results.loc[row.Index, "pars_runtime"] = tab.parsing_complete_time - start_time
    results.loc[row.Index, "tab_runtime"] = end_time - tab.parsing_complete_time


#final results are contained in the table "results"



###############
#PART 2 --- the second part of the script can be used to find runtimes for consistency check of an ontology with respect to a concept with a local definitie description (or its negation)

#for this part of the script a different version of the sript "tableu.py" will be needed: "tableau_exp_DD.py"
#set the folder path in which all the prover scripts are contained (with "tableau_exp_DD.py") as well as the ontologies (in functional syntax)

import os

#set the folder path in which all the prover scripts are contained (with "tabeau_exp_DD.py")

#folder path = .....
os.chdir(folder_path)

import tableau_exp_DD
from copy import deepcopy
import random
import pandas as pd
import time
import forms
import re

random_seed = 16   #set random seed
random.seed(random_seed)

#in our IJCAR submission we have used a separate random_seed for each ontology. Here are the random_seeds:
#ore_ont_2229.owl: random seed = 11
#ore_ont_2338.owl: random seed = 16
#ore_ont_2608.owl: random seed = 17
#ore_ont_4516.owl: random seed = 18
#ore_ont_7833.owl: random seed = 19
#ore_ont_10366.owl: random seed = 20
    


#when using the script "tabeau_exp_DD.py" (instead of "tabeau.py"), we first perform the parsing and initial preparation and save it in the object tab_orig. The tableaux itself will be be built later (using a separate function on the DL_Tableau object)
#in definition of the DL_Tableau object, choose the ontology for which you want to produce the results
tab_orig = tableau_exp_DD.DL_Tableau(ontology = "ore_ont_2338.owl",
                         flexible_syntax = True,
                         measure_time = True)

tab = deepcopy(tab_orig)

results = tab.ont_concepts_df

results["runtime"] = pd.Series(dtype="float64")
results["is_sat"] = False
results['no_rules_applied'] = pd.Series(dtype="float64")
results['no_branches_explored'] = pd.Series(dtype="float64")

#choosing a random subset of 30 rows 
results = results.sample(n=30, random_state=random_seed)

#replace the "arbitrary string" with simplified one (to be readable by the parser) - consistently with the map applied for the prover
replacements_map = dict(zip(results.source_iri, results.concept_name))
pattern_concepts = re.compile("|".join(re.escape(key) for key in sorted(replacements_map.keys(), key=len, reverse=True)))

#this loops goes through the 30 randomly chosen concepts, and generates the 
#NOTE in the middle of loop you decide whether a local definite description should be added to the ABox, or negation of a local definite description
n = 0
for row in results.itertuples():

    tab = deepcopy(tab_orig)

    atom_str = results.loc[row.Index, "source_iri"]
    
    #replace the "arbitrary string" with simplified one (to be readable by the parser) - consistently with the map applied for the prover
    atom_str = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], atom_str)
    
    parser_tree = forms.parser_DL.parse(atom_str)
    atom = forms.ToFml().transform(parser_tree)
    
    #passing the local definite description to the ABox
    #choose whether to test a local description or its negation (choose only one, comment the second one)
    dd_concept = forms.Description_Local(atom)     #local description
  #  dd_concept = forms.Negation(forms.Description_Local(atom))    #negation of a local description
    individual = "working_indiv" 
    x = tab.interpretation.add_world([dd_concept])
    x._world_name_str = individual

    #measuring runtime
    start_time = time.time()
    tab_results = tab.build_tableau()
    end_time = time.time()

    results.loc[row.Index, "runtime"] = end_time - start_time
    results.loc[row.Index, 'is_sat'] = tab_results[1]
    results.loc[row.Index, 'no_branches_explored'] = (tab_results[2] + 1) if tab_results[1] else tab_results[2]
    results.loc[row.Index, 'no_rules_applied'] = tab_results[3]

    n +=1
    #this printout is just to track how many tableaus have been built so far
    print("tab built", n)





#using the final results, you can calculate the average values over the 30 randomly chosen concepts
results.runtime.mean()
results.no_rules_applied.mean()
results.no_branches_explored.mean()





