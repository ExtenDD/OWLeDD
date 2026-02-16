import os
os.chdir('C:\\projekt_UŁ\\python\\FLOC_2026')

import numpy as np
import pandas as pd
import re
#from math import ceil
import timeit
import time
import forms
import tableau
#import tableau_exp

os.chdir('C:\\projekt_UŁ\\DL\\ore competition sample\\ore2015_sample\\pool_sample\\dl\\consistency\\files_consistency_dl')

ont = pd.read_csv('ont_metadata.csv', sep=';')

#ont = ont[0:3]
ont = ont[ont.ax_size_type == "very large"]
#ont = ont[ont.ore2015_filename == "ore_ont_2338.owl"]
#ont = ont[ont.ore2015_filename != "small"]
ont = ont[0:1]


ont["pars_runtime"] = pd.Series(dtype="float64")
ont["prover_runtime_min"] = pd.Series(dtype="float64")
ont["prover_runtime_av"] = pd.Series(dtype="float64")
ont["prover_runtime_SAT_min"] = pd.Series(dtype="float64")
ont["prover_runtime_SAT_av"] = pd.Series(dtype="float64")
ont["is_sat"] = False
ont["TBox_cyclic"] = False
ont['no_rules_applied'] = pd.Series(dtype="float64")
ont['no_branches_explored'] = pd.Series(dtype="float64")

#ont.info()
#ont.head()



for row in ont.itertuples():

    #measuring parsing time
    start_time = time.time()
    tab_init = tableau.DL_Tableau(ontology_file_funct_syntax = row.ore2015_filename)
    end_time = time.time()
    ont.loc[row.Index, "pars_runtime"] = end_time - start_time
    
    print("parser", row.ore2015_filename)

    #building the tableau in order to gather information about it
    tab = tableau.DL_Tableau.build_tableau(tab_init)

    print("tab", row.ore2015_filename)

    ont.loc[row.Index, 'is_sat'] = tab[1]
    #ont.loc[row.Index, 'time_out'] = tab_result[0]
    ont.loc[row.Index, 'no_branches_explored'] = (tab[2] + 1) if tab[1] else tab[2]
    ont.loc[row.Index, 'no_rules_applied'] = tab[3]


#3.1. measuring exact tableau generation time --


preparation_parser = """
import tableau
tab_init = tableau.DL_Tableau(ontology_file_funct_syntax = row.ore2015_filename)
"""

n=0
for row in ont.itertuples():

    time_tableau = timeit.repeat(stmt='tab_init.build_tableau()',
                                  setup = preparation_parser,
                                  number=1, 
                                  repeat = 5,
                                  globals=globals())
    
    ont.loc[row.Index, "prover_runtime_SAT_min"] = min(time_tableau)
    ont.loc[row.Index, "prover_runtime_SAT_av"] = np.mean(time_tableau)
    
    n +=1
    print("tab built", n)
    

ont.to_csv('data_very_large8.csv')
#data.to_excel('data.xlsx')
#ont.to_csv('tt.csv')



#EXPERIMENTS WITH DESCRIPTIONS---------------------

#idziemy po konceptach
#testujemy i.A
#zapisujemy runtime i spełnialnosć (ew też l. regul i branches)
#pyt.: jak to zrobić, żeby parsing był zrobiony tylko raz?


import os
os.chdir('C:\\projekt_UŁ\\python\\FLOC_2026')

import tableau
from copy import deepcopy
import random
import numpy as np
import pandas as pd
import re
#from math import ceil
import time
import forms


random_seed = 40   #set random seed
random.seed(random_seed)

os.chdir('C:\\projekt_UŁ\\python\\FLOC_2026')
tab_orig = tableau.DL_Tableau(ontology_file_funct_syntax = 'testing2.owl',
                         flexible_syntax = True)

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


n = 0
for row in results.itertuples():

    tab = deepcopy(tab_orig)

    atom_str = results.loc[row.Index, "source_iri"]
    
    #replace the "arbitrary string" with simplified one (to be readable by the parser) - consistently with the map applied for the prover
    atom_str = pattern_concepts.sub(lambda match: replacements_map[match.group(0)], atom_str)
    
    parser_tree = forms.parser_DL.parse(atom_str)
    atom = forms.ToFml().transform(parser_tree)
    
    #passing the definite description to the ABox
    dd_concept = forms.Description_Local(atom)     #choose whether to test a local description or its negation
  #  dd_concept = forms.Negation(forms.Description_Local(atom))
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
    print("tab built", n)



os.chdir('C:\\projekt_UŁ\\python\\FLOC_2026\\exp2')
results.to_csv('test9596.csv')




