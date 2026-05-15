#This script can be used to perform some experiments on ontologies of ALC expressivity (in functional syntax), by outputing selected information about the tableau procedure, such as runtime, number of applied rules, etc.

import os

#set the folder path in which all the prover scripts are contained as well as the ontologies and the "ont_metadata.csv" file
#NOTE: as we are not entitled to put ontology files on our github, please download them using http://owl.cs.manchester.ac.uk/publications/supporting-material/ore-2015-report/

#set the folder path
folder path = ""
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
    #create tableau
    tab = tableau.DL_Tableau(ontology = row.ore2015_filename,
                                  flexible_syntax = True)

    results.loc[row.Index, 'is_sat'] = tab.is_satisfiable
    results.loc[row.Index, 'no_branches_explored'] = tab.branches_count()
    results.loc[row.Index, 'no_rules_applied'] = tab.nodes_count()
    results.loc[row.Index, "total_runtime"] = tab.parsing_time + tab.runtime 
    results.loc[row.Index, "pars_runtime"] = tab.parsing_time
    results.loc[row.Index, "tab_runtime"] = tab.runtime





