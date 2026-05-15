import os
#set the path to a folder in which all the prover files are present
path = ""
os.chdir(path)



import numpy as np
import pandas as pd
from math import ceil
import random
import random_concept_generator_arqnl
import tableau_experiments_arqnl
import timeit
import forms


#set the random seed
#random seeds for the 9 generated datasets are in the file readme_arqnl.txt
random_seed =5
random.seed(random_seed)



#1. Generating sets of random conceptss----------------

#1.1. preparation --

#number of concepts to generate
no_concepts = 120

#create empty data.frame first
data = pd.DataFrame(index=range(no_concepts), columns=['concept', 'no_atoms',
                                                       'time_tableau_min','time_tableau_avg',
                                                       'time_out', 'is_satisfiable',
                                                       'no_rules_applied', 'no_branches_explored'])



#1.2. generating the random formulas --

for i in range(no_concepts):

    #choose the number of atoms; this will determine the size of the generated syntax tree
    no_atoms = random.randint(10,500)

    #set parameters of formulas to be generated    
    rand_concept = random_concept_generator_arqnl.random_ALCi_concept_str(no_atoms = no_atoms,
                                                                          no_diff_atoms = ceil(no_atoms/2),
                                                                          neg_chance = 0.5,
                                                                          #no_modal = 0,
                                                                          no_modal = ceil((2*no_atoms-1)*0.4),
                                                                          #no_LD = 0.0001,
                                                                          no_LD = ceil(0.2*(no_atoms-1)),
                                                                          #GD_chance = 0)
                                                                          GD_count = ceil(0.2*(no_atoms-1)))
                                                                           #GD_count = 0)


    data.loc[i, 'concept'] = rand_concept
    data.loc[i, 'no_atoms'] = no_atoms


data.to_csv('NEW_GD20_LD20_MOD40_test.csv')




#2. Building the tableau --------------------------------------------------

#read in the file
data = 'NEW_GD20_LD20_MOD40.csv'


data = pd.read_csv(data, 
                   usecols = ['concept', 'time_tableau_min','time_tableau_avg',
                              'time_out', 'is_satisfiable',
                              'no_rules_applied', 'no_branches_explored'])


#2.1. measuring tableau generation time --

preparation_parser = """
import tableau_experiments_arqnl
tab = tableau_experiments_arqnl.DL_Tableau(concept = concept)
"""

n=0
for row in data.itertuples():
    
    concept = row.concept

    time_tableau = timeit.repeat(stmt='tab.build_tableau()',
                                  setup = preparation_parser,
                                  number=1, 
                                  repeat = 3,
                                  globals=globals())
    
    data.loc[row.Index, 'time_tableau_min'] = min(time_tableau)
    data.loc[row.Index, 'time_tableau_avg'] = np.mean(time_tableau)
    n +=1
    print("tab built", n)


#2.2. gathering information about the tableau --


for row in data.itertuples():
    
    concept = row.concept

    tab = tableau_experiments_arqnl.DL_Tableau(concept = concept)

    tab_result = tab.build_tableau()

    data.loc[row.Index, 'time_out'] = tab_result[0]
    data.loc[row.Index, 'is_satisfiable'] = tab_result[1]
    data.loc[row.Index, 'no_branches_explored'] = (tab_result[2] + 1) if tab_result[1] else tab_result[2]
    data.loc[row.Index, 'no_rules_applied'] = tab_result[3]
    
    
    
data.to_excel('RESULTS_GD20_LD20_MOD40.xlsx')


