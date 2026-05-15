#Experiment 1

In order to reproduce experiment 1 from our ARQNL2026 paper, you first need to place all the prover files in one folder, with "tableau.py" replaced by "tableau_experiments_arqnl.py", and additionally with the files  "data_generation_arqnl.py" and "random_concept_generator_arqnl.py". This latter file is the random concept generator, and the file "data_generation_arqnl.py" can be used to generate concepts and files that have been used in the experiment. Below are the random seeds for the 9 datasets mentioned in the paper:

#dataset 1: no DDs, and no existential or universal restrictions:
#random seed: 60

#dataset 2: medium amount of DDs, and no existential or universal restrictions:
#random seed: 71

#dataset 3: high amount of DDs, and no existential or universal restrictions:
#random seed: 99

#dataset 4: no DDs, medium amount of existential or universal restrictions:
#random seed: 49

#dataset 5: medium amount of DDs, medium amount of existential or universal restrictions:
#random seed: 101

#dataset 6: high amount of DDs, medium amount of existential or universal restrictions:
#random seed: 47

#dataset 7: no DDs, high amount of existential or universal restrictions:
#random seed: 112

#dataset 8: medium amount of DDs, high amount of existential or universal restrictions:
#random seed: 88

#dataset 9: high amount of DDs, high amount of existential or universal restrictions:
#random seed: 5


The collective resultant dataset is also included as "experiment1_data.csv". To obtain the data from Table 2 presented in the paper you can use the R script "experiment1_results.R".



#Experiment 2

In order to repeat the second experiment from the paper, you can use the script "experiment2_arqnl.py". 
However, as we are not entitled to put ontology files on our github, please download them using http://owl.cs.manchester.ac.uk/publications/supporting-material/ore-2015-report/
