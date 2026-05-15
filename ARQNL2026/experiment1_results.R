install.packages("dplyr")
install.packages("ggplot2")
install.packages("stringr")

library(dplyr)
library(ggplot2)
library(stringr)


data <- read.csv("experiment1_data.csv")


data$concept_size <- str_count(data$concept, "A") + str_count(data$concept, "E") + str_count(data$concept, "i") + str_count(data$concept, "~") + str_count(data$concept, "i")

data_reduced <- data %>% 
  select(concept, time_tableau_min, time_out, data_type, concept_size) %>% 
  filter(!startsWith(concept, "~*E r")) %>% 
  select(-concept)


data_reduced$concept_size_rec <- case_when(data_reduced$concept_size %in% 0:400 ~ "1",
                                    data_reduced$concept_size %in% 401:800 ~ "2",
                                    data_reduced$concept_size %in% 801:1200 ~ "3",
                                    data_reduced$concept_size > 1200 ~ "4")

#Table 2 left-hand part, runtimes
data_reduced %>% 
  group_by(data_type) %>%
  filter(time_out==FALSE) %>% 
  summarise(n=n(),
            runtime = mean(time_tableau_min))

#Table 2 left-hand part, timeout
data_reduced %>% 
  group_by(data_type) %>%
  summarise(n=n(),
            timouts = sum(time_out),
            timouts_share = mean(time_out))


data_reduced$DDs <- ifelse(str_detect(data_reduced$data_type, "DDs_None"),
                           "None",
                           ifelse(str_detect(data_reduced$data_type, "DDs_Medium"),
                                  "Medium",
                                  "High"))


#Table 2 right-hand part, runtimes
data_reduced %>% 
  group_by(DDs, concept_size_rec) %>%
  filter(time_out==FALSE) %>% 
  summarise(n=n(),
            runtime = mean(time_tableau_min))


#Table 2 right-hand part, timeout
data_reduced %>% 
  group_by(DDs, concept_size_rec) %>%
  summarise(n=n(),
            timouts = sum(time_out),
            timouts_share = mean(time_out))


