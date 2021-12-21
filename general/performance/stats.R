## Read input csv file.
library(here)
data <- read.csv(header=TRUE, sep = "#", file = here("out_run-stats.csv"))

## Aggregate generted per minute.
data$GenMin <- data$Generated / data$Duration

## Convert epoch to date.
library(anytime)
data$date <- anytime(data$Timestamp)
