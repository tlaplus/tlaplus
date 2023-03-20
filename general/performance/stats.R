## Read input csv file.
library(here)
data <- read.csv(header=TRUE, sep = "#", file = here("out_run-stats.csv"))

## Merge two or more commits when they cannot impact performance because
## a commit only changes auxiliary files.
## Replace git commit short-hash f91... with df1...

## Original code
data[data == "9035dfa"] <- "6f05042"
data[data == "46de326"] <- "6f05042"

## No LazyValue chains: PR #799
## https://github.com/tlaplus/tlaplus/commit/682f17227a607a5c5486415dcc9008a66dccb805
#data[data == "xxx"] <- "682f172"

## LazyValue disabled (commit 8ef124090c3ee0ee5bc22dc25e1874605ff57f3b):
#data[data == "xxx"] <- "8ef1240"


## Convert epoch to date.
library(anytime)
data$Date <- anytime(data$Timestamp)
  
## Aggregate multiple runs.
data <- aggregate(cbind(Generated,Duration) ~ Spec + RevTag + Workers, data = data, FUN = mean, na.rm = TRUE)

## Calculate Throughput on aggregated data.
data$Throughput <- data$Generated / data$Duration

##################

# Get the baseline throughput values
baseline <- data[data$RevTag == "6f05042", c("Spec", "Workers", "Throughput")]
names(baseline)[3] <- "baseline_throughput"

# Merge baseline_throughput to the original data frame
data <- merge(data, baseline, by = c("Spec", "Workers"))

# Calculate the change in throughput percentage
data$change <- (data$Throughput - data$baseline_throughput) / data$baseline_throughput * 100

library(knitr)
kable(format = "markdown", data[data$RevTag != "6f05042", ][, c(3,1,2,8)], digits=2)

##################

lma <- lm(Throughput ~ RevTag, data)
line <- data.frame(slope = coef(lma)["RevTag"], intercept = coef(lma)["(Intercept)"], stroke = "red", stroke_width = 3, stroke_dasharray = "7,5")

library(scatterD3)
#library(htmlwidgets)
s <- scatterD3(data = data, 
               x = RevTag, y = Throughput, y_log=T,
               xlab = "RevTag", ylab = "log(Time&Throughput)", 
               col_var=Spec
               )
plot(s)

library(htmlwidgets)
saveWidget(s, file="index.html")

##################

library(dplyr)
trend <- data %>%
  group_by(Spec, RevTag, Workers) %>% 
  summarise(Throughput = mean(Throughput)) %>%
  arrange(Spec, Workers) %>% 
  group_by(Spec, Workers) %>%
  summarise(
    inc = (first(Throughput) - last(Throughput)) / first(Throughput), 
    increase = scales::percent(inc)
  )

library(knitr)
trend <- trend[order(-trend$inc),]
kable(format = "markdown", trend[, c(1,2,4)], digits=2)
