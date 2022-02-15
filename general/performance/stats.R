## Read input csv file.
library(here)
data <- read.csv(header=TRUE, sep = "#", file = here("out_run-stats.csv"))

## Merge two or more commits when they cannot impact performance because
## a commit only changes auxiliary files.
## Replace git commit short-hash f91... with df1...
data[data == "f91c7b0"] <- "df144c5"
data[data == "46de326"] <- "df144c5"


data[data == "0f6a80b"] <- "1eb600d"
data[data == "0b93602"] <- "1eb600d"

## Convert epoch to date.
library(anytime)
data$Date <- anytime(data$Timestamp)
  
## Aggregate multiple runs.
data <- aggregate(cbind(Generated,Duration) ~ Spec + RevTag + Workers, data = data, FUN = mean, na.rm = TRUE)

## Calculate Throughput on aggregated data.
data$Throughput <- data$Generated / data$Duration

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
