#!/usr/bin/env Rscript
library(scatterD3)
library(htmlwidgets)
## https://github.com/juba/scatterD3
## https://cran.r-project.org/web/packages/scatterD3/scatterD3.pdf
## https://cran.r-project.org/web/packages/scatterD3/vignettes/introduction.html

caption = list(title = "Notes",
               subtitle = "",
               text = "Builds 50 to 80 ran with excessive coverage reporting set to -Dcoverage=1. The straight line represents the linear regression on throughput.")

data <- read.csv(file('stdin'), header=T, as.is=T)

## Derive some data
data$labels <- ifelse(data$CLOUD == "aws-ec2","", data$CLOUD)
data$urls <- sprintf("https://tla.msr-inria.inria.fr/build/job/M-HEAD-master-TLC-performances/CLOUD=%s,SPEC=%s/%s/", data$CLOUD, data$SPEC, data$BUILD_NUMBER)
data$tooltips <- sprintf("<b>Cloud:</b> %s<br><b>Spec:</b> %s<br><b>Build number:</b> %s<br><b>Commit:</b> %s (%s)", data$CLOUD, data$SPEC, data$BUILD_NUMBER, data$REVISION, data$BRANCH)

## linear regression of throuphput
lma <- lm(VALUE ~ BUILD_NUMBER, data=subset(data, MEASUREMENT == "Throughput"))
line <- data.frame(slope = coef(lma)["BUILD_NUMBER"], intercept = coef(lma)["(Intercept)"], stroke = "red", stroke_width = 3, stroke_dasharray = "7,5")

s <- scatterD3(data = data, x = BUILD_NUMBER, y = VALUE, y_log=T, xlab = "Build Number", ylab = "log(Time&Throughput)", 
               col_var=SPEC, symbol_var = MEASUREMENT,
               url_var = urls, tooltip_text = data$tooltips,
               lab = labels, caption = caption,
               lines = line)
saveWidget(s, file="index.html")
