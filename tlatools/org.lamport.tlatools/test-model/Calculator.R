calculator <- unique(read.csv(header = TRUE, sep = "#", file = "Calculator.csv"))
calculator$dist2gen <- calculator$distinct/calculator$generated

par(mfrow = c(1, 3))

barplot(
  as.matrix(calculator[, c("dist2gen")]),
  beside = TRUE,
  log = "y",
  col=c("darkblue","red"),
  main = "dist2gen (log)",
  las = 2 # Rotate x-axis labels by 90 degrees
)

barplot(
  as.matrix(calculator[, c("distinct")]),
  beside = TRUE,
  log = "y",
  col=c("darkblue","red"),
  main = "distinct (log)",
  las = 2 # Rotate x-axis labels by 90 degrees
)

barplot(
  as.matrix(calculator[, c("Inc", "Dec", "Mul", "Div", "Rst")]),
  beside = TRUE,
  main = "actions",
  col=c("darkblue","red"),
  las = 2 # Rotate x-axis labels by 90 degrees
)
legend("topright", 
       legend = c("baseline", "rl"), 
       fill = c("darkblue", "red"))