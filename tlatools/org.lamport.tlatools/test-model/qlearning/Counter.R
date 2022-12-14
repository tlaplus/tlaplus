  require(ggplot2)
  require(dplyr)
  require(gridExtra)
  
  df <- read.csv(header = TRUE, sep = "#", file = "./Counter.csv")
  df$Val <- as.numeric(df$Val)
  df$Time <- as.numeric(df$Time)
  
  ####################
  
  ## Action Frequency
  rlaf <- df %>%
    filter(Mode == "rl") %>%
    group_by(Action) %>%
    summarize(count = n()) %>%
    ggplot(aes(x=Action, y=count)) +
    geom_bar(stat="identity") +
    ggtitle("RL Actions")
  
  rndaf <- df %>%
    filter(Mode == "random") %>%
    group_by(Action) %>%
    summarize(count = n()) %>%
    ggplot(aes(x=Action, y=count)) +
    geom_bar(stat="identity") +
    ggtitle("Random Actions")
  
  grid.arrange(rlaf, rndaf, ncol=2)
  
  ####################
  
  dfrl <- df %>%
      filter(Mode == "rl") %>%
      group_by(Val) %>%
      summarize(count = n()) 
  
  rl <- dfrl %>%
      ggplot(aes(x=Val, y=count)) +
      geom_bar(stat="identity") +
      ggtitle("RL") +
      scale_y_continuous(trans='log2')
  
  dfrnd <- df %>%
    filter(Mode == "random") %>%
    group_by(Val) %>%
    summarize(count = n())
  
  rnd <- dfrnd %>%
    ggplot(aes(x=Val, y=count)) +
    geom_bar(stat="identity") +
    ggtitle("Random") +
    scale_y_continuous(trans='log2')
  
  grid.arrange(rl, rnd, ncol=2)