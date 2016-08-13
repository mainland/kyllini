#!/usr/bin/env Rscript
# install.packages("ggplot2")
library(plyr)
library(ggplot2)
library(RColorBrewer)
library(tikzDevice)

data <- read.csv("master-2f2e7096.csv")

txCols <- c("TX 6Mbps","TX 9Mbps","TX 12Mbps","TX 18Mbps","TX 24Mbps","TX 36Mbps","TX 48Mbps","TX 54Mbps")
rxCols <- c("RX 6Mbps","RX 9Mbps","RX 12Mbps","RX 18Mbps","RX 24Mbps","RX 36Mbps","RX 48Mbps","RX 54Mbps")

txBlockCols <- c("Encoding 12","Encoding 23","Encoding 34",
                 "Interleaving BPSK","Interleaving QPSK","Interleaving 16QAM","Interleaving 64QAM",
                 #"Modulating BPSK","Modulating QPSK","Modulating 16QAM","Modulating 64QAM",
                 "IFFT","Map OFDM","Scramble")

rxBlockCols <- c("CCA",
                 "Pilot tracking","Remove DC","LTS",
                 "FFT","Viterbi",
                 "Channel Equalization",
                 #"Data symbol",
                 #"Down-sample",
                 #"De-interleave BPSK","De-interleave QPSK","De-interleave QAM16","De-interleave QAM64",
                 "De-map BPSK","De-map QPSK","De-map QAM16","De-map QAM64")

rxtxPlot <- function (data, cols, ytitle, lpos) {
  data <- data[data$test %in% cols,]
  data$rate = data$nsamples/data$cpuTime/1e6
  
  # Calculate mean and standard deviation
  dataSummary <- ddply(data, c("platform", "test"), summarise,
                       meanRate=mean(rate, na.rm=TRUE),
                       sd=sd(rate, na.rm=TRUE),
                       n=sum(!is.na(rate)),
                       se=sd/sqrt(n))
  
  plot <- ggplot(dataSummary, aes(x=factor(test, levels=cols), y=meanRate, fill=platform)) +
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=meanRate-sd, ymax=meanRate+sd),
                  width=.2,
                  position=position_dodge(.9)) +
    scale_fill_brewer(type="qual", palette="Dark2",
                      name="Implementation",
                      breaks=c("kzc", "ziria"),
                      labels=c("kzc", "Ziria")) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.5) +
    theme(legend.position=lpos) +
    theme(axis.title.x=element_blank(),axis.text.x=element_text(angle=45, hjust=1))
  
  return(plot)
}

rxtxBoxPlot <- function (data, cols, ytitle, lpos) {
  d <- data[data$test %in% cols,]
  d$rate = d$nsamples/d$cpuTime/1e6
  
  plot <- ggplot(d, aes(x=factor(test, levels=cols), y=rate, fill=platform)) +
    geom_boxplot() +
    scale_fill_grey(name="Implementation",
                    breaks=c("kzc", "ziria"),
                    labels=c("kzc", "Ziria")) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.5) +
    theme(legend.position=lpos) +
    theme(axis.title.x=element_blank(),axis.text.x=element_text(angle=45, hjust=1))
  
  return(plot)
}

rxp <- rxtxPlot(data, rxCols, "Receive rate (Msamples/sec)", c(0.85, 0.85))
txp <- rxtxPlot(data, txCols, "Transmission rate (Mbits/sec)", c(0.1, 0.85))
rxbp <- rxtxPlot(data, rxBlockCols, "Throughput (Msamples/sec)", c(0.1, 0.85))
txbp <- rxtxPlot(data, txBlockCols, "Throughput (Msamples/sec)", c(0.1, 0.85))

# tikz(file="rx.tex")
# print(rxp)
# dev.off()
# 
# tikz(file="tx.tex")
# print(txp)
# dev.off()
