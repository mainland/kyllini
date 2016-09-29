#!/usr/bin/env Rscript
# install.packages("ggplot2")
library(plyr)
library(ggplot2)
library(RColorBrewer)
library(tikzDevice)

ziria   <- read.csv("data/ziria-2016-09-28-mainland-ghc710-b5f8a17c.csv")
wifi    <- read.csv("data/wifi-2016-09-28-perf-a5734919.csv")
wifiSid <- read.csv("data/wifi-sid-2016-09-28-perf-a5734919.csv")
pepm    <- read.csv("data/pepm-component-2016-09-28-perf-20592cb4.csv")

data <- rbind(ziria, wifi, wifiSid)

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

perfRatioColums <- c("Encoding 12","Encoding 23","Encoding 34",
                     "Interleaving BPSK","Interleaving QPSK","Interleaving 16QAM","Interleaving 64QAM",
                     "Modulating BPSK","Modulating QPSK","Modulating 16QAM","Modulating 64QAM",
                     "IFFT","Map OFDM","Scramble",
                     "CCA",
                     "Pilot tracking","Remove DC","LTS",
                     "FFT","Viterbi",
                     "Channel Equalization",
                     "Data symbol",
                     "Down-sample",
                     "De-interleave BPSK","De-interleave QPSK","De-interleave QAM16","De-interleave QAM64",
                     "De-map BPSK","De-map QPSK","De-map QAM16","De-map QAM64")

summarizeRates <- function(data) {
  summary <- ddply(data, c("platform", "test"), summarize,
                   meanRate=mean(rate, na.rm=TRUE),
                   sd=sd(rate, na.rm=TRUE),
                   n=sum(!is.na(rate)),
                   se=sd/sqrt(n))

  return (summary)
}

rateRatios <- function(data, numeratorPlat, denominatorPlat) {
  ratios <- ddply(data, ~test, here(summarize),
                  ratio=meanRate[platform == numeratorPlat]/meanRate[platform == denominatorPlat],
                  ratioMax=(meanRate[platform == numeratorPlat]+sd[platform == numeratorPlat])/
                           (meanRate[platform == denominatorPlat]-sd[platform == denominatorPlat]),
                  ratioMin=(meanRate[platform == numeratorPlat]-sd[platform == numeratorPlat])/
                           (meanRate[platform == denominatorPlat]+sd[platform == denominatorPlat]))
  return(ratios)
}

ratePlot <- function(data, cols, ytitle, breaks, labels, lpos) {
  data <- data[data$test %in% cols,]
  data$rate = data$nsamples/data$cpuTime/1e6

  dataSummary <- summarizeRates(data)

  limits <- aes(ymin=meanRate-sd, ymax=meanRate+sd)
  dodge <- position_dodge(.9)

  plot <- ggplot(dataSummary, aes(x=factor(test, levels=cols), y=meanRate, fill=platform)) +
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(limits,
                  width=.2,
                  position=dodge) +
    scale_fill_brewer(type="qual", palette="Dark2",
                      name="Implementation",
                      breaks=breaks,
                      labels=labels) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.4) +
    theme(legend.position=lpos,
          legend.title=element_blank(),
          legend.text=element_text(size=16)) +
    theme(axis.title.x=element_blank(),
          axis.title.y=element_text(size=16),
          axis.text.x=element_text(angle=45, hjust=1, size=16))

  return(plot)
}

ratioPlot <- function (data, cols, ytitle, lpos) {
  data <- data[data$test %in% cols,]
  data$rate = data$nsamples/data$cpuTime/1e6

  data <- summarizeRates(data)
  data <- rateRatios(data, 'wifi', 'ziria')
  data$pos = data$ratio < 1

  plot <- ggplot(data, aes(x=reorder(factor(test, levels=cols), ratio), y=ratio, fill=pos)) +
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=ratioMin, ymax=ratioMax),
                  width=.2,
                  position=position_dodge(.9)) +
    scale_fill_brewer(type="qual", palette="Dark2") +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.4) +
    theme(legend.position="none") +
    theme(axis.title.x=element_blank(),
          axis.title.y=element_text(size=16),
          axis.text.x=element_text(angle=45, hjust=1, size=14))

  return(plot)
}

rateBoxPlot <- function (data, cols, ytitle, lpos) {
  d <- data[data$test %in% cols,]
  d$rate = d$nsamples/d$cpuTime/1e6

  plot <- ggplot(d, aes(x=factor(test, levels=cols), y=rate, fill=platform)) +
    geom_boxplot() +
    scale_fill_grey(name="Implementation",
                    breaks=c("wifi", "ziria"),
                    labels=c("KZC", "Ziria")) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.5) +
    theme(legend.position=lpos) +
    theme(axis.title.x=element_blank(),axis.text.x=element_text(angle=45, hjust=1))

  return(plot)
}

breaks <- c("ziria", "wifi", "wifi-sid")
labels <- c("Ziria", "KZC", "KZC (new)")

rxPlot <- ratePlot(data, rxCols, "Data rate (Msamples/sec)", breaks, labels, c(0.9, 0.87))
txPlot <- ratePlot(data, txCols, "Data rate (Mbits/sec)", breaks, labels, c(0.1, 0.87))
rxBlocksPlot <- ratePlot(data, rxBlockCols, "Throughput (Msamples/sec)", breaks, labels, c(0.1, 0.85))
txBlocksPlot <- ratePlot(data, txBlockCols, "Throughput (Msamples/sec)", breaks, labels, c(0.1, 0.85))

perfRatioPlot <- ratioPlot(data, c(rxCols, txCols),
                           "Performance ratio (kzc/wplc)",
                           c(0.85, 0.85))
perfRatioPlot <- perfRatioPlot + coord_cartesian(ylim = c(0.95, 1.35))

blockPerfRatioPlot <- ratioPlot(data, perfRatioColums,
                                "Performance ratio (kzc/wplc)",
                                c(0.85, 0.85))
blockPerfRatioPlot <- blockPerfRatioPlot + scale_y_log10() + annotation_logticks(sides="l")

pepmData <- rbind(wifi, pepm)

pepmColumns <- c("IFFT", "FFT", "Viterbi")

categories <- c("wifi", "base", "peval")
labels <- c("Sora", "KZC (unoptimized)", "KZC (optimized)")

pepmData <- pepmData[pepmData$platform %in% categories,]

pepmBlocksPlot <- ratePlot(pepmData, pepmColumns, "Throughput (Msamples/sec)", categories, labels, c(0.85, 0.85))
