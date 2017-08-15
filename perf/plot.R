#!/usr/bin/env Rscript
library(RColorBrewer)
library(ggplot2)
library(optparse)
library(plyr)
library(tikzDevice)

option_list = list(
  make_option(c("--presentation"), action="store_true", default=FALSE,
              help="produce color plots for presentation"),
  make_option(c("--color"), action="store_true", default=FALSE,
              help="produce color plots for publication"),
	make_option(c("--odir"), type="character", default=NULL,
              help="output directory [default=current directory]"),
  make_option(c("--format"), type="character", default="pdf",
              help="output format [default=%default]. Valid choices are pdf or tikz"),
  make_option(c("--combined-data"), type="character", dest="combined_data", default=NULL,
              help="combined (old) ziria/kzc benchmark data"),
  make_option(c("--ziria-data"), type="character", dest="ziria_data", default=NULL,
              help="ziria benchmark data"),
  make_option(c("--kzc-data"), type="character", dest="kzc_data", default=NULL,
              help="kzc benchmark data"),
  make_option(c("--kzc-alt-data"), type="character", dest="kzc_alt_data", default=NULL,
              help="alternative kzc benchmark data"),
  make_option(c("--component-data"), type="character", dest="component_data", default=NULL,
              help="component-wise benchmark data")
);

test_args <- c("--hspiral",
               "data/timing.csv",
               "--clock-rate",
               "3.4",
               "--format",
               "pdf");

opt_parser = OptionParser(option_list=option_list);
opt = parse_args(opt_parser);
#opt = parse_args(opt_parser, args=test_args);

data <-rbind()

if (!is.null(opt$combined_data)) {
  combined_data <- read.csv(opt$combined_data)
  data <- rbind(combined_data[combined_data$platform == "ziria",],
                combined_data[combined_data$platform == "kzc",])
}

if (!is.null(opt$ziria_data)) {
  ziria <- read.csv(opt$ziria_data)
  ziria$platform <- factor("ziria")
  data <- rbind(data, ziria)
}

if (!is.null(opt$kzc_data)) {
  kzc <- read.csv(opt$kzc_data)
  kzc$platform <- factor("kzc")
  data <- rbind(data, kzc)
}

if (!is.null(opt$kzc_alt_data)) {
  kzc_alt <- read.csv(opt$kzc_alt_data)
  kzc_alt$platform <- factor("kzc-alt")
  data <- rbind(data, kzc_alt)
}

if (!is.null(opt$component_data)) {
  component <- read.csv(opt$component_data)
}

summarizeRates <- function(data) {
  ddply(data, c("platform", "test"), summarize,
        meanRate=mean(rate, na.rm=TRUE),
        sd=sd(rate, na.rm=TRUE),
        n=sum(!is.na(rate)),
        se=sd/sqrt(n))
}

rateRatios <- function(data, numeratorPlat, denominatorPlat) {
  ddply(data, ~test, here(summarize),
        ratio=meanRate[platform == numeratorPlat]/meanRate[platform == denominatorPlat],
        ratioMax=(meanRate[platform == numeratorPlat]+sd[platform == numeratorPlat])/
                 (meanRate[platform == denominatorPlat]-sd[platform == denominatorPlat]),
        ratioMin=(meanRate[platform == numeratorPlat]-sd[platform == numeratorPlat])/
                 (meanRate[platform == denominatorPlat]+sd[platform == denominatorPlat]))
}

scaleFill <- function(breaks, labels) {
  if (opt$presentation) {
    scale_fill_brewer(type="qual", palette="Dark2",
                      name="Implementation",
                      breaks=breaks,
                      labels=labels)
  } else if (opt$color) {
    scale_fill_brewer(type="qual", palette="Set3",
                      name="Implementation",
                      breaks=breaks,
                      labels=labels)
  } else {
    scale_fill_grey(start=0.4, end=0.9,
                    name="Implementation",
                    breaks=breaks,
                    labels=labels)
  }
}

ratePlot <- function(data, cols, ytitle, breaks, labels, lpos) {
  data <- data[data$test %in% cols,]
  data$rate = data$nsamples/data$cpuTime/1e6

  # Explicitly order by breaks
  dataSummary <- summarizeRates(data)
  dataSummary$platform <- factor(dataSummary$platform, levels=breaks)
  dataSummary <- dataSummary[order(dataSummary$platform),]

  limits <- aes(ymin=meanRate-sd, ymax=meanRate+sd)
  dodge <- position_dodge(.9)

  plot <- ggplot(dataSummary, aes(x=factor(test, levels=cols), y=meanRate, fill=platform)) +
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(limits,
                  width=.2,
                  position=dodge) +
    scaleFill(breaks, labels) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.4) +
    theme(legend.position=lpos,
          legend.title=element_blank(),
          legend.text=element_text(size=16),
          legend.background=element_rect(fill="transparent")) +
    theme(axis.title.x=element_blank(),
          axis.title.y=element_text(size=16),
          axis.text.x=element_text(angle=45, hjust=1, size=16))

  return(plot)
}

ratioPlot <- function (data, cols, ytitle, lpos) {
  data <- data[data$test %in% cols,]
  data$rate = data$nsamples/data$cpuTime/1e6

  data <- summarizeRates(data)
  data <- rateRatios(data, 'kzc', 'ziria')
  data$pos = data$ratio < 1

  plot <- ggplot(data, aes(x=reorder(factor(test, levels=cols), ratio), y=ratio, fill=pos)) +
    geom_bar(position=position_dodge(), stat="identity") +
    geom_errorbar(aes(ymin=ratioMin, ymax=ratioMax),
                  width=.2,
                  position=position_dodge(.9)) +
    scaleFill(breaks, labels) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.4) +
    theme(legend.position="none") +
    theme(axis.title.x=element_blank(),
          axis.title.y=element_text(size=16),
          axis.text.x=element_text(angle=60, hjust=1, size=14))

  return(plot)
}

rateBoxPlot <- function (data, cols, ytitle, lpos) {
  d <- data[data$test %in% cols,]
  d$rate = d$nsamples/d$cpuTime/1e6

  plot <- ggplot(d, aes(x=factor(test, levels=cols), y=rate, fill=platform)) +
    geom_boxplot() +
    scale_fill_grey(name="Implementation",
                    breaks=c("kzc", "ziria"),
                    labels=c("KZC", "Ziria")) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.5) +
    theme(legend.position=lpos) +
    theme(axis.title.x=element_blank(),axis.text.x=element_text(angle=45, hjust=1))

  return(plot)
}

breaks <- c("ziria", "kzc", "kzc-alt")

if (opt$format == "tikz") {
  labels <- c("\\textsf{wplc} (C++)", "\\textsf{kzc} (C++)", "\\textsf{kzc} (native Ziria)")
} else {
  labels <- c("wplc (C++)", "kzc (C++)", "kzc (native Ziria)")
}

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

rxPlot <- ratePlot(data, rxCols, "Data rate (Msamples/sec)", breaks, labels, c(0.86, 0.85))
txPlot <- ratePlot(data, txCols, "Data rate (Mbits/sec)", breaks, labels, c(0.18, 0.85))
rxBlocksPlot <- ratePlot(data, rxBlockCols, "Throughput (Msamples/sec)", breaks, labels, c(0.1, 0.85))
txBlocksPlot <- ratePlot(data, txBlockCols, "Throughput (Msamples/sec)", breaks, labels, c(0.1, 0.85))

perfRatioPlot <- ratioPlot(data, c(rxCols, txCols),
                           if (opt$format == "tikz") {
                             "Performance ratio (\\textsf{kzc}/\\textsf{wplc})"
                           } else {
                             "Performance ratio (kzc/wplc)"
                           },
                           c(0.85, 0.85))
perfRatioPlot <- perfRatioPlot + coord_cartesian(ylim = c(0.95, 1.35))

blockPerfRatioPlot <- ratioPlot(data, perfRatioColums,
                                if (opt$format == "tikz") {
                                  "Performance ratio (\\textsf{kzc}/\\textsf{wplc})"
                                } else {
                                  "Performance ratio (kzc/wplc)"
                                },
                                c(0.85, 0.85))
blockPerfRatioPlot <- blockPerfRatioPlot + scale_y_log10() + annotation_logticks(sides="l")

figs <- list(list("rx", rxPlot),
             list("tx", txPlot),
             list("perfRatio", perfRatioPlot),
             list("blockPerfRatio", blockPerfRatioPlot))

if (!is.null(opt$component_data)) {
  data <- rbind(kzc, component)

  columns <- c("Viterbi", "IFFT", "FFT")

  categories <- c("kzc", "base", "peval")
  labels <- c("Sora", "KZC (unoptimized)", "KZC (optimized)")

  data <- data[data$platform %in% categories,]

  blocksPlot <- ratePlot(data, columns, "Throughput (Msamples/sec)", categories, labels, c(0.2, 0.85)) +
    theme(aspect.ratio=0.8) +
    theme(legend.text=element_text(size=10),
          legend.key.size=unit(2,'lines')) +
    theme(axis.title.y=element_text(size=10, margin=margin(0,30,0,0)),
          axis.text.x=element_text(angle=45, hjust=1.2, size=10))

  figs[[length(figs)+1]] <- list("blocks", blocksPlot)
}

# Rewrite generated TikZ code to get rid of extra whitespace
# See:
#   https://stackoverflow.com/questions/36023898/ggplot2-and-tikzdevice-removing-white-space
fixTikz <- function(path) {
  lines <- readLines(con=path)
  lines <- lines[-which(grepl("\\path\\[clip\\]*", lines,perl=F))]
  lines <- lines[-which(grepl("\\path\\[use as bounding box*", lines,perl=F))]
  writeLines(lines,con=path)
}

figPath <- function(name, ext) {
  if (is.null(opt$odir)) {
    paste(name, ext, sep=".")
  } else {
    file.path(opt$odir, paste(name, ext, sep="."))
  }
}

tikzFig <- function(fig) {
  path <- figPath(fig[[1]], "tikz")
  tikz(file=path)
  print(fig[[2]])
  dev.off()
  fixTikz(path)
}

pdfFig <- function(fig) {
  pdf(file=figPath(fig[[1]], "pdf"))
  print(fig[[2]])
  dev.off()
}

if (opt$format == "tikz") {
  dummy <- lapply(figs, tikzFig)
} else if (opt$format == "pdf") {
  dummy <- lapply(figs, pdfFig)
}
