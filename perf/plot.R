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
  make_option(c("--hspiral"), type="character", dest="hspiral", default=NULL,
              help="HSpiral benchmark data"),
  make_option(c("--clock-rate"), type="double", dest="clock_rate", default=NULL,
              help="clock rate in GHz")
);

test_args <- c("--hspiral",
               "data/timing.csv",
               "--clock-rate",
               "3.4",
               "--format",
               "pdf");

opt_parser = OptionParser(option_list=option_list);
#opt = parse_args(opt_parser);
opt = parse_args(opt_parser, args=test_args);

data <-rbind()

if (!is.null(opt$hspiral)) {
  hspiral <- read.csv(opt$hspiral)
  data <- rbind(data, hspiral)
}

data$time <- data$cycles/(opt$clock_rate*1000000000)
data$synthn <- 5*data$N*log2(data$N)
data$mflops <- data$synthn/data$time/1000000

# FLOPS per cycle
data$flops <- data$synthn/data$cycles

summarizeFlops <- function(data) {
  ddply(data, c("platform", "N"), summarize,
        meanFlops=mean(flops, na.rm=TRUE),
        sd=sd(flops, na.rm=TRUE),
        n=sum(!is.na(flops)),
        se=sd/sqrt(n))
}

scaleColor <- function(name, breaks, labels) {
  if (opt$presentation) {
    scale_color_brewer(type="qual", palette="Dark2",
                       name=name,
                       breaks=breaks,
                       labels=labels)
  } else if (opt$color) {
    scale_color_brewer(type="qual", palette="Set3",
                       name=name,
                       breaks=breaks,
                       labels=labels)
  } else {
    scale_color_grey(start=0.0, end=0.8,
                     name=name,
                     breaks=breaks,
                     labels=labels)
  }
}

flopsPlot <- function(data, cols, ytitle, breaks, labels, lpos) {
  data <- data[data$N %in% cols,]

  # Explicitly order by breaks
  dataSummary <- summarizeFlops(data)
  dataSummary$platform <- factor(dataSummary$platform, levels=breaks)
  dataSummary <- dataSummary[order(dataSummary$platform),]

  limits <- aes(ymin=meanFlops-sd, ymax=meanFlops+sd)
  dodge <- position_dodge(.9)

  plot <- ggplot(dataSummary, aes(x=as.factor(N), y=meanFlops, color=platform, shape=platform)) +
    geom_point() +
    #geom_errorbar(limits,
    #              width=.2,
    #              position=dodge) +
    scaleColor("Implementation", breaks, labels) +
    scale_shape(name="Implementation",
                solid=TRUE,
                size=10,
                breaks=breaks,
                labels=labels) +
    ylab(ytitle) +
    theme_bw() +
    theme(aspect.ratio=0.4) +
    theme(legend.position=lpos,
          legend.title=element_blank(),
          legend.text=element_text(size=12),
          legend.background=element_rect(fill="transparent")) +
    theme(axis.title.x=element_blank(),
          axis.title.y=element_text(size=14),
          axis.text.x=element_text(size=10))
  
  return(plot)
}

breaks <- c("hspiral", "spiral", "fftw3")
labels <- c("HSpiral", "Spiral", "FFTW3")

nCols <- c("2", "4", "8", "16", "32", "64", "128", "256", "512")

flops <- flopsPlot(data,
                   nCols,
                   if (opt$format == "tikz") {
                     "Performance (Flops/cycle)"
                   } else {
                     "Performance (Flops/cycle)"
                   },
                   breaks, labels, c(0.1, 0.85))

figs <- list(list("flops", flops))

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
