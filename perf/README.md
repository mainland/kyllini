The `perf.sh` script will run the perf benchmarks and place the results in a CSV
file named according to the current branch and git hash. Invoking `perf.sh` with
an extra directory argument, which it assumes is the location of the Ziria Wifi
code, will cause it to run the benchmarks using the Ziria compiler as well. For
example:

```
./perf.sh ~/projects/ziria/Ziria/code/WiFi./perf.sh
```

The `plot.R` R script can be used to plot the CSV data.
