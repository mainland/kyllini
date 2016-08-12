/--input-dev=dummy/ {
    filename = substr($1, 3, length($1) - 6);
}

/--dummy-samples/ {
    x=index($1, "=");
    nosamples=substr($1, x+1, length($1));
}

/Elapsed cpu time \(sec\):/ {
    time = $5;
    print filename " " nosamples / time / 1e6
}
