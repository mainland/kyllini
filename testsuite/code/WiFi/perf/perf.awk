/--input-dev=dummy/ {
    filename = substr($1, 3, length($1) - 6);
}

/--dummy-samples/ {
    x=index($1, "=");
    nosamples=substr($1, x+1, length($1));
}

/Time elapsed \(usec\):/ {
    time = $4;
    print filename " " nosamples / time
}
