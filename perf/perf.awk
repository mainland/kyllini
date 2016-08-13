/Elapsed cpu time \(sec\):/ {
    cpuTime = $5;
}

/Elapsed real time \(sec\):/ {
    realTime = $5;
}

/branch-instructions/ {
    branchInstructions = $1;
}

/branch-misses/ {
    branchMisses = $1;
}

/cache-misses/ {
    cacheMisses = $1;
}

/cpu-cycles/ {
    cpuCycles = $1;
}

/instructions/ {
    instructions = $1;
}

/context-switches/ {
    contextSwitches = $1;
}

/cpu-migrations/ {
    cpuMigrations = $1;
}

/page-faults/ {
    pageFaults = $1;
}

END {
    print platform "," gitRev "," test "," nsamples "," cpuTime "," realTime "," branchInstructions "," branchMisses "," cacheMisses "," cpuCycles "," instructions "," contextSwitches "," cpuMigrations "," pageFaults
}
