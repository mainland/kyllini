stats = {'Fusion failures': 0}

test("fuse01")
test("fuse01-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse01")
