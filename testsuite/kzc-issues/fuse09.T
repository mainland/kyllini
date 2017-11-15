stats = {'Fusion failures': 0}

test("fuse09")
test("fuse09-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse09")
