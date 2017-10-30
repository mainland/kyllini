stats = {'Fusion failures': 0}

test("fuse06")
test("fuse06-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse06")
