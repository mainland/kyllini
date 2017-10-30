stats = {'Fusion failures': 0}

test("fuse03")
test("fuse03-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse03")
