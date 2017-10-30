stats = {'Fusion failures': 0}

test("fuse11")
test("fuse11-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse11")
