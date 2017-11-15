stats = {'Fusion failures': 0}

test("fuse07")
test("fuse07-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse07")
