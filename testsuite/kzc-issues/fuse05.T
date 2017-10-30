stats = {'Fusion failures': 0}

test("fuse05")
test("fuse05-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse05")
