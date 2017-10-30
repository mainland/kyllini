stats = {'Fusion failures': 0}

test("fuse08")
test("fuse08-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse08")
