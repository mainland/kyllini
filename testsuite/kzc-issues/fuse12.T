stats = {'Fusion failures': 0}

test("fuse12")
test("fuse12-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse12")
