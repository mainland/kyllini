stats = {'Fusion failures': 0}

test("fuse01", [only_way('fuse-simpl')], compile_and_run)
test("fuse01-fusion", [only_way('fuse-simpl'), wantStats(stats)], compile_stats, source="fuse01")
