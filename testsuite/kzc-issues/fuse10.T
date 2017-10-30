stats = {'Top-level repeat': True,
         'Fusion failures': 0}

test("fuse10")
test("fuse10-fusion", [should_fail, only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse10")
