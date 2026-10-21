#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
import numpy as np, sys, time
J=int(sys.argv[1]); CH=2**24
for j in range(29, J+1):
    t0=time.time(); E=0
    for start in range(0, 2**j, CH):
        y = np.arange(start, start+CH, dtype=np.int64)
        for _ in range(j):
            odd = (y & 1).astype(bool); y = np.where(odd, (3*y+1)>>1, y>>1)
        E += int((1-2*(y&1)).sum())
    print(f"j={j} E={E} E/2^(j/2)={E/2**(j/2):.3f} ({time.time()-t0:.0f}s)", flush=True)
