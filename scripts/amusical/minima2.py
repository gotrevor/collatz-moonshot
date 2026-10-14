import sys
from collections import Counter
from minima import status
N=int(sys.argv[1])
mins=[n for n in range(1,N+1) if status(n)=='min']
import json; json.dump(mins, open(f'mins_{N}.json','w'))
print(N, len(mins), len(mins)/N, 20*len(mins)/N)
for M in (6,12,24,36,72):
    c=Counter(m%M for m in mins); tot=len(mins)
    print(M, sorted((r, round(v/tot,4)) for r,v in c.items()))
