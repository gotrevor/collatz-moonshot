#!/usr/bin/env bash
# runr.sh X1 R NPROC TAG : rsearch over [1, X1+1) in 800 chunks, NPROC parallel.
set -euo pipefail
X1=$1; R=$2; NP=$3; TAG=$4
D=logs/$TAG; mkdir -p "$D"
HI=$((X1+1)); NCH=800; STEP=$(( (HI + NCH - 1) / NCH ))
seq 0 $((NCH-1)) | xargs -P "$NP" -I{} bash -c '
  i={}; lo=$(( i*'"$STEP"' )); hi=$(( (i+1)*'"$STEP"' )); [ $hi -gt '"$HI"' ] && hi='"$HI"'
  [ $lo -lt 1 ] && lo=1
  ./rsearch $lo $hi '"$R"' 1 > '"$D"'/chunk_$i.out 2> '"$D"'/chunk_$i.err'
cat "$D"/chunk_*.out > "$D"/found.txt || true
python3 - "$D" "$X1" "$R" <<'PY'
import sys,glob,re
D,X1,R=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
tot=dict(dips=0,runcap=0,found=0,overflow=0); steps=0.0; ranges=[]
for f in glob.glob(D+'/chunk_*.err'):
    s=open(f).read()
    m=re.search(r'range \[(\d+),(\d+)\) R=(\d+): dips=(\d+) runcap=(\d+) found=(\d+) overflow=(\d+) steps=([\d.e+]+)',s)
    assert m,(f,s)
    lo,hi,r=map(int,m.group(1,2,3)); assert r==R
    ranges.append((lo,hi))
    for i,k in enumerate(['dips','runcap','found','overflow']): tot[k]+=int(m.group(4+i))
    steps+=float(m.group(8))
ranges.sort(); assert ranges[0][0]==1 and ranges[-1][1]==X1+1
assert all(a[1]==b[0] for a,b in zip(ranges,ranges[1:])),'gap'
n=X1-4
assert tot['dips']+tot['runcap']+tot['found']+tot['overflow']==n,(tot,n)
out=f"COVERAGE [1,{X1}] contiguous in {len(ranges)} chunks; R={R}; candidates (excl. 1,2,4,44)={n}; {tot}; steps={steps:.4e}"
print(out); open(D+'/summary.txt','w').write(out+'\n')
PY
echo "found/overflow lines:"; cat "$D"/found.txt
