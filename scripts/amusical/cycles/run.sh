#!/usr/bin/env bash
# run.sh X0 H NPROC TAG : run cyclemin over [1, X0+1) in chunks, NPROC in parallel.
# Logs: logs/TAG/chunk_*.{out,err}; summary: logs/TAG/summary.txt
set -euo pipefail
X0=$1; H=$2; NP=$3; TAG=$4
D=logs/$TAG; mkdir -p "$D"
HI=$((X0+1)); NCH=400; STEP=$(( (HI + NCH - 1) / NCH ))
seq 0 $((NCH-1)) | xargs -P "$NP" -I{} bash -c '
  i={}; lo=$(( i*'"$STEP"' )); hi=$(( (i+1)*'"$STEP"' )); [ $hi -gt '"$HI"' ] && hi='"$HI"'
  [ $lo -lt 1 ] && lo=1
  ./cyclemin $lo $hi '"$H"' 1 > '"$D"'/chunk_$i.out 2> '"$D"'/chunk_$i.err'
cat "$D"/chunk_*.out > "$D"/found.txt || true
python3 - "$D" "$X0" "$H" <<'PY'
import sys,glob,re
D,X0,H=sys.argv[1],int(sys.argv[2]),int(sys.argv[3])
tot=dict(dips=0,survivors=0,found=0,fpcoll=0); steps=0.0; ml=0; ranges=[]
for f in glob.glob(D+'/chunk_*.err'):
    s=open(f).read()
    m=re.search(r'range \[(\d+),(\d+)\) H=(\d+): dips=(\d+) survivors=(\d+) found=(\d+) fpcoll=(\d+) steps=([\d.e+]+) maxlimbs=(\d+)',s)
    assert m, (f,s)
    lo,hi,h=map(int,m.group(1,2,3)); assert h==H
    ranges.append((lo,hi))
    for i,k in enumerate(['dips','survivors','found','fpcoll']): tot[k]+=int(m.group(4+i))
    steps+=float(m.group(8)); ml=max(ml,int(m.group(9)))
ranges.sort(); assert ranges[0][0]==1 and ranges[-1][1]==X0+1
assert all(a[1]==b[0] for a,b in zip(ranges,ranges[1:])), 'gap in coverage'
n=X0-4
assert tot['dips']+tot['survivors']+tot['found']==n, (tot,n)
out=f"COVERAGE [1,{X0}] contiguous in {len(ranges)} chunks; H={H} (periods <= {2*H}); candidates (excl. 1,2,4,44)={n}; {tot}; steps={steps:.4e}; maxlimbs={ml}"
print(out); open(D+'/summary.txt','w').write(out+'\n')
PY
echo "found lines:"; cat "$D"/found.txt
