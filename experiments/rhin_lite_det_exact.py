import sys, math
from fractions import Fraction
sys.set_int_max_str_digits(4000000)
from rhin_lite_det_check import rational_parts

d = {}
for t in (1,2):
    d[t] = rational_parts(t)   # (cN, R1, R2)
c1,R1a,R2a = d[1]
c2,R1b,R2b = d[2]
# t0=0 form determinant reduced factor: det(rows (1,0,0),(c1,R1a,R2a),(c2,R1b,R2b))
det0 = R1a*R2b - R2a*R1b
print("t0=0 reduced det = R1(1)R2(2)-R2(1)R1(2):", "NONZERO" if det0!=0 else "ZERO")
# magnitude via logs
def l10(fr):
    fr=abs(fr); return (math.log(fr.numerator)-math.log(fr.denominator))/math.log(10)
print("  log10|det0| =", l10(det0))
# ratios
r1=R1a/R2a; r2=R1b/R2b
print("R1/R2 equal across t=1,2 exactly?", r1==r2)
diff=r1-r2
print("  log10|ratio diff| =", l10(diff))
target = math.log(1.5)/math.log(4/3)
print("  ratio(t=1) approx", float(r1), " log(3/2)/log(4/3)=", target)
