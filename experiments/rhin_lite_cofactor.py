import sys, math
from fractions import Fraction
sys.set_int_max_str_digits(4000000)
from rhin_lite_det_check import rational_parts
L32 = None  # use mpmath-free: represent I = R + c*theta with theta as Fraction approx? need real.
# Use Python float logs are too low precision. Use Fraction high-precision log via mpmath-free series? 
# Instead: compute magnitudes with math.log on exact Fractions (bignum-aware).
def l10(fr):
    if fr==0: return None
    fr=abs(fr); return (math.log(fr.numerator)-math.log(fr.denominator))/math.log(10)
# theta as high-precision Fraction: use Python's Fraction from decimal of log via integer ratio not needed;
# We only need MAGNITUDE of cofactor terms. Use I ~ R (since det(c,I1,I2)=det(c,R1,R2)), and the cofactor
# expansion along column0 differs between R and I, but for a magnitude sanity we test the R-cofactor terms:
d={}
for t in (1,2):
    d[t]=rational_parts(t)
# t0=0 rows: t=0 (c=1,R1=0,R2=0), t=1, t=2
c0,R10,R20 = 1, Fraction(0), Fraction(0)
c1,R11,R21 = d[1]
c2,R12,R22 = d[2]
def minor(a,b):  # (R1(a)R2(b)-R2(a)R1(b))
    return a[1]*b[1+1]... 
