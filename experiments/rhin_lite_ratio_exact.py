import sys
from fractions import Fraction
sys.set_int_max_str_digits(2000000)
from rhin_lite_det_check import rational_parts
for t in (1,2):
    cN,R1,R2 = rational_parts(t)
    print(f"t={t}: R1/R2 exact =", R1/R2)
    print(f"t={t}: R1/R2 == 705/500 ?", R1/R2 == Fraction(705,500), " float", float(R1/R2))
