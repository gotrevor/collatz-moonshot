#!/usr/bin/env -S uv run --quiet python3
"""Search exact finite transfer certificates in the barriered inverse tree.

An odd inverse macro-child of ``x`` at cost ``j`` is

    y = (2^j x - 1) / 3,

whose forward block is ``y -> 2^j x -> ... -> x``.  For ``j >= 2`` and
``x >= 2`` the child is larger than its parent, so the whole block stays above
the parent's floor and has peak at most ``2^j x``.  We retain only children
that are units modulo 3, because those can branch again.

Integrality and unit status depend only on ``x mod 9``.  This script derives
the ordered cost stream in every unit residue class rather than assuming a
table, takes the coordinatewise worst stream, and searches for a finite exact
weighted certificate

    sum(q^cost) > 1.

Such a certificate is the Collatz-specific input to a standard variable-length
tree-growth lemma.  With ``q = 5/6``, it gives growth on the scale
``q^-p = (6/5)^p`` inside the ceiling ``2^p x``.  The script also computes
prefix-free finite-budget leaf counts and exhaustively checks the arithmetic,
forward blocks, and cross-parent non-collision on a configurable finite range.

The second part implements the harder shrinking ``j = 1`` transfer.  It uses
residues modulo ``3^k`` and rational lower bounds for ``x/d``; loss of the next
ternary digit is handled adversarially.  A frozen 36-state integer potential
(modulo 27, height floors ``1`` and ``7/4``) is checked in exact arithmetic at
``q = 7/9``.  The optional nonlinear search explains where that certificate
came from, but is explicitly diagnostic rather than part of the exact check.

The stronger correlated certificates keep a correlation discarded by that
first search.  All children of one source share its single unknown next ternary
digit; their lift choices cannot be minimized independently.  Tracking the
three joint alternatives modulo 81 yields the Lean-checked exponent ``2/3``
certificate.  Modulo 243 with five height floors yields an exactly checked
candidate at exponent ``3/4``.

At ternary depth 8 the same five height floors cross exponent ``4/5``.  A
close rational underweight and the generated 21,870-state integer potential
pass 65,610 exact inequalities; this larger candidate is intended to be frozen
by the next Lean formalization rather than duplicated below.

Examples:
    uv run --quiet python3 experiments/barrier_transfer.py
    uv run --quiet python3 experiments/barrier_transfer.py --verify-up-to 100000
    uv run --quiet python3 experiments/barrier_transfer.py --correlated-net-search-only
    uv run --quiet python3 experiments/barrier_transfer.py --correlated-three-quarters-certificate
    uv run --quiet python3 experiments/barrier_transfer.py --correlated-four-fifths-certificate
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from fractions import Fraction
from math import exp, log, log2


UNIT_RESIDUES_MOD_9 = (1, 2, 4, 5, 7, 8)

# Exact residue-plus-height certificate, in state order
#   height in (1, 7/4), then residue in UNITS_MOD_27.
# These small integer potentials were found numerically and are verified below
# using Fraction arithmetic.  They are data, not floating-point evidence.
UNITS_MOD_27 = tuple(value for value in range(27) if value % 3 != 0)
HEIGHT_CERTIFICATE_BINS = (Fraction(1), Fraction(7, 4))
HEIGHT_CERTIFICATE_Q = Fraction(7, 9)
HEIGHT_CERTIFICATE_WEIGHTS = (
    1278, 800, 1028, 972, 820, 588, 1117, 1045, 804,
    1055, 756, 638, 1254, 831, 965, 975, 758, 590,
    1356, 1648, 1028, 972, 820, 1325, 1249, 1619, 1069,
    1055, 756, 1245, 1254, 1441, 1344, 975, 758, 1036,
)

# A stronger certificate after refunding the factor 3 between successive odd
# endpoints.  For target exponent 1/2,
#
#   (5/3) * (7/10)^j < sqrt(3) * (1/sqrt(2))^j = (3/2^j)^(1/2).
#
# The two strict comparisons reduce to 25 < 27 and 98 < 100.  Thus this fully
# rational transfer is a safe under-approximation of the net-height operator.
NET_HALF_FACTOR = Fraction(5, 3)
NET_HALF_Q = Fraction(7, 10)
NET_HALF_WEIGHTS = (
    140, 76, 108, 99, 78, 48, 109, 114, 68,
    111, 69, 55, 132, 77, 99, 92, 65, 45,
    159, 200, 108, 99, 78, 154, 141, 188, 110,
    111, 69, 141, 132, 155, 163, 92, 65, 97,
)

# A stronger exact candidate which keeps the next ternary digit correlated
# across all children of one parent.  States are unit residues modulo 81 times
# the five height floors below.  The rational edge underweight targets endpoint
# exponent 2/3:
#
#   (52/25) * (629/1000)^j < (3 / 2^j)^(2/3),
#
# because (52/25)^3 < 9 and 4*(629/1000)^3 < 1.  The integer potential was
# found numerically and is checked exactly by `verify_exact_correlated_two_thirds_certificate`.
CORRELATED_TWO_THIRDS_FACTOR = Fraction(52, 25)
CORRELATED_TWO_THIRDS_Q = Fraction(629, 1000)
CORRELATED_TWO_THIRDS_DEPTH = 4
CORRELATED_TWO_THIRDS_HEIGHT_BINS = (
    Fraction(1), Fraction(7, 4), Fraction(5, 2), Fraction(3), Fraction(4)
)
CORRELATED_TWO_THIRDS_WEIGHTS = (
    461753, 223157, 354780, 319087, 225411, 131094, 290624, 375318, 166953,
    358364, 208416, 114782, 432633, 170055, 249164, 284972, 171167, 112746,
    394347, 203733, 314233, 331345, 182484, 167449, 371464, 292251, 153316,
    340602, 200706, 141783, 453055, 229355, 314767, 272126, 179247, 107664,
    461235, 197653, 323900, 416101, 214239, 126244, 526780, 370729, 169907,
    290117, 266215, 134756, 401835, 296972, 228221, 252754, 158983, 100000,
    523834, 734142, 354780, 319087, 225411, 564071, 385367, 720355, 364635,
    358364, 208416, 500446, 432633, 462104, 596690, 284972, 171167, 265436,
    471039, 733322, 314233, 331345, 182484, 514959, 562831, 687920, 270357,
    340602, 200706, 396148, 453055, 837558, 589394, 272126, 179247, 270131,
    461235, 626973, 323900, 423235, 214239, 499604, 526780, 638945, 472134,
    290117, 266215, 362855, 401835, 590676, 464628, 252754, 158983, 243754,
    541497, 734142, 354780, 319087, 225411, 564071, 507293, 720355, 668875,
    358364, 208416, 500446, 432633, 462104, 684050, 284972, 171167, 265436,
    569735, 733322, 314233, 331345, 182484, 514959, 661528, 687920, 420981,
    340602, 200706, 396148, 453055, 837558, 589394, 272126, 179247, 270131,
    461235, 626973, 323900, 423235, 214239, 499604, 526780, 638945, 472134,
    290117, 266215, 362855, 401835, 590676, 586555, 252754, 158983, 243754,
    541497, 832839, 354780, 319087, 225411, 564071, 507293, 720355, 668875,
    358364, 208416, 937060, 432633, 612728, 684050, 284972, 171167, 579716,
    569735, 733322, 314233, 331345, 182484, 514959, 661528, 687920, 420981,
    340602, 200706, 948653, 453055, 837558, 589394, 272126, 179247, 750619,
    461235, 748900, 323900, 423235, 214239, 499604, 526780, 638945, 472134,
    290117, 266215, 738702, 401835, 894916, 586555, 252754, 158983, 429829,
    541497, 860930, 354780, 319087, 225411, 564071, 507293, 720355, 668875,
    358364, 208416, 937060, 432633, 806569, 684050, 284972, 171167, 579716,
    569735, 733322, 314233, 331345, 182484, 514959, 672870, 687920, 420981,
    340602, 200706, 948653, 453055, 837558, 589394, 272126, 179247, 750619,
    461235, 905810, 323900, 423235, 214239, 499604, 526780, 638945, 472134,
    290117, 266215, 738702, 401835, 1051827, 743466, 252754, 158983, 429829,
)

# Candidate rational underweight for endpoint exponent 3/4.  Positivity plus
# these two fourth-power comparisons imply
#
#   (2279/1000) * (2973/5000)^j < (3 / 2^j)^(3/4).
#
# The table below was generated from the nonlinear eigenvector and is checked
# by an exact common-denominator integer calculation.
CORRELATED_THREE_QUARTERS_FACTOR = Fraction(2279, 1000)
CORRELATED_THREE_QUARTERS_Q = Fraction(2973, 5000)
CORRELATED_THREE_QUARTERS_DEPTH = 5
CORRELATED_THREE_QUARTERS_HEIGHT_BINS = (
    Fraction(1), Fraction(7, 4), Fraction(3), Fraction(6), Fraction(12)
)
CORRELATED_THREE_QUARTERS_WEIGHTS = (
  5620241, 2507527, 3120869, 3594000, 2733565, 1519851, 3988049, 4200861, 1575034,
  3728847, 2556089, 1151736, 3957839, 1982248, 2633593, 3244528, 1837253, 1166946,
  4669019, 2209771, 4393798, 4265757, 1936993, 1632640, 4346694, 2774639, 1611259,
  3417814, 3231598, 1592286, 4786053, 2537186, 3552608, 3089897, 1962573, 1116127,
  5230181, 2318676, 3621694, 3629770, 2437381, 2312784, 5989602, 4019530, 1924277,
  3191331, 2745779, 1628117, 4756914, 3085015, 2172146, 3129179, 1681803, 1151424,
  4664483, 2835167, 4250585, 4566439, 2677912, 1688767, 2747974, 4373230, 1993314,
  3093145, 2783384, 1099490, 5141104, 1635142, 2968143, 3202303, 1877105, 1045486,
  6084338, 2333835, 3899557, 3972764, 1855553, 1873211, 4105507, 3782885, 1537297,
  3858188, 3089640, 1634936, 4862954, 2722793, 3799060, 3005190, 1929196, 1092430,
  4488548, 2612552, 3356852, 4067300, 2554673, 1921508, 6480411, 4215861, 1972128,
  3109866, 2802573, 1449267, 4774924, 2921251, 2790263, 2828461, 1936469, 1000000,
  5620973, 2655402, 3928948, 2637009, 2491042, 1655000, 3499971, 3885783, 1614337,
  4182946, 2840173, 1103312, 4684206, 1602291, 2981782, 2957116, 2076895, 1147100,
  3850026, 1995984, 3797237, 4369645, 1849126, 2188851, 4612354, 5050888, 1449099,
  3503410, 2381301, 1771183, 4507000, 2125448, 2879756, 3156921, 1758301, 1234922,
  4910136, 2780278, 3797265, 4531573, 2083128, 1777770, 5495385, 3562362, 2274287,
  3120674, 3150372, 1238628, 4840945, 3480021, 3097188, 3110857, 1849716, 1099841,
  6488712, 9452282, 4217166, 5196165, 2749641, 5248892, 6044400, 8178893, 4579202,
  4597318, 2556089, 6389398, 5054137, 6707481, 7065021, 3244528, 1837253, 2648953,
  6271185, 7549045, 4393798, 4298839, 1936993, 5645621, 6840397, 6656830, 3333751,
  4296456, 3231598, 4429260, 5456657, 10899463, 7090247, 3089897, 1962573, 3316769,
  5230181, 7852505, 3716400, 4713376, 2437381, 7389619, 7174162, 8030982, 4912969,
  3257640, 2745779, 4692785, 4756914, 7311024, 4666395, 3256759, 1681803, 2709848,
  5748089, 9453559, 4465864, 5434910, 2677912, 6607792, 4434930, 8049557, 4267046,
  4189442, 2783384, 5974900, 5196597, 5886565, 6535121, 3300661, 1877105, 2715037,
  7034891, 8796398, 3899557, 4776612, 1855553, 6091044, 6104557, 7878291, 2694737,
  4099194, 3889646, 5014842, 4973287, 10073757, 6760057, 3492928, 1929196, 3236295,
  5367190, 6475113, 3356852, 4617860, 2738171, 6386366, 7348882, 8000776, 5188386,
  3109866, 3681216, 3653281, 5262662, 7757623, 8494599, 2828461, 1936469, 2437126,
  5892046, 7844869, 4768192, 4004878, 2978780, 7148759, 7679850, 7580270, 3574585,
  4503719, 2840173, 4843258, 5309318, 4621823, 7354910, 2957116, 2076895, 3352408,
  5202060, 8258099, 4675879, 4681104, 1849126, 6386316, 7621213, 8646801, 2749987,
  3503410, 2989859, 4991917, 5385642, 9242846, 5991191, 3156921, 1758301, 3824930,
  5248358, 10232784, 3925050, 5298305, 2083128, 6558398, 6681406, 8142052, 5852709,
  3120674, 3150372, 5208974, 5231849, 6905165, 6362068, 3110857, 1849716, 2585457,
  6894037, 10912879, 5037445, 6541619, 2749641, 7092648, 8738926, 8364417, 8773118,
  4624354, 2556089, 11369212, 5874416, 10165798, 7996720, 3244528, 1837253, 7701370,
  7731782, 9026748, 4393798, 4298839, 1936993, 5645621, 7766330, 8500586, 7362220,
  4605064, 3231598, 11882041, 5456657, 12360060, 7146050, 3089897, 1962573, 8725882,
  5230181, 10547033, 3716400, 6191079, 2437381, 7389619, 7229799, 8851261, 6390672,
  3257640, 2745779, 14286354, 4756914, 11504940, 6940250, 3256759, 1681803, 5606738,
  7225792, 9909450, 4465864, 5434910, 2677912, 8019248, 6735416, 9177388, 9490808,
  5009721, 2783384, 11924483, 5196597, 12916299, 8357533, 3300661, 1877105, 6011785,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 7926969, 8929589, 4288083,
  4099194, 3889646, 12369589, 4973287, 12065953, 7402008, 3492928, 1929196, 8262685,
  5478709, 8748968, 3356852, 4617860, 2738171, 7864070, 7872694, 8000776, 5188386,
  3109866, 3928034, 7848114, 5477226, 12818016, 10093242, 2828461, 1936469, 4624966,
  5892046, 9667280, 4768192, 5028354, 3139192, 7510907, 9140448, 9057973, 6936591,
  4503719, 2840173, 10076079, 5309318, 7458950, 8815507, 2957116, 2076895, 7176377,
  7045816, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 5429408,
  3503410, 3810139, 10990861, 5551060, 11237500, 7468895, 3156921, 1758301, 9843131,
  5248358, 11831427, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 10699860, 5231849, 10267174, 9056595, 3110857, 1849716, 4532044,
  6894037, 11594601, 5322918, 6541619, 2749641, 8472195, 11001713, 8364417, 10326103,
  4624354, 2556089, 12448831, 5874416, 14697460, 7996720, 3244528, 1837253, 14754711,
  7777252, 9214286, 4393798, 4298839, 1936993, 5645621, 7766330, 9880133, 7710202,
  4605064, 3231598, 13448986, 5456657, 13240765, 7146050, 3089897, 1962573, 8725882,
  5230181, 13003470, 3716400, 6606180, 2437381, 7389619, 7229799, 9212171, 6742852,
  3257640, 2745779, 16974956, 4756914, 13062211, 10041083, 3256759, 1681803, 12381828,
  7744811, 9909450, 4465864, 5434910, 2677912, 8019248, 8456701, 9177388, 11496029,
  5279502, 2783384, 12018348, 5196597, 15372735, 10842739, 3300661, 1877105, 11666016,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 10412175, 8929589, 6435760,
  4099194, 3889646, 14826025, 4973287, 12159456, 7402008, 3492928, 1929196, 10747890,
  5478709, 11849802, 3356852, 4617860, 2738171, 7992089, 7872694, 8000776, 5188386,
  3109866, 3928034, 11672289, 5477226, 14986603, 10713364, 2828461, 1936469, 9131220,
  5892046, 12152486, 4768192, 6407902, 3139192, 7510907, 9140448, 9336133, 10001529,
  4503719, 2840173, 12561285, 5309318, 11327913, 9227373, 2957116, 2076895, 15961726,
  8425364, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 9961069,
  3503410, 3810139, 14055799, 5551060, 13511174, 7699875, 3156921, 1758301, 10367269,
  5248358, 12738738, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 15231525, 5231849, 13332111, 11205314, 3110857, 1849716, 7211738,
  6894037, 11594601, 5322918, 6541619, 2749641, 8952266, 11001713, 8364417, 10326103,
  4624354, 2556089, 12448831, 5874416, 18503081, 7996720, 3244528, 1837253, 17366526,
  7777252, 9214286, 4393798, 4298839, 1936993, 5645621, 7766330, 9880133, 7710202,
  4605064, 3231598, 13448986, 5456657, 13240765, 7146050, 3089897, 1962573, 8725882,
  5230181, 13079938, 3716400, 6606180, 2437381, 7389619, 7229799, 9212171, 6742852,
  3257640, 2745779, 18017896, 4756914, 13062211, 12361211, 3256759, 1681803, 12967068,
  7744811, 9909450, 4465864, 5434910, 2677912, 8019248, 10776828, 9177388, 11496029,
  5279502, 2783384, 12018348, 5196597, 15372735, 11495168, 3300661, 1877105, 16820637,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 11110292, 8929589, 9330623,
  4099194, 3889646, 15518704, 4973287, 12159456, 7402008, 3492928, 1929196, 11340183,
  5478709, 14169929, 3356852, 4617860, 2738171, 7992089, 7872694, 8000776, 5188386,
  3109866, 3928034, 16887280, 5477226, 14986603, 10713364, 2828461, 1936469, 16752581,
  5892046, 13025379, 4768192, 6407902, 3139192, 7510907, 9140448, 9336133, 14181155,
  4503719, 2840173, 12949752, 5309318, 14222775, 9227373, 2957116, 2076895, 19334101,
  8879081, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 14092311,
  3503410, 3810139, 18235425, 5551060, 13511174, 7699875, 3156921, 1758301, 10367269,
  5248358, 12738738, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 18845234, 5231849, 17511738, 11205314, 3110857, 1849716, 10823707,

)

# Exact exponent-4/5 candidate found at ternary depth 8.  The two elementary
# comparisons imply
#
#   (2408224/1000000) * (574349/1000000)^j < (3 / 2^j)^(4/5).
#
# Its potential is generated on demand: 21,870 states and 65,610 exact
# shared-lift inequalities, with minimum ratio 1.001017912682.
CORRELATED_FOUR_FIFTHS_FACTOR = Fraction(2_408_224, 1_000_000)
CORRELATED_FOUR_FIFTHS_Q = Fraction(574_349, 1_000_000)
CORRELATED_FOUR_FIFTHS_DEPTH = 8
CORRELATED_FOUR_FIFTHS_HEIGHT_BINS = CORRELATED_THREE_QUARTERS_HEIGHT_BINS


def step(n: int) -> int:
    return n // 2 if n % 2 == 0 else 3 * n + 1


def odd_macro_child(x: int, cost: int) -> int | None:
    """Return the odd macro-child at ``cost``, or ``None`` if nonintegral."""
    numerator = 2**cost * x - 1
    return numerator // 3 if numerator % 3 == 0 else None


def is_reusable_growing_cost(residue: int, cost: int) -> bool:
    """Test a cost using only a representative of ``x mod 9``."""
    if cost < 2:
        return False
    child = odd_macro_child(residue, cost)
    return child is not None and child % 2 == 1 and child % 3 != 0


def first_reusable_costs(residue: int, count: int) -> tuple[int, ...]:
    costs: list[int] = []
    cost = 2
    while len(costs) < count:
        if is_reusable_growing_cost(residue, cost):
            costs.append(cost)
        cost += 1
    return tuple(costs)


def coordinatewise_envelope(rows: dict[int, tuple[int, ...]]) -> tuple[int, ...]:
    width = len(next(iter(rows.values())))
    assert all(len(row) == width for row in rows.values())
    return tuple(max(row[index] for row in rows.values()) for index in range(width))


def expected_envelope(index: int) -> int:
    """The periodic worst stream: 5, 7, 11, 13, 17, 19, ..."""
    block, offset = divmod(index, 2)
    return 6 * block + (5 if offset == 0 else 7)


def minimum_supercritical_prefix(
    costs: tuple[int, ...], q: Fraction
) -> tuple[tuple[int, ...], Fraction]:
    weight = Fraction(0)
    for index, cost in enumerate(costs):
        weight += q**cost
        if weight > 1:
            return costs[: index + 1], weight
    raise ValueError("cost prefix is too short to produce a supercritical certificate")


def critical_exponent() -> tuple[float, float]:
    """Solve q^5 + q^6 + q^7 = 1 for the infinite envelope."""
    low, high = 0.0, 1.0
    for _ in range(100):
        q = (low + high) / 2
        if q**5 + q**6 + q**7 < 1:
            low = q
        else:
            high = q
    q = (low + high) / 2
    return q, -log2(q)


def prefix_free_leaf_counts(costs: tuple[int, ...], max_budget: int) -> list[int]:
    """Best leaf count from recursively using every affordable child.

    A node may remain a leaf, or be replaced by the disjoint child subtrees
    whose certified costs fit in the remaining budget.  Because every term is
    positive, taking every affordable child maximizes the recurrence.
    """
    counts = [1]
    for budget in range(1, max_budget + 1):
        expanded = sum(counts[budget - cost] for cost in costs if cost <= budget)
        counts.append(max(1, expanded))
    return counts


def verify_forward_block(x: int, child: int, cost: int) -> None:
    value = child
    values = [value]
    for _ in range(cost + 1):
        value = step(value)
        values.append(value)
    assert value == x
    assert min(values) >= x
    assert max(values) == 2**cost * x


def verify_arithmetic(rows: dict[int, tuple[int, ...]], limit: int) -> int:
    owners: dict[int, int] = {}
    checked = 0
    width = len(next(iter(rows.values())))
    for x in range(2, limit + 1):
        if x % 3 == 0:
            continue
        costs = first_reusable_costs(x % 9, width)
        assert costs == rows[x % 9]
        children: list[int] = []
        for cost in costs:
            child = odd_macro_child(x, cost)
            assert child is not None
            assert child > x
            assert child % 2 == 1
            assert child % 3 != 0
            assert 3 * child + 1 == 2**cost * x
            source_lift_digit = (x // 3**CORRELATED_TWO_THIRDS_DEPTH) % 3
            assert child % 3**CORRELATED_TWO_THIRDS_DEPTH == (
                child_residue_for_shared_lift(
                    x % 3**CORRELATED_TWO_THIRDS_DEPTH,
                    cost,
                    CORRELATED_TWO_THIRDS_DEPTH,
                    source_lift_digit,
                )
            )
            verify_forward_block(x, child, cost)
            children.append(child)
            checked += 1
        shrinking_child = odd_macro_child(x, 1)
        if shrinking_child is not None and shrinking_child % 3 != 0:
            source_lift_digit = (x // 3**CORRELATED_TWO_THIRDS_DEPTH) % 3
            assert shrinking_child % 3**CORRELATED_TWO_THIRDS_DEPTH == (
                child_residue_for_shared_lift(
                    x % 3**CORRELATED_TWO_THIRDS_DEPTH,
                    1,
                    CORRELATED_TWO_THIRDS_DEPTH,
                    source_lift_digit,
                )
            )
        assert len(set(children)) == width

        # The collision theorem used by iteration assumes distinct odd parents.
        if x % 2 == 1:
            for child in children:
                previous = owners.setdefault(child, x)
                assert previous == x
    return checked


def shrinking_child_class(residue: int) -> str:
    child = odd_macro_child(residue, 1)
    if child is None:
        return "nonintegral"
    return "unit" if child % 3 != 0 else "multiple-of-3"


def parse_fraction(value: str) -> Fraction:
    return Fraction(value.strip())


def child_residue_possibilities(residue: int, cost: int, ternary_depth: int) -> tuple[int, ...]:
    """Possible child residues after division loses one known ternary digit.

    If ``x`` is known modulo ``3^k``, then its odd macro-child is determined
    modulo ``3^(k-1)``.  The next base-3 digit is genuinely unknown, so a
    universal certificate must survive all three lifts modulo ``3^k``.
    """
    modulus = 3**ternary_depth
    lower_modulus = modulus // 3
    numerator = 2**cost * residue - 1
    assert numerator % 3 == 0
    base = (numerator // 3) % lower_modulus
    possibilities = tuple(base + digit * lower_modulus for digit in range(3))
    assert all(value % 3 != 0 for value in possibilities)
    return possibilities


def child_residue_for_shared_lift(
    residue: int, cost: int, ternary_depth: int, source_lift_digit: int
) -> int:
    """Child residue for one shared next digit of the source.

    Write ``x = residue + t*3^k (mod 3^(k+1))`` and
    ``Q = (2^cost*residue - 1)/3``.  Division by three gives

        child = Q + 2^cost*t*3^(k-1) (mod 3^k).

    Thus the fixed high digit already present in ``Q`` must be retained, while
    the same ``t`` controls every child of ``x``; only the parity of ``cost``
    changes its multiplier modulo three.  Treating these lift choices
    independently throws away this genuine correlation.
    """
    if source_lift_digit not in range(3):
        raise ValueError("a ternary lift digit must be 0, 1, or 2")
    modulus = 3**ternary_depth
    lower_modulus = modulus // 3
    numerator = 2**cost * residue - 1
    assert numerator % 3 == 0
    quotient = numerator // 3
    base = quotient % lower_modulus
    base_digit = (quotient // lower_modulus) % 3
    child_digit = (base_digit + pow(2, cost, 3) * source_lift_digit) % 3
    child_residue = base + child_digit * lower_modulus
    assert child_residue in child_residue_possibilities(residue, cost, ternary_depth)
    return child_residue


def next_height_lower_bound(height: Fraction, cost: int) -> Fraction:
    """Uniform lower bound for y/d, using d >= 2.

    From x/d >= h and y = (2^j x - 1)/3,

        y/d >= (2^j h - 1/2)/3.
    """
    return (2**cost * height - Fraction(1, 2)) / 3


def build_height_transitions(
    ternary_depth: int,
    heights: tuple[Fraction, ...],
    growing_children: int,
    include_shrinking: bool,
) -> tuple[tuple[tuple[int, tuple[int, ...]], ...], ...]:
    if ternary_depth < 2:
        raise ValueError("the height-state search needs ternary depth at least 2")
    modulus = 3**ternary_depth
    residues = tuple(value for value in range(modulus) if value % 3 != 0)
    state_index = {
        (residue, height_index): height_index * len(residues) + residue_index
        for height_index in range(len(heights))
        for residue_index, residue in enumerate(residues)
    }

    transitions: list[tuple[tuple[int, tuple[int, ...]], ...]] = []
    for height_index, height in enumerate(heights):
        for residue in residues:
            costs = list(first_reusable_costs(residue % 9, growing_children))
            if include_shrinking and shrinking_child_class(residue % 9) == "unit":
                if next_height_lower_bound(height, 1) >= 1:
                    costs.insert(0, 1)

            edges: list[tuple[int, tuple[int, ...]]] = []
            for cost in costs:
                child_height = next_height_lower_bound(height, cost)
                if child_height < 1:
                    continue
                child_height_index = bisect_right(heights, child_height) - 1
                child_height_index = min(child_height_index, len(heights) - 1)
                targets = tuple(
                    state_index[(child_residue, child_height_index)]
                    for child_residue in child_residue_possibilities(
                        residue, cost, ternary_depth
                    )
                )
                edges.append((cost, targets))
            assert edges
            transitions.append(tuple(edges))
    return tuple(transitions)


def build_correlated_height_transitions(
    ternary_depth: int,
    heights: tuple[Fraction, ...],
    growing_children: int,
    include_shrinking: bool,
) -> tuple[tuple[tuple[tuple[int, int], ...], ...], ...]:
    """Build the shared-lift operator.

    Each source state has three alternatives, one per possible next ternary
    digit.  An alternative contains all child edges together.  A universal
    certificate must expand for each alternative, but is allowed to use the
    correlation among its children.
    """
    if ternary_depth < 2:
        raise ValueError("the height-state search needs ternary depth at least 2")
    modulus = 3**ternary_depth
    residues = tuple(value for value in range(modulus) if value % 3 != 0)
    state_index = {
        (residue, height_index): height_index * len(residues) + residue_index
        for height_index in range(len(heights))
        for residue_index, residue in enumerate(residues)
    }

    transitions: list[tuple[tuple[tuple[int, int], ...], ...]] = []
    for height_index, height in enumerate(heights):
        for residue in residues:
            costs = list(first_reusable_costs(residue % 9, growing_children))
            if include_shrinking and shrinking_child_class(residue % 9) == "unit":
                if next_height_lower_bound(height, 1) >= 1:
                    costs.insert(0, 1)

            alternatives: list[tuple[tuple[int, int], ...]] = []
            for source_lift_digit in range(3):
                edges: list[tuple[int, int]] = []
                for cost in costs:
                    child_height = next_height_lower_bound(height, cost)
                    if child_height < 1:
                        continue
                    child_height_index = bisect_right(heights, child_height) - 1
                    child_height_index = min(child_height_index, len(heights) - 1)
                    child_residue = child_residue_for_shared_lift(
                        residue, cost, ternary_depth, source_lift_digit
                    )
                    edges.append((cost, state_index[(child_residue, child_height_index)]))
                assert edges
                alternatives.append(tuple(edges))
            transitions.append(tuple(alternatives))
    return tuple(transitions)


def nonlinear_radius(
    transitions: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...],
    q: float,
    iterations: int,
    edge_factor: float = 1.0,
) -> tuple[float, float, int]:
    """Collatz bounds for the monotone min-over-lifts transfer operator."""
    weights = [1.0] * len(transitions)
    lower = upper = 0.0
    for iteration in range(1, iterations + 1):
        image = [
            edge_factor
            * sum(q**cost * min(weights[target] for target in targets)
                  for cost, targets in edges)
            for edges in transitions
        ]
        ratios = [new / old for new, old in zip(image, weights)]
        lower, upper = min(ratios), max(ratios)

        # Normalize in log space, with damping for the nonsmooth min operator.
        scale = exp(sum(log(value) for value in image) / len(image))
        normalized = [value / scale for value in image]
        updated = [(old * new) ** 0.5 for old, new in zip(weights, normalized)]
        delta = max(abs(log(new / old)) for new, old in zip(updated, weights))
        weights = updated
        if delta < 1e-13 and upper - lower < 1e-11:
            return lower, upper, iteration
    return lower, upper, iterations


def correlated_nonlinear_eigenvector(
    transitions: tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
    q: float,
    iterations: int,
    edge_factor: float = 1.0,
) -> tuple[float, float, int, tuple[float, ...]]:
    """Collatz bounds and a numerical potential for the correlated operator."""
    weights = [1.0] * len(transitions)
    lower = upper = 0.0
    for iteration in range(1, iterations + 1):
        image = [
            edge_factor
            * min(
                sum(q**cost * weights[target] for cost, target in edges)
                for edges in alternatives
            )
            for alternatives in transitions
        ]
        ratios = [new / old for new, old in zip(image, weights)]
        lower, upper = min(ratios), max(ratios)

        scale = exp(sum(log(value) for value in image) / len(image))
        normalized = [value / scale for value in image]
        updated = [(old * new) ** 0.5 for old, new in zip(weights, normalized)]
        delta = max(abs(log(new / old)) for new, old in zip(updated, weights))
        weights = updated
        if delta < 1e-13 and upper - lower < 1e-11:
            return lower, upper, iteration, tuple(weights)
    return lower, upper, iterations, tuple(weights)


def correlated_nonlinear_radius(
    transitions: tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
    q: float,
    iterations: int,
    edge_factor: float = 1.0,
) -> tuple[float, float, int]:
    """Collatz bounds for the min-of-correlated-sums transfer operator."""
    lower, upper, used_iterations, _ = correlated_nonlinear_eigenvector(
        transitions, q, iterations, edge_factor
    )
    return lower, upper, used_iterations


def exact_integer_correlated_certificate(
    transitions: tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
    factor: Fraction,
    q: Fraction,
    iterations: int,
    minimum_weight: int = 1_000_000,
) -> tuple[tuple[int, ...], float, int, int]:
    """Round a numerical potential and check every inequality exactly.

    All edges have a bounded integral cost.  Multiplying by the common
    denominator ``factor.denominator * q.denominator^max_cost`` turns every
    certificate inequality into one integer comparison, avoiding slow repeated
    normalization of very large ``Fraction`` values.
    """
    if minimum_weight < 1:
        raise ValueError("minimum_weight must be positive")
    _, _, _, numerical = correlated_nonlinear_eigenvector(
        transitions, float(q), iterations, float(factor)
    )
    floor = min(numerical)
    weights = tuple(round(minimum_weight * value / floor) for value in numerical)
    ratio, margin, checked = verify_integer_correlated_certificate(
        transitions, factor, q, weights
    )
    return weights, ratio, margin, checked


def verify_integer_correlated_certificate(
    transitions: tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
    factor: Fraction,
    q: Fraction,
    weights: tuple[int, ...],
) -> tuple[float, int, int]:
    """Check a supplied correlated potential by common-denominator integers."""
    if len(weights) != len(transitions) or min(weights) < 1:
        raise ValueError("the potential must have one positive weight per state")
    max_cost = max(
        cost
        for alternatives in transitions
        for edges in alternatives
        for cost, _ in edges
    )
    common_q_denominator = q.denominator**max_cost
    source_scale = factor.denominator * common_q_denominator
    minimum_margin: int | None = None
    minimum_ratio = float("inf")
    checked = 0
    for source_weight, alternatives in zip(weights, transitions):
        for edges in alternatives:
            image = factor.numerator * sum(
                q.numerator**cost
                * q.denominator ** (max_cost - cost)
                * weights[target]
                for cost, target in edges
            )
            source = source_scale * source_weight
            margin = image - source
            if margin <= 0:
                raise ValueError(
                    f"rounded potential is not a certificate: margin={margin}"
                )
            minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
            minimum_ratio = min(minimum_ratio, image / source)
            checked += 1
    assert minimum_margin is not None
    return minimum_ratio, minimum_margin, checked


def search_height_critical_q(
    transitions: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...],
    iterations: int,
) -> tuple[float, float, float, int]:
    low, high = 0.5, 0.999
    last_iterations = 0
    for _ in range(48):
        q = (low + high) / 2
        lower, upper, last_iterations = nonlinear_radius(transitions, q, iterations)
        estimate = (lower * upper) ** 0.5
        if estimate < 1:
            low = q
        else:
            high = q
    q = (low + high) / 2
    lower, upper, last_iterations = nonlinear_radius(transitions, q, iterations)
    return q, lower, upper, last_iterations


def verify_exact_height_certificate() -> tuple[Fraction, Fraction]:
    """Check all 36 weighted transfer inequalities in exact arithmetic."""
    transitions = build_height_transitions(
        ternary_depth=3,
        heights=HEIGHT_CERTIFICATE_BINS,
        growing_children=7,
        include_shrinking=True,
    )
    weights = HEIGHT_CERTIFICATE_WEIGHTS
    assert len(transitions) == len(weights) == 2 * len(UNITS_MOD_27)
    margins: list[Fraction] = []
    ratios: list[Fraction] = []
    for weight, edges in zip(weights, transitions):
        image = sum(
            HEIGHT_CERTIFICATE_Q**cost
            * min(weights[target] for target in targets)
            for cost, targets in edges
        )
        margins.append(image - weight)
        ratios.append(image / weight)
    assert min(margins) > 0
    assert min(ratios) > 1
    return min(margins), min(ratios)


def verify_exact_net_half_certificate() -> tuple[Fraction, Fraction]:
    """Check the rational net-height exponent-1/2 certificate exactly."""
    assert NET_HALF_FACTOR**2 < 3
    assert 2 * NET_HALF_Q**2 < 1
    transitions = build_height_transitions(
        ternary_depth=3,
        heights=HEIGHT_CERTIFICATE_BINS,
        growing_children=7,
        include_shrinking=True,
    )
    weights = NET_HALF_WEIGHTS
    assert len(transitions) == len(weights) == 2 * len(UNITS_MOD_27)
    margins: list[Fraction] = []
    ratios: list[Fraction] = []
    for weight, edges in zip(weights, transitions):
        image = NET_HALF_FACTOR * sum(
            NET_HALF_Q**cost * min(weights[target] for target in targets)
            for cost, targets in edges
        )
        margins.append(image - weight)
        ratios.append(image / weight)
    assert min(margins) > 0
    assert min(ratios) > 1
    return min(margins), min(ratios)


def verify_exact_correlated_two_thirds_certificate() -> tuple[Fraction, Fraction]:
    """Check the 270-state shared-lift exponent-2/3 certificate exactly."""
    assert CORRELATED_TWO_THIRDS_FACTOR**3 < 9
    assert 4 * CORRELATED_TWO_THIRDS_Q**3 < 1
    transitions = build_correlated_height_transitions(
        ternary_depth=CORRELATED_TWO_THIRDS_DEPTH,
        heights=CORRELATED_TWO_THIRDS_HEIGHT_BINS,
        growing_children=7,
        include_shrinking=True,
    )
    weights = CORRELATED_TWO_THIRDS_WEIGHTS
    assert len(transitions) == len(weights) == 270
    margins: list[Fraction] = []
    ratios: list[Fraction] = []
    for weight, alternatives in zip(weights, transitions):
        assert len(alternatives) == 3
        for edges in alternatives:
            image = CORRELATED_TWO_THIRDS_FACTOR * sum(
                CORRELATED_TWO_THIRDS_Q**cost * weights[target]
                for cost, target in edges
            )
            margins.append(image - weight)
            ratios.append(image / weight)
    assert len(margins) == 810
    assert min(margins) > 0
    assert min(ratios) > 1
    return min(margins), min(ratios)


def verify_exact_correlated_three_quarters_certificate() -> tuple[float, int, int]:
    """Check the frozen 810-state shared-lift exponent-3/4 certificate."""
    factor = CORRELATED_THREE_QUARTERS_FACTOR
    q = CORRELATED_THREE_QUARTERS_Q
    assert factor**4 < 27
    assert 8 * q**4 < 1
    transitions = build_correlated_height_transitions(
        ternary_depth=CORRELATED_THREE_QUARTERS_DEPTH,
        heights=CORRELATED_THREE_QUARTERS_HEIGHT_BINS,
        growing_children=7,
        include_shrinking=True,
    )
    assert len(transitions) == len(CORRELATED_THREE_QUARTERS_WEIGHTS) == 810
    ratio, margin, checked = verify_integer_correlated_certificate(
        transitions,
        factor,
        q,
        CORRELATED_THREE_QUARTERS_WEIGHTS,
    )
    assert checked == 2430
    return ratio, margin, checked


def search_net_critical_exponent(
    transitions: tuple[tuple[tuple[int, tuple[int, ...]], ...], ...],
    iterations: int,
) -> tuple[float, float, float, int]:
    """Numerically solve rho(3^a T_(2^-a)) = 1."""
    low, high = 0.0, 1.5
    last_iterations = 0
    for _ in range(42):
        exponent = (low + high) / 2
        q = 2.0 ** (-exponent)
        lower, upper, last_iterations = nonlinear_radius(
            transitions, q, iterations, edge_factor=3.0**exponent
        )
        estimate = (lower * upper) ** 0.5
        if estimate > 1:
            low = exponent
        else:
            high = exponent
    exponent = (low + high) / 2
    q = 2.0 ** (-exponent)
    lower, upper, last_iterations = nonlinear_radius(
        transitions, q, iterations, edge_factor=3.0**exponent
    )
    return exponent, lower, upper, last_iterations


def search_correlated_net_critical_exponent(
    transitions: tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
    iterations: int,
) -> tuple[float, float, float, int]:
    """Numerically solve the shared-lift endpoint-height critical exponent."""
    low, high = 0.0, 1.5
    last_iterations = 0
    for _ in range(42):
        exponent = (low + high) / 2
        q = 2.0 ** (-exponent)
        lower, upper, last_iterations = correlated_nonlinear_radius(
            transitions, q, iterations, edge_factor=3.0**exponent
        )
        estimate = (lower * upper) ** 0.5
        if estimate > 1:
            low = exponent
        else:
            high = exponent
    exponent = (low + high) / 2
    q = 2.0 ** (-exponent)
    lower, upper, last_iterations = correlated_nonlinear_radius(
        transitions, q, iterations, edge_factor=3.0**exponent
    )
    return exponent, lower, upper, last_iterations


def run_height_search(args: argparse.Namespace) -> None:
    heights = tuple(parse_fraction(value) for value in args.height_bins.split(",") if value)
    if (
        not heights
        or heights[0] != 1
        or any(a >= b for a, b in zip(heights, heights[1:]))
    ):
        raise ValueError("--height-bins must increase strictly and start at 1")

    print()
    print("height/residue transfer search (numerical candidate, not a proof)")
    print("  bins: " + ",".join(map(str, heights)))
    for include_shrinking in (False, True):
        transitions = build_height_transitions(
            args.ternary_depth, heights, args.height_children, include_shrinking
        )
        q, lower, upper, iterations = search_height_critical_q(
            transitions, args.height_iterations
        )
        label = "growing+j=1" if include_shrinking else "growing control"
        edge_count = sum(len(edges) for edges in transitions)
        print(
            f"  {label:15s}: states={len(transitions)}, edges={edge_count}, "
            f"q~{q:.12f}, exponent~{-log2(q):.12f}, "
            f"ratio=[{lower:.12f},{upper:.12f}], iterations={iterations}"
        )


def run_net_search(args: argparse.Namespace) -> None:
    heights = tuple(parse_fraction(value) for value in args.height_bins.split(",") if value)
    if not heights or heights[0] != 1 or any(a >= b for a, b in zip(heights, heights[1:])):
        raise ValueError("--height-bins must increase strictly and start at 1")

    print()
    print("net-height transfer search (numerical candidate, not a proof)")
    print("  edge scale: (3 / 2^j)^alpha; bins: " + ",".join(map(str, heights)))
    for include_shrinking in (False, True):
        transitions = build_height_transitions(
            args.ternary_depth, heights, args.height_children, include_shrinking
        )
        exponent, lower, upper, iterations = search_net_critical_exponent(
            transitions, args.height_iterations
        )
        label = "growing+j=1" if include_shrinking else "growing control"
        print(
            f"  {label:15s}: states={len(transitions)}, exponent~{exponent:.12f}, "
            f"ratio=[{lower:.12f},{upper:.12f}], iterations={iterations}"
        )


def correlated_search_configuration(
    args: argparse.Namespace,
) -> tuple[
    tuple[Fraction, ...],
    tuple[tuple[tuple[tuple[int, int], ...], ...], ...],
]:
    heights = tuple(
        parse_fraction(value)
        for value in args.correlated_height_bins.split(",")
        if value
    )
    if not heights or heights[0] != 1 or any(a >= b for a, b in zip(heights, heights[1:])):
        raise ValueError("--height-bins must increase strictly and start at 1")
    transitions = build_correlated_height_transitions(
        args.correlated_depth,
        heights,
        args.height_children,
        True,
    )
    return heights, transitions


def run_correlated_net_search(args: argparse.Namespace) -> None:
    heights, transitions = correlated_search_configuration(args)
    exponent, lower, upper, iterations = search_correlated_net_critical_exponent(
        transitions, args.height_iterations
    )
    print()
    print("shared-lift net-height transfer search (numerical candidate)")
    print(
        f"  states={len(transitions)} (unit residues mod {3**args.correlated_depth} "
        f"x height floors {{{','.join(map(str, heights))}}}); "
        "three correlated source lifts"
    )
    print(
        f"  exponent~{exponent:.12f}, ratio=[{lower:.12f},{upper:.12f}], "
        f"iterations={iterations}"
    )


def run_correlated_three_quarters_certificate(args: argparse.Namespace) -> None:
    heights, transitions = correlated_search_configuration(args)
    factor = CORRELATED_THREE_QUARTERS_FACTOR
    q = CORRELATED_THREE_QUARTERS_Q
    assert factor**4 < 27
    assert 8 * q**4 < 1
    weights, ratio, margin, checked = exact_integer_correlated_certificate(
        transitions,
        factor,
        q,
        args.height_iterations,
        args.certificate_minimum_weight,
    )
    print()
    print("exact shared-lift net-height exponent-3/4 candidate")
    print(
        f"  states={len(transitions)} (unit residues mod {3**args.correlated_depth} "
        f"x {len(heights)} height floors); inequalities={checked}"
    )
    print(
        f"  rational edge under-bound: ({factor})*({q})^j; "
        "valid because factor^4 < 27 and 8*q^4 < 1"
    )
    print(
        f"  exact integer inequalities strict; minimum ratio={ratio:.12f}; "
        f"minimum scaled margin={margin}; weights=[{min(weights)},{max(weights)}]"
    )
    if args.print_certificate:
        print("  weights=(")
        for offset in range(0, len(weights), 9):
            print("    " + ", ".join(map(str, weights[offset : offset + 9])) + ",")
        print("  )")


def run_correlated_four_fifths_certificate(args: argparse.Namespace) -> None:
    heights = CORRELATED_FOUR_FIFTHS_HEIGHT_BINS
    transitions = build_correlated_height_transitions(
        CORRELATED_FOUR_FIFTHS_DEPTH,
        heights,
        args.height_children,
        True,
    )
    factor = CORRELATED_FOUR_FIFTHS_FACTOR
    q = CORRELATED_FOUR_FIFTHS_Q
    assert factor**5 < 81
    assert 16 * q**5 < 1
    weights, ratio, margin, checked = exact_integer_correlated_certificate(
        transitions,
        factor,
        q,
        args.height_iterations,
        args.certificate_minimum_weight,
    )
    print()
    print("exact shared-lift net-height exponent-4/5 candidate")
    print(
        f"  states={len(transitions)} (unit residues mod "
        f"{3**CORRELATED_FOUR_FIFTHS_DEPTH} x {len(heights)} height floors); "
        f"inequalities={checked}"
    )
    print(
        f"  rational edge under-bound: ({factor})*({q})^j; "
        "valid because factor^5 < 81 and 16*q^5 < 1"
    )
    print(
        f"  exact integer inequalities strict; minimum ratio={ratio:.12f}; "
        f"minimum scaled margin={margin}; weights=[{min(weights)},{max(weights)}]"
    )
    if args.print_certificate:
        print("  weights=(")
        for offset in range(0, len(weights), 9):
            print("    " + ", ".join(map(str, weights[offset : offset + 9])) + ",")
        print("  )")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--children",
        type=int,
        default=12,
        help="number of reusable growing costs derived in each residue class",
    )
    parser.add_argument(
        "--verify-up-to",
        type=int,
        default=10_000,
        help="exhaustively check all unit parents through this value",
    )
    parser.add_argument(
        "--budgets",
        default="13,19,30,80",
        help="comma-separated bit budgets for prefix-free leaf counts",
    )
    parser.add_argument("--q-num", type=int, default=5)
    parser.add_argument("--q-den", type=int, default=6)
    parser.add_argument(
        "--height-search",
        action="store_true",
        help="run the conservative residue-plus-height j=1 transfer search",
    )
    parser.add_argument(
        "--net-search",
        action="store_true",
        help="search after refunding the factor 3 between odd endpoints",
    )
    parser.add_argument(
        "--correlated-net-search",
        action="store_true",
        help="run the shared-next-ternary-digit net-height search",
    )
    parser.add_argument(
        "--correlated-net-search-only",
        action="store_true",
        help="run only the shared-lift search, skipping the standard exact checks",
    )
    parser.add_argument(
        "--correlated-three-quarters-certificate",
        action="store_true",
        help="generate and exactly check a 3/4 shared-lift integer certificate",
    )
    parser.add_argument(
        "--correlated-four-fifths-certificate",
        action="store_true",
        help="generate and exactly check the depth-8 4/5 integer certificate",
    )
    parser.add_argument(
        "--correlated-depth",
        type=int,
        default=CORRELATED_THREE_QUARTERS_DEPTH,
        help="ternary residue depth for --correlated-net-search",
    )
    parser.add_argument(
        "--correlated-height-bins",
        default=",".join(map(str, CORRELATED_THREE_QUARTERS_HEIGHT_BINS)),
        help="height floors for --correlated-net-search",
    )
    parser.add_argument("--certificate-minimum-weight", type=int, default=1_000_000)
    parser.add_argument("--print-certificate", action="store_true")
    parser.add_argument("--ternary-depth", type=int, default=3)
    parser.add_argument("--height-children", type=int, default=7)
    parser.add_argument("--height-iterations", type=int, default=4000)
    parser.add_argument(
        "--height-bins",
        default="1,7/4",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.correlated_net_search_only:
        run_correlated_net_search(args)
        return
    if args.correlated_three_quarters_certificate:
        run_correlated_three_quarters_certificate(args)
        return
    if args.correlated_four_fifths_certificate:
        run_correlated_four_fifths_certificate(args)
        return
    if args.children < 1:
        raise ValueError("--children must be positive")
    if args.verify_up_to < 2:
        raise ValueError("--verify-up-to must be at least 2")
    q = Fraction(args.q_num, args.q_den)
    if not 0 < q < 1:
        raise ValueError("q must lie strictly between 0 and 1")

    rows = {
        residue: first_reusable_costs(residue, args.children)
        for residue in UNIT_RESIDUES_MOD_9
    }
    envelope = coordinatewise_envelope(rows)
    expected = tuple(expected_envelope(index) for index in range(args.children))
    assert envelope == expected

    print("growing reusable odd-child costs by parent residue mod 9")
    for residue, costs in rows.items():
        print(f"  {residue}: " + ",".join(map(str, costs)))
    print("worst: " + ",".join(map(str, envelope)))

    prefix, weight = minimum_supercritical_prefix(envelope, q)
    denominator = args.q_den ** prefix[-1]
    numerator = sum(
        args.q_num**cost
        * args.q_den ** (prefix[-1] - cost)
        for cost in prefix
    )
    assert weight == Fraction(numerator, denominator)
    assert numerator > denominator
    print()
    print(
        f"finite transfer: q={args.q_num}/{args.q_den}, costs={list(prefix)}, "
        f"sum(q^j)={float(weight):.12f} > 1"
    )
    print(
        f"exact margin: {numerator} - {denominator} = {numerator - denominator} "
        f"over {denominator}"
    )
    print(
        f"certified counting exponent: log2({args.q_den}/{args.q_num}) "
        f"= {log2(args.q_den / args.q_num):.12f}"
    )

    q_critical, exponent_critical = critical_exponent()
    print(
        f"infinite-envelope critical q={q_critical:.12f}; "
        f"limiting exponent={exponent_critical:.12f}"
    )

    budgets = sorted({int(value) for value in args.budgets.split(",") if value})
    if not budgets or budgets[0] < 0:
        raise ValueError("--budgets must contain nonnegative integers")
    counts = prefix_free_leaf_counts(prefix, budgets[-1])
    print()
    print("prefix-free leaves from the finite certificate")
    for budget in budgets:
        count = counts[budget]
        exponent = log2(count) / budget if budget else 0.0
        print(f"  p={budget:3d}: leaves={count:>10,d}, exponent={exponent:.12f}")

    checked = verify_arithmetic(rows, args.verify_up_to)
    print()
    print(
        f"verified {checked:,} child blocks for every 3-unit parent "
        f"2 <= x <= {args.verify_up_to:,}; odd-parent collisions: none"
    )

    print("j=1 child status by parent residue mod 9")
    for residue in UNIT_RESIDUES_MOD_9:
        print(f"  {residue}: {shrinking_child_class(residue)}")
    print("  safety condition when integral: (2*x - 1) / 3 >= d")

    margin, ratio = verify_exact_height_certificate()
    print()
    print("exact residue-plus-height certificate")
    print(
        "  states=36 (unit residues mod 27 x height floors {1,7/4}); "
        "growing children=7; shrinking j=1 enabled when certified safe"
    )
    print(
        f"  q=7/9; all rational inequalities strict; "
        f"minimum ratio={float(ratio):.12f}; minimum margin={float(margin):.12f}"
    )
    print(f"  transfer exponent: log2(9/7)={log2(9 / 7):.12f}")

    net_margin, net_ratio = verify_exact_net_half_certificate()
    print()
    print("exact net-height exponent-1/2 certificate")
    print(
        "  rational edge under-bound: (5/3)*(7/10)^j; "
        "valid because (5/3)^2 < 3 and 2*(7/10)^2 < 1"
    )
    print(
        f"  all 36 inequalities strict; minimum ratio={float(net_ratio):.12f}; "
        f"minimum margin={float(net_margin):.12f}"
    )

    two_thirds_margin, two_thirds_ratio = (
        verify_exact_correlated_two_thirds_certificate()
    )
    print()
    print("exact shared-lift net-height exponent-2/3 certificate")
    print(
        "  states=270 (unit residues mod 81 x five height floors); "
        "one next ternary digit shared across every child"
    )
    print(
        "  rational edge under-bound: (52/25)*(629/1000)^j; "
        "valid because (52/25)^3 < 9 and 4*(629/1000)^3 < 1"
    )
    print(
        f"  all 810 inequalities strict; minimum ratio={float(two_thirds_ratio):.12f}; "
        f"minimum margin={float(two_thirds_margin):.12f}"
    )

    three_quarters_ratio, three_quarters_margin, three_quarters_checked = (
        verify_exact_correlated_three_quarters_certificate()
    )
    print()
    print("exact shared-lift net-height exponent-3/4 candidate")
    print(
        "  states=810 (unit residues mod 243 x height floors {1,7/4,3,6,12}); "
        "one next ternary digit shared across every child"
    )
    print(
        "  rational edge under-bound: (2279/1000)*(2973/5000)^j; "
        "valid because (2279/1000)^4 < 27 and 8*(2973/5000)^4 < 1"
    )
    print(
        f"  all {three_quarters_checked} integer inequalities strict; "
        f"minimum ratio={three_quarters_ratio:.12f}; "
        f"minimum scaled margin={three_quarters_margin}"
    )

    if args.height_search:
        run_height_search(args)
    if args.net_search:
        run_net_search(args)
    if args.correlated_net_search:
        run_correlated_net_search(args)


if __name__ == "__main__":
    main()
