# Dubickas - "On the distance from a rational power to the nearest integer"

- **Venue**: J. Number Theory 117 (2006) 222-239, doi:10.1016/j.jnt.2005.07.004.  Cornell/ScienceDirect, read 2026-10-05.
- **Thm 3 / Cor 1** (`p/q = 3/2`): for `ξ ≠ 0`, `‖ξ(3/2)^n‖` has a limit point `≥ (3 - T(2/3))/12 = 0.238117…` and a limit point `≤ (1 + T(2/3))/4 = 0.285647…`, where `T` is the Thue-Morse product.
- **Use**: the second limit point caps `sup_ξ inf_n ‖ξ(3/2)^n‖` below 0.2857.  In Lean this is `ArcTrap.Literature.Dubickas2006`.  The first is the "opposite direction" quantity (lim sup), which is what the Markoff-Lagrange spectrum papers study.
