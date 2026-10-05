# KICKOFF 2026-10-05: Mahler's 3/2 problem sits inside Nashida's benchmark (Lean statement)

**Lane:** a short wiring theorem plus cited Props.  **Engine:** Opus/low, at most two laps.  **Not launched; needs Trevor's go.**

Source: `RESEARCH-2026-10-05-rewriting-lane-landscape.md` § Outcome.  New module `CollatzMoonshot/Benchmark/Mahler.lean`.

## Freeze these

1. `def mahlerMap (x : ℕ) : Option ℕ` - Nashida's benchmark row `0:3,0,1;1:3,1,1;2:3,0,1`: `none` when `x % 4 = 3`, otherwise `some ((3*x + x % 2) / 2)`.  Plus `def MahlerMapTerminates : Prop` (every `x ≥ 1` reaches `none` in finitely many steps).
2. `def IsZNumber (ξ : ℝ) : Prop := 0 < ξ ∧ ∀ n : ℕ, Int.fract (ξ * (3/2)^n) < 1/2`.
3. `theorem zNumber_orbit_infinite {ξ} (h : IsZNumber ξ) : ∀ n, ⌊ξ * (3/2)^n⌋₊ % 4 ≠ 3 ∧ ⌊ξ*(3/2)^(n+1)⌋₊ = (3*⌊ξ*(3/2)^n⌋₊ + ⌊ξ*(3/2)^n⌋₊ % 2)/2`, and `1 ≤ ⌊ξ⌋₊`.  This is Mahler 1968, eqs. (2) and (13).  The proof is elementary: write `ξ(3/2)^n = g + r` with `0 ≤ r < 1/2`; then `3r/2 < 3/4` gives the recursion, and two consecutive odd `g` force `r ≥ 1/2`.  `g_0 = 0` makes `g_n = 0` forever, contradicting growth.
4. `theorem noZNumber_of_mahlerMapTerminates : MahlerMapTerminates → ¬ ∃ ξ, IsZNumber ξ`.
5. `Literature.FlattoLagariasPollington : Prop` (Thm 1.4, limsup − liminf ≥ 1/p) and `Literature.DubickasShifted` (the same for `ξ(p/q)^n + η`, every real `η`), cited, faithful-or-weaker.
6. Maze rows:
   - "FLP on the G_2 benchmark", verdict `wall`.  Obstruction: a `sorry` statement with 90% confidence saying every single-ratio benchmark map has covering arc ≥ 1/p.  Evidence: `experiments/g2_mahler_triage.py`; control: Mahler's map is not claimed.  Reopen `def`: a union-of-intervals extension of FLP (cf. Dubickas, Math. Nachr. 281, 2008).
   - "Benchmark termination", verdict `costume`: it contains Mahler's problem, citing theorem 4.

## Stop

Theorems 3–4 proved, the build green, `#maze_audit` passing, and a dated handoff.  No successor.
