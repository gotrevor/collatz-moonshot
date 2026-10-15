# KICKOFF 2026-10-15: ray joins (Theorem J, research §52)

Repo `collatz-moonshot-amusical-zcore` (branch `wip/amusical-rayjoin`): close every `sorry` in
`CollatzMoonshot/AmusicalRayJoin.lean`.

## Ratified, do not change

`EllisonBound` and the three theorem statements.  No `native_decide`, no new axioms; `EllisonBound`
stays a hypothesis.  Lean lines ≤ 100 characters.  Do **not** edit `RESEARCH-*.md`.  **Commit after
every proved target.**  Write notes to disk as you go (`HANDOFF-amusical-rayjoin.md`).

## Paper proofs (Fable round 5, `~/personal/tmp/amusical-agents/out/newroutes5-fable.md` §2.2; Ren checked)

1. **`ray_join_three`, `ray_join_four`.**  `decide` (or `rfl`/`norm_num [amusical]` step by step).
2. **`no_early_ray_join`.**  Write `x_j = U^j(3^m)`; each step is `2^{k_j} x_{j+1} = 3 x_j + ε_j` with
   `(k_j, ε_j) ∈ {(1,0), (2,1), (2,−1)}` (`amusical_step_affine` / `amusical_iterate_affine` in
   `AmusicalGlobal.lean` give the iterate form `2^{b_k} x_k = 3^k · 3^m + C_k`, `b_k ≤ 2k`).
   * **Lemma BJ.**  `|C_k| ≤ (1/3)·Σ_{j<k} 3^{k−j}·2^{b_j}·…`; the usable form is
     `|C_k| / 3^{k+m} ≤ Q_k ≤ (4/3)^k · 3^{−m}` (each step adds `|ε_j| 2^{b_j}/3^{j+1}` to `|e|`,
     `e_k = C_k/3^k`, and `b_j ≤ 2j`).  Stronger: `|C_k| < 4^k` already (`amusical_iterate_affine`),
     which gives `|2^x/3^y − 1| < (4/3)^k 3^{−m}` with `x = b_k + m'`, `y = k + m`.
   * **Ellison.**  If `x_k = 2^{m'}` then `2^x − 3^y = C_k`.  If `x ∉ S` (the finite set),
     `EllisonBound` gives `2^x e^{−x/10} < |C_k| < 4^k`.  With `2^x ≥ 3^y/2` (from `|2^x/3^y − 1| < 1/2`)
     and `x ≤ 1.585·(k+m) + 1`, this needs `(4/3)^k 3^{−m} > ½ e^{−0.1585(k+m) − 0.1}`, false once
     `k ≤ 2m − 2` and `m ≥ 17` (check the constants; any clean sufficient chain is fine, e.g. bound
     `log 2/log 3`, `e^{−x/10} ≥ 2^{−x/6.93}`, and compare powers of 2, 3, 4 in ℕ).
   * **Finite cases.**  `x ∈ S` forces `2^x ≤ 2^27`, so `3^{k+m} < 2^28` and `k + m ≤ 17`; together with
     `m ≤ 16` everything is finitely many `(m, k)` with `k ≤ 2m − 2 ≤ 30`: check by `decide` that no
     `U^k(3^m)` is a power of 2 there (a Python check found none for `m < 60`).  Structure the proof
     as "`m ≤ 16` → finite check" and "`m ≥ 17` → Ellison", with `x ∈ S` impossible when `m ≥ 17`
     (then `3^y ≥ 3^{18}`, so `2^x ≥ 3^y/2 > 2^{27}`).
