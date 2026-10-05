# Dubickas - "On the powers of 3/2 and other rational numbers"

- **Venue**: Math. Nachr. 281 (2008), no. 7, 951-958, doi:10.1002/mana.200510651.  Cornell/Wiley, read 2026-10-05.
- **Thm 1.1 / Cor 1.2**: no `ξ` with `{ξ(3/2)^n} ∈ [8/39, 18/39] ∪ [21/39, 31/39]` for all `n` (total length 20/39 > 1/2).  More generally, for `η ∈ [1/5, 8/39]`, no `ξ` has `η ≤ ‖ξ(3/2)^n‖ ≤ 9η/4` for all `n`.
- **Thm 1.3**: every `(k, k + 1)` contains `ξ` with `‖ξ(3/2)^n‖ > 5/48` for all `n ≥ 0`.  This is the record our arc-trap certificate (0.1196) beats.  Pollington 1981 gave 4/65 and announced 0.088.
- **Lemma 1.4** (the proof engine): an adversary shows `{3, -1}` or `{1, -3}` at each step and the player picks one, keeping `|Σ_j u_{n+j}(2/3)^j| < 2.3745` for all `n`.  This is a parity-adversarial game, the same shape as `experiments/arc_trap_k.py`.
- §2: general `p/q` existence results (Thm 2.2, a Tijdeman-type interval; Thm 2.3, centred arcs for `p > 2q`).  None of them applies to 3/2.
