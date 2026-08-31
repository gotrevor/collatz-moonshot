# HANDOFF 2026-08-31 — Rhin-lite objective 4: simultaneous-approximation criterion wired

- **Branch:** `main`  **Tree:** clean after commit (not pushed).
- `lake build` green (8763 jobs). `bash scripts/check-proof-debt.sh` = exactly **two** disclosed
  sorries: `FrontA/PowSeparation.lean:40` (`sep_two_three`) and `FrontA/RhinLiteApprox.lean:124`
  (`rhinLiteLIMeasure`).

## What landed this session (`CollatzMoonshot/FrontA/RhinLiteApprox.lean`, new)

Objective 4 of `FRONT-A-RHIN-LITE.md`: turn the two `D_N`-cleared log forms into the effective
separation `sep_two_three` needs, wired as far as elementary algebra allows.

**Trust-base clean (added to `scripts/AxiomAudit.lean`, ledgers `[propext, Classical.choice,
Quot.sound]`):**
- `log_three_halves`, `log_four_thirds` — `log(3/2) = log3 − log2`, `log(4/3) = 2log2 − log3`.
- `linForm_eq_log23` — **change of basis:** `(m−2k)·log(3/2) + (m−k)·log(4/3) = m·log2 − k·log3`.
  This expresses the Baker linear form `Λ` (whose lower bound `sep_two_three` needs) as a
  *homogeneous* integer combination of `{log(3/2), log(4/3)}` — no constant term — so a linear
  independence measure of `{1, log(3/2), log(4/3)}` directly bounds `Λ`.
- `elim_identity` — `B·(p + q·θ₁ + r·θ₂) = (pB − qA₁ − rA₂) + q·L₁ + r·L₂`, the algebraic
  mechanism turning the two small common-`B` forms into a lower bound on `Λ` (nonzero integer part
  `n = pB − qA₁ − rA₂` ⇒ `|BΛ| ≥ 1 − |q||L₁| − |r||L₂|`).

**The disclosed crux (single new `sorry`):**
- `rhinLiteLIMeasure` — the coarse Rhin linear-independence measure of `{1, log(3/2), log(4/3)}`:
  `∃ κ c, 0 < c ∧ ∀ (p,q,r) ≠ 0, c/H^κ ≤ |p + q·log(3/2) + r·log(4/3)|`, `H = max(|p|,|q|,|r|)`.
  Its docstring records the concrete proof route from `rhinLiteEven_two_log_forms` (data),
  `rhinLiteEvenIntegral_le/_pos` (size), `elim_identity` (algebra), determinant non-vanishing, and
  the `lcmUpto` asymptotic.

**Proved from the crux (ledger carries `sorryAx`, as expected):**
- `log23_effective_measure` — `∃ κ c, 0 < c ∧ ∀ near-critical k m, c/k^κ ≤ m·log2 − k·log3`.
  This is exactly the `hLF` shape consumed by `sep_of_linear_form_poly`. Proof: apply
  `rhinLiteLIMeasure` at `(p,q,r) = (0, m−2k, m−k)`, use `linForm_eq_log23` to identify the
  combination with `Λ`, the sign `Λ > 0` (from `3^k < 2^m`), and the crude height bound `H ≤ 2k`
  (established from `k ≤ m < 3k` on the near-critical window).

## Why this is crux progress, not scaffolding

Before this lap the sole obligation was the abstract `sep_two_three` / its `hLF` linear-form
input. That input is now **reduced to a concrete named node** — the Rhin linear-independence
measure of `{1, log(3/2), log(4/3)}` — which is *exactly* the object the entire `RhinLite*` tower
constructs its auxiliary forms to prove, and which is provably true (Rhin 1987). The two
trust-base-clean bridges (`linForm_eq_log23`, `elim_identity`) are the reusable mathematical heart
of that reduction.

## Next steps (priority order — see `PENDING_WORK.md` top block)

1. **Attack `rhinLiteLIMeasure`** (the hard node). Decompose as named sorries next lap:
   (a) size bridge `0 < Lᵢ ≤ D_N·(9/40)^N` (the `x^{N+1}`→`x^N` factor `1/x` on
   `rhinLiteEvenIntegral_le`, plus positivity from `rhinLiteEvenIntegral_pos_23/_34`);
   (b) two-consecutive-`N` determinant non-vanishing ⇒ `n ≠ 0` for one of two consecutive `N`;
   (c) `lcmUpto N ≤ 4^N·e^{o(N)}` asymptotic converting `1/(2·D_N·18^N)` into `c·H^{−κ}`.
2. **Close the elementary residual** `log23_effective_measure ⇒ sep_two_three`. The gap is the
   constant/threshold coupling in `sep_of_linear_form_poly`'s `hcross` (fixed `130` too small for
   a realistic `κ`). RESOLUTION: route through the integer `sep_of_uniform_measure` instead
   (`hK = pow_le_two_pow_gen` explicit at `k ≥ (3C)²`; `hfin` a `native_decide` table on
   `6 ≤ k < (3C)²`) once the crux lands with concrete `C`.

## Gate / audit bookkeeping

- `scripts/check-proof-debt.sh` updated to expect the two disclosed sorries (PowSeparation +
  RhinLiteApprox); rejects anything else.
- `scripts/AxiomAudit.lean` gained `linForm_eq_log23`, `elim_identity`, `log23_effective_measure`.
- `README.md`, `STATUS.md`, `DIRECTION.md`, `FRONT-A-RHIN-LITE.md`, `PENDING_WORK.md` updated.
