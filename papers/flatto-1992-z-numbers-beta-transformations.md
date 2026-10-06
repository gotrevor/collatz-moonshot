# Flatto - "Z-numbers and β-transformations"

- **Venue**: in *Symbolic Dynamics and its Applications* (ed. P. Walters), Contemp. Math. 135, AMS 1992, pp. 181-201, doi:10.1090/conm/135/1185087.  Read 2026-10-05 from a scan of the volume (Anna's Archive / Libgen, ISBN 0-8218-5146-2); the chapter PDF here is an OCR'd extract of pp. 181-201.
- **Setting**: Mahler's `Z = {α > 0 : 0 ≤ {α(3/2)^n} < 1/2 ∀n}`.  Write `α(3/2)^n = g_n + r_n/2`.  **Proposition P (§2)**: `α` is a Z-number iff the parity expansion `ε_n(g_0)` of the integer map `T(g) = 3g/2` (g even), `(3g+1)/2` (g odd) equals the β-expansion of `r_0` under `f(x) = {3x/2}` with partition `[0,2/3) ∪ [2/3,1)`.  Hence at most one Z-number per `[g, g+1)` (Mahler's first theorem).
- **Thm 3.1**: for `T_{p/q}(g) = (pg+i)/q` (`pg+i ≡ 0 mod q`), *every* word in `{0..q-1}^{n+1}` is T-admissible, and its cylinder is a residue class mod `q^{n+1}`.  So the integer side imposes nothing on finite words; all constraint comes from the β-side.
- **Thm 3.2** (Parry criterion, stated without proof): β-admissible iff every shift is lexicographically `≤` the expansion of 1.  For β = 3/2, `1 = 1,0,1,0,0,...`, so forbidden blocks `11` and `10101`.
- **Thm 4.3**: with `σ = Σ f^n1/β^n`, the number `N_n` of β-admissible words of length n is `N_n = β(1-β^{-N})/(σ(β-1)) · β^n + O(δ^n)`, `δ < β` (`N` = first n with `f^n1 = 0`, else ∞).  Remark 1: topological entropy of the β-shift is `log β`.  §5 (Thm 5.2): periodic points of `f^n` in `[a,b)` grow like `(∫_a^b h)/σ · β^n`, `h(x) = Σ_{f^k1 > x} β^{-k}` (Parry's density).  Pure β-shift theory, no interval restriction.
- **Mahler's second theorem**: `|Z(x)| = O(x^{log2((1+√5)/2)}) ≈ O(x^0.70)` (no `11` block, Fibonacci count).  **Thm 6.1** (the improvement): `|Z(x)| = O(x^δ)`, `δ = log2(3/2) ≈ 0.585`, from `N_n = O((3/2)^n)`.  Also: Mahler's "two consecutive odd `g_n`" test shows no Z-numbers below 2000.
- **§7, general `Z_{t,θ} = {α > 0 : 0 ≤ {αθ^n} < t ∀n}`**, intervals anchored at 0 only.
  - Thm 7.1: `Z_{t,θ}` is countable or has the cardinality of the continuum.
  - **Thm 7.2**: `θ = p/q`, `(p,q)=1`, `p > q ≥ 2`.  (i) If `t ≤ min(1/q, 1/θ)`, each `[g, g+1)` has at most one Z-number.  (ii) If `p < q²` and `t ≤ 1/q`, then `|Z(x)| = O(x^δ)`, `δ = log_q(p/q) < 1`.  The proof of (ii) just uses `Z_{t,θ} ⊂ Z_{1/q,θ}`, so the exponent does not improve for smaller `t`.  Proposition P': the extra condition is `f^n(r_0) < tq` for all n.
  - Rederives Pollington: no Z-numbers for `t = 1/p`.
  - Thm 7.3 (Tijdeman): `θ = p/q > 2`, `t > (q-1)/(p-q)` gives at least one Z-number per `[g, g+1)`.  Thm 7.4: `p > q²`, `(q-1)/(p-q) < t ≤ q/p` gives exactly one.  Thm 7.5: `θ > 3`, `2/(θ-1) < t < 1` gives continuum many per `[g, g+1)`.  None applies to 3/2.

## Against our claims

1. **Intervals**: only `[0, t)` (fractional parts below `t`), never a general arc `[s, s+t]`.  The counted object is `|Z(x)|`, bounded via the number of β-admissible parity words.  Best exponent for 3/2 is `log2(3/2)`; for general `p/q` with `p < q²`, `log_q(p/q)`, valid only for `t ≤ 1/q`.
2. **Entropy vs interval**: entropy is computed only for the full β-shift (`log β`, Thm 4.3).  Nothing as a function of interval length or position; no `2/3`, no growth `2`, no "entropy < log 2 iff length < 2/3".
3. **Density / finite memory**: density zero (`O(x^δ)`, δ < 1) only for `[0, t)`, `t ≤ 1/q` (Thms 6.1, 7.2 ii).  No threshold statement for general arcs.  The only finite-memory content is the Parry forbidden blocks (`11`, `10101`) and the type-k renewal structure of the β-shift (Lemma 4.1, Defs 4.1-4.2).  No construction in the style of our arc-trap or finite-memory words.
4. **Length 1/2 at arbitrary position**: no.  For the arc `[0, 1/2)` the word count is `N_n ≍ (3/2)^n` (Thm 3.1 + Prop P + Thm 4.3), stated as an upper bound for `|Z(x)|`, not as an exact word count for the arc.

- **(a)** growth `< 2` on every arc of length `< 2/3`, hence density zero: **not in Flatto.**  He covers only `[0, t)` with `t ≤ 1/2` (growth 3/2, exponent `log2(3/2)`).  His Thm 6.1 is the special case: position 0, length 1/2.
- **(b)** at least `2^N` words at length exactly 2/3: **not there.**
- **(c)** growth exactly 3/2 at every position for length 1/2: **partially.**  Position 0 (Mahler's set) is effectively Thm 4.3 + Thm 6.1.  Position-independence is not addressed.
