# HANDOFF — amusical adelic (2026-10-14)

Kickoff: `KICKOFF-2026-10-14-amusical-adelic.md`.  Target `CollatzMoonshot/AmusicalAdelic.lean`
is **sorry-free**; both theorems depend only on `[propext, Classical.choice, Quot.sound]`.

- `amusicalRat_intCast`: three-way case split `n = 2m | 4m+1 | 4m+3`, `if_pos/if_neg` by
  `omega`, then `push_cast; ring`.
- `amusicalRat_subgroup_one_mem` (Proposition L): instantiates
  `Adelic.one_mem` in `CollatzMoonshot/AmusicalAdelic/Descent.lean`, which is generic in a map
  `f : ℚ → ℚ` with two specs (`f x = 3x/2` at even numerator, `4 f x - 3 x = ±1` at a `2`-adic
  unit).  The descent inducts on `n` with `2^n ∤ a` for `x = a/d`, `d` odd, starting from
  `n = |x.num|`; the even step uses `IsCoprime (2^n) 3`.

Ratified statements and `amusicalRat` unchanged (diff touches only proof bodies and one import).

Next: nothing open in scope.  Theorem M and Corollary S_K (research §25) have no Lean statements
yet; they are outside this kickoff's ratified surface.
