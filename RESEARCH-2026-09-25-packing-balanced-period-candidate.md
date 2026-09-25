# Candidate: finite packing, balanced periods, and Knight

25 September 2026.  Proposed during the cross-project research review by the Collatz reviewer, then checked adversarially at the level of the lemma chain.  **Not proved in this repository.**  The purpose is to identify a bounded next research test for the repeated-state branch of the 23 September Christoffel-family result.

## Proposed strengthening

For each fixed C, sufficiently long members v_K of the specific Christoffel/Beatty first-crossing family in `RESEARCH-2026-09-22-finite-packing-christoffel.md` have no positive integer realization starting at n<=C K, including realizations that repeat a state.

The existing paper proves this only with distinct odd states.  The new ingredient proposed here is to use the long remaining balanced word after the forced early repeat, and then apply Knight's already known exclusion of integral high cycles.  The change is this composition of existing ingredients.  It does not restore a general low-complexity or fixed-prefix strategy.

## Lemma chain to check

1. **Truncate before the artificially forced endpoint.**  Let alpha=log_2(3), p_i=floor(i alpha), and use the genuine Beatty prefix through L=p_(K-1).  Do not use the final forced zero at p_K as if it belonged to the infinite balanced word.
2. **Height.**  The existing affine estimate gives x_t<=3n+K<=(3C+1)K throughout this prefix.
3. **Early repeat.**  The finite residence estimate bounds a consecutive distinct prefix in [1,X] by O(X^beta log X), beta<1.  If no repeat occurs before L it already gives a contradiction.  Otherwise apply it to the prefix before the *first* repeat at j.  This gives j=O(K^beta log K)=o(K); its eventual cycle has minimal state period p<=j.  The depth-headroom loss from the finite packing lemma remains included.
4. **Long periodic factor.**  The suffix from the cycle entry to L still has length Theta(K), so eventually contains at least 2p letters.  Its letters are a factor of the genuine infinite Beatty indicator word, hence balanced.  The number of ones in an integer interval [a,a+q) is `ceil((a+q)/alpha)-ceil(a/alpha)` and is within one of q/alpha.
5. **Circular balance.**  A length-2p periodic factor contains every cyclic rotation of its length-p period and every circular factor of length at most p.  Its balance therefore makes the period word circularly balanced.  Factors of larger length reduce by removing full periods.  Write this threshold argument precisely; do not infer periodicity merely from a short repeated substring.
6. **Primitive period.**  A parity word of a minimal state cycle cannot be a proper power u^k.  The affine map F for u has positive slope, and F^k(x)=x forces F(x)=x (strict monotonic motion otherwise), contradicting minimality.  Constant parity cycles are unavailable for positive integers.
7. **Christoffel and Knight.**  A primitive circularly balanced binary word is a conjugate of a primitive Christoffel word, hence has coprime length/one-count.  A positive integer cycle gives D=2^p-3^a>0 and integral values for every rotation.  Knight's high-cycle argument applies: the difference for the appropriate two rotations is 2^(p-2)/D, so the positive odd D divides a power of two and D=1.  Only the trivial cycle remains.
8. **Trivial cycle.**  The shortcut cycle 1,2 has odd density 1/2.  A long factor of the Beatty word has count within one of its length divided by alpha, with 1/alpha>1/2, so it cannot be this alternating suffix.

## Sources and scope

- Local finite packing, including the last-depth headroom: `RESEARCH-2026-09-22-finite-packing-christoffel.md`, sections 1-3.
- De Luca and Fici, [Some results on digital segments and balanced words](https://iris.unipa.it/retrieve/979a9693-1ea2-4536-ba4a-49c888580c1f/1-s2.0-S0304397524005528-main.pdf), Proposition 18, circular balance and Christoffel conjugacy.  Check primitive/power conventions explicitly.
- Knight, [Collatz high cycles do not exist](https://doi.org/10.1016/j.disc.2025.114812), with locally audited summary `papers/knight-2026-collatz-high-cycles-summary.md`.  There is no local Lean Knight theorem; this would initially be a paper argument using the external theorem.

The existing negative inventory retires Christoffel residue signatures as a general admission method and finds no second uniform Knight identity family.  Neither is the proposed step here: the already studied v_K family forces the cycle into Knight's existing class after packing controls its entry time.

If all details check, this closes a precise repeated-state loophole for linear-size realizations of v_K.  It would not prove CST, exclude arbitrary cycles, or cover arbitrary first-crossing words.  The next larger problem would still be a genuine word-family coverage theorem and a suitable prefix-height bound.  Do not spend effort optimizing the enormous finite cutoff before the asymptotic derivation is independently checked.
