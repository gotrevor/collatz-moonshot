# NN and Collatz: local witnesses, missing global control

The useful similarity is a quantifier gap, not a shared proof technique.
In NN, [`G4.isDisjunctive_base`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4SchedBAssembly.lean:510)
proves that every finite word appears in the prime Lambert constant.  For
an omitted word of length `ℓ`,
[`SchedB.scheduleWitnessB`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4SchedBAssembly.lean:440)
chooses one large scale `K` depending on `ℓ`; CRT factorization, a row-mass
bound, and the omitted-cylinder covering deficit contradict the omission.
The CRT step is an actual quantitative theorem:
[`G4.crt_input`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4CRTInput.lean:255)
factors the mean of periodic phases over an AP sample, with error at most
`2Q/|sample|`, for pairwise-coprime moduli whose product is `Q`.  It uses
independent residue coordinates in a *varying sample*, not a single orbit.

Normality asks for frequencies on ordinary initial prefixes.  The
proved consumer
[`G4.isNormal_G4_of_prefixDecay`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4WindowK.lean:370)
requires [`PrefixDecay`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4WindowK.lean:333):
for every nonzero Fourier mode and `ε>0`, all sufficiently large `M` and
*every* `1≤k≤windowK M` have `o(M)` phase sums.  The
[`windowK`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4WindowK.lean:24)
site count tends to infinity, albeit at triple-log speed.  A fixed site
count leaves a current truncation bound that need not vanish with `N`;
this does not show the actual error stays nonzero.  The schedule's sparse
sampling cannot replace ordinary averages.  In the
[`Maze`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/Maze.lean:170),
`hall_T_E` has an exact masked-real counterexample, while
`hall_quantized_normality` records that the digit-local sampler reads far
below density one.  `hall_pointwise_deficit` likewise blocks turning an
averaged entropy deficit into a pointwise frequency claim.  These are
specific exclusions, not a judgment that G4 normality is false.

The Collatz local theorem is weaker in a different direction.
[`lower_five_head_pair`](/Users/gotrevor/src/collatz-moonshot/CollatzMoonshot/Obstructions/FiveHead.lean:89)
certifies a legal scalar-preserving Q move
`{5n,c}->{n,d}` for a whole arithmetic family, with `c,d<n`.
[`legalPairMove`](/Users/gotrevor/src/collatz-moonshot/CollatzMoonshot/Obstructions/CatalyticRepair.lean:9)
checks pair availability, positive oddness, and equality of `certificateValue`.
It does not supply a unit containing `c`, choose subsequent moves, or force
the directed edge boundary to be `e_n-e_1`.  The two pair boundaries have
eight distinct vertices in this family.  The sought quantifiers are closer
to: for every parameter and every supplied path certificate of the smaller
virtual endpoint, construct a restricted-palette script, without the path
of `n`, ending in a balanced certificate and decreasing a well-founded
state.  A finite repair aimed at a known path does not satisfy this.  NN's
[`window_tail_tendsto_zero`](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/G4WindowK.lean:219)
can discard distant carries because their averaged weighted tail tends to
zero.  The Collatz Q boundary instead has eight integral charges at every
parameter, with no small-tail parameter to absorb them.

The NN Maze suggests a concrete countermodel discipline.  Its masked real
agrees with every sampled observation while failing the unsampled normality
conclusion.  Collatz's analogous missing information is visible without a
new model: the five-head Q equation agrees on scalar product, while its
boundary change has `l1` norm 8 and its borrowed-label supply is separate.
One cannot infer balance by summing local product identities.  The earlier
four-charge minimum in
[`arithmetic-lifts-followup`](/Users/gotrevor/src/collatz-moonshot/RESEARCH-2026-09-27-arithmetic-lifts-followup.md:95)
also rules out a blindly decreasing `l1` repair algorithm.

What transfers precisely:

* **CRT as adversarial input selection.**  In the lower family,
  `T^6(n)+1=11675+20655h`.  Since `20655` is odd, for every `j` there is a
  residue of `h mod 2^j` making the next `j` shortcut steps all odd and
  above `n`.  This gives arbitrarily long first-descent delays inside the
  very family with the legal Q move.  It is residue construction, not CRT
  independence or a convergence estimate.  The NN
  [`Maze` CRT-stacking row](/Users/gotrevor/src/normal-numbers/src/NormalNumbers/Maze.lean:686)
  similarly warns that a residue handle can re-import the unknown quantity.
* **Multiscale witnesses as a specification discipline.**  NN chooses `K`
  from word length for occurrence, but frequency needs a growing window
  with uniform ordinary-scale control.  A Collatz repair may likewise use
  length growing with `v₂(T^6(n)+1)`; the missing theorem is a legal script
  and rank decrease *uniform in that length*.  Merely adding more finite
  certificates repeats the easy quantifier.
* **Least closure has limited reach.**  The restricted palette's closure can
  certify that `c(h)` is borrowable, just as CRT certifies certain NN local
  phase relations.  [`unit_labels_bounded`](/Users/gotrevor/src/collatz-moonshot/CollatzMoonshot/Obstructions/UnitSupportBound.lean:197)
  shows any borrowing unit for unbounded `c(h)` must grow in size.  Closure
  alone does not balance vertices or prove a terminating script.  The NN
  carry lemmas inspected here do not supply this deterministic directed-flow
  condition.

**One paired control in the `experiments/repair_family.py` suite.**
Pre-register lower-family `h=43` and `h=44`, retaining the same five-head
Q identity and `c,d<n`.  For `h=43`, `n=710983` and
`T^6(n)+1=899840=2^8·3515`, so the first 14 steps remain above `n` and
`T^14(n)=23061914`.  For `h=44`, `n=727303` and `T^7(n)=460247<n`.
Have a target-blind routine consume only the virtual certificate and a
supplied certificate for its smaller endpoint, then record legal borrowing
of `c`, the first Q move, and the odd-edge boundary vector after each move.
A claim of *full* balance must additionally locate every factor-of-two
edge and verify boundary `e_n-e_1`; a bare count of twos has no vertex
location.  Use the known `n` trajectories only as held-out evaluation.
Any candidate macro should run on both starts with the same frozen rules;
success only on the step-7 control would leave the long-growth branch open.
Record search truncation separately from a complete obstruction.  This
tests a specific local-to-global claim without treating finite success as
an induction.

The `lower-prefix h` command evaluates only the fixed six-step word
and the initial odd run given by `v₂(11675+20655h)`.  It reports a step-7
descent for even `h`, a step-8 descent for `h≡1 mod 4`, and no conclusion
about later descent in other cases.  The `lower-growth j` command chooses
the least nonnegative solution of `11675+20655h≡0 mod 2^j` for `j≥2`;
the actual odd run can exceed `j`, as it does at `j=2` with `h=3`.
