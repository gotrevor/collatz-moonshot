#!/usr/bin/env bash
set -euo pipefail

# Full FORMALIZE gate for Campaign B. Lean 4.33.1 reports these inherited
# native_decide certificates by generated declaration name; lean-green's
# built-in native allowlist recognizes only Lean.ofReduceBool/trustCompiler.
# These are exact finite certificates already present before Campaign B,
# not new mathematical axioms. Keep this list explicit, never wildcard it.
# Sources: RhinLite{,Critical,Interval,Maximum,Approx}.lean.
repo_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
native_certificates=(
  rhinLiteRootLeft_ge_three
  rhinLite_boundProduct_certificate
  rhinLite_boundProduct_certificate_tight
  rhinLite_cauchy_radius_certificate
  rhinLite_critical_sign_change
  rhinLite_factorBound_nonneg
  rhinLite_positiveRootLeft
  rhinLite_rootBracket_lt
  rhinLite_rootBrackets_separated
  seventeen_pow_scale_le_rhinLiteBlockTerm
)
gate_args=(
  --axioms CollatzMoonshot.FrontA.affineBlockCycle_mass_bound
  --axioms CollatzMoonshot.FrontA.headBlock_cascade_composition
  --axioms CollatzMoonshot.FrontA.blockComposition_length_bound
  --axioms CollatzMoonshot.FrontA.acyclicParadoxical_length_lt_of_oddRunCount
  --axioms CollatzMoonshot.FrontA.oddRunCount_boundary_controls
  --axioms CollatzMoonshot.FrontA.fixedBlockLength_nonvacuous
  --allow CollatzMoonshot.FrontA.rhinLiteI₁_ratio_base._native.native_decide.ax_1_2
)
for certificate in "${native_certificates[@]}"; do
  gate_args+=(--allow "CollatzMoonshot.FrontA.${certificate}._native.native_decide.ax_1_1")
done
exec "$HOME/personal/bin/lean-green" "$repo_dir" "${gate_args[@]}"
