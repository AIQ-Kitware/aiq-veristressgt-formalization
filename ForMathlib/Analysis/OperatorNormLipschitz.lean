/-
Operator norm of a continuous linear map as its Lipschitz constant, and the
`L = ∏ ‖Wᵢ‖₂` composition bound behind the VeriStressGT CNN certificate (T1′).

Status: the single-affine-layer bound `lipschitz_affine_of_opNorm` follows from
`ContinuousLinearMap.lipschitz` + translation invariance.  `lipschitzWith_listComp`
— the product-of-constants bound for a *list* of composed Lipschitz self-maps — is
**not a Mathlib candidate**: the 2026-07-13 prior-art audit (EXTERNAL-LEAN-SURVEY.md
§10) found it subsumed by Mathlib's `LipschitzWith.list_prod`
(`Mathlib/Topology/EMetricSpace/Lipschitz.lean`; in `Function.End α`, `List.prod` is
exactly `foldr (· ∘ ·) id`).  It is kept only as a local `Forall₂`-shaped convenience
wrapper for the `LipschitzMargin` net construction, which uses it to prove
`LipschitzWith (∏ᵢ ‖Wᵢ‖₊) net` (see `LipschitzMargin/DeepContractiveCNN.lean`,
`netLipschitz`).

Cross-ref: prose/lipschitz-margin-certificate.md §2; edge `dccnn-L-power-iter`
(the empirical `L̂` from power iteration is a *lower* bound on the true `∏‖Wᵢ‖₂`,
so it does NOT satisfy the upper-bound hypothesis these lemmas want — see the
edges Appendix A).
-/

import Mathlib

set_option autoImplicit false
open scoped NNReal

namespace VeriStressGT.ForMathlib

/-- A single coordinate of a Euclidean vector is bounded by its L²-norm:
`|v j| ≤ ‖v‖`.  Thin wrapper over Mathlib's `PiLp.norm_apply_le`; the shared coordinate
bound used by the attention certificates (audit AUDIT3 H5, de-duplicated from the two
`SelfAttention` block files). -/
theorem abs_apply_le_norm {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (j : ι) : |v j| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le v j

/-- A `1`-Lipschitz activation composed with an affine map `x ↦ W x + b` keeps the
Lipschitz constant equal to the operator norm of `W`.  (`W` is a continuous linear
map; adding a constant `b` and postcomposing a `1`-Lipschitz `φ` preserve the
constant.)  This is the single genuine (small) target here: `‖W‖₊`-Lipschitz of the
affine map, from `ContinuousLinearMap.lipschitz` plus `LipschitzWith.const_add`. -/
theorem lipschitz_affine_of_opNorm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : E →L[ℝ] F) (b : F) :
    LipschitzWith ‖W‖₊ (fun x => W x + b) := by
  intro x y
  calc edist (W x + b) (W y + b)
      = edist (W x) (W y) := by simp [edist_dist, dist_add_right]
    _ ≤ ‖W‖₊ * edist x y := W.lipschitz x y

/-- **Product-of-constants composition bound.**  A composition of Lipschitz
self-maps `f₀ ∘ f₁ ∘ … ∘ fₖ₋₁` (as `List.foldr (· ∘ ·) id fs`) is Lipschitz with
constant `∏ Kᵢ`, where `fᵢ` is `Kᵢ`-Lipschitz (paired via `List.Forall₂`).

**Subsumed by Mathlib's `LipschitzWith.list_prod`** (audit 2026-07-13,
EXTERNAL-LEAN-SURVEY.md §10): in `Function.End α` the list product is exactly this
foldr-composition, so this is the same theorem with `Forall₂` packaging instead of
an indexed family.  Kept as a local convenience wrapper (3 lines from
`LipschitzWith.comp`); cite `LipschitzWith.list_prod` upstream, do not PR this. -/
theorem lipschitzWith_listComp {E : Type*} [PseudoEMetricSpace E]
    {fs : List (E → E)} {Ks : List ℝ≥0}
    (h : List.Forall₂ (fun f K => LipschitzWith K f) fs Ks) :
    LipschitzWith Ks.prod (fs.foldr (· ∘ ·) id) := by
  induction h with
  | nil => simpa using LipschitzWith.id
  | cons hf _ ih => simpa [List.prod_cons] using hf.comp ih

end VeriStressGT.ForMathlib
