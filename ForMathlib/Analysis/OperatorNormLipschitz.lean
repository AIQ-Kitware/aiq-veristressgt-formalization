/-
ForMathlib candidate: the operator norm of a continuous linear map is exactly its
Lipschitz constant, and Lipschitz constants compose submultiplicatively — the
`L = ∏ ‖Wᵢ‖₂` composition bound behind the VeriStressGT CNN certificate (T1′).

Status: the single-affine-layer bound `lipschitz_affine_of_opNorm` follows from
`ContinuousLinearMap.lipschitz` + translation invariance.  The reusable packaged
piece is `lipschitzWith_listComp` — the product-of-constants bound for a *list* of
composed Lipschitz self-maps — which the `LipschitzMargin` net construction uses to
prove `LipschitzWith (∏ᵢ ‖Wᵢ‖₊) net` (see `LipschitzMargin/DeepContractiveCNN.lean`,
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
constant `∏ Kᵢ`, where `fᵢ` is `Kᵢ`-Lipschitz (paired via `List.Forall₂`).  This is
the reusable packaged form of iterated `LipschitzWith.comp`; the `LipschitzMargin`
net uses it to obtain `LipschitzWith (∏ᵢ ‖Wᵢ‖₊) net`. -/
theorem lipschitzWith_listComp {E : Type*} [PseudoEMetricSpace E]
    {fs : List (E → E)} {Ks : List ℝ≥0}
    (h : List.Forall₂ (fun f K => LipschitzWith K f) fs Ks) :
    LipschitzWith Ks.prod (fs.foldr (· ∘ ·) id) := by
  induction h with
  | nil => simpa using LipschitzWith.id
  | cons hf _ ih => simpa [List.prod_cons] using hf.comp ih

end VeriStressGT.ForMathlib
