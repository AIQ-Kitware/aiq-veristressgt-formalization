/-
SelfAttention.ConcreteGlue — shared L∞-box → per-token ℓ² glue for the concrete attention
instances (bridging step B1, REFERENCE-COMPARISON.md §6).

Both concrete constructions (`FixedPatternConcrete`, `LinearDominanceConcrete`) read raw
tokens `X i : Fin d → ℝ` into `EuclideanSpace` via `toLp` and need the same fact: an L∞
ε-box on the token matrix (`dist X X₀ ≤ ε` in the sup metric on `Fin n → Fin d → ℝ`) gives
a per-token ℓ² deviation `‖ΔXᵢ‖₂ ≤ √d·ε`.  This is the `√d` factor of edge `LM-4` /
`attn-Lattn` at the token layer.  Composes `dist_le_pi_dist` (sup-metric coordinate bound)
with `euclid_dist_le_sqrt_card_mul` (the ℓ∞→ℓ² Cauchy–Schwarz glue from `FixedPatternBlock`).
-/

import SelfAttention.FixedPatternBlock

set_option autoImplicit false
open scoped BigOperators
open WithLp

namespace VeriStressGT.SelfAttention

variable {n d : ℕ}

/-- **L∞-box → per-token ℓ² deviation.**  From `dist X X₀ ≤ ε` in the sup metric, each token
moves by `≤ √d·ε` in ℓ² — the `√d` glue every concrete-instance seam consumes. -/
theorem token_l2_dev (X X₀ : Fin n → Fin d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hX : dist X X₀ ≤ ε) (i : Fin n) :
    ‖toLp 2 (X i) - toLp 2 (X₀ i)‖ ≤ Real.sqrt d * ε := by
  rw [← dist_eq_norm]
  refine euclid_dist_le_sqrt_card_mul _ _ ε hε (fun j => ?_)
  show |X i j - X₀ i j| ≤ ε
  calc |X i j - X₀ i j| = dist (X i j) (X₀ i j) := (Real.dist_eq _ _).symm
    _ ≤ dist (X i) (X₀ i) := dist_le_pi_dist (X i) (X₀ i) j
    _ ≤ dist X X₀ := dist_le_pi_dist X X₀ i
    _ ≤ ε := hX

/-- Operator-norm bound for the affine ℓ² deviation of a continuous linear map applied to a
token: `‖W(toLp Xⱼ) − W(toLp X₀ⱼ)‖ ≤ ‖W‖·√d·ε`.  The value/projection seam of both concrete
constructions (`W = W_V`, `Q`, or `K`). -/
theorem clm_token_dev {dv : ℕ} (W : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X X₀ : Fin n → Fin d → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hX : dist X X₀ ≤ ε) (j : Fin n) :
    ‖W (toLp 2 (X j)) - W (toLp 2 (X₀ j))‖ ≤ ‖W‖ * (Real.sqrt d * ε) := by
  rw [← map_sub]
  exact (W.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (token_l2_dev X X₀ ε hε hX j) (norm_nonneg _))

end VeriStressGT.SelfAttention
