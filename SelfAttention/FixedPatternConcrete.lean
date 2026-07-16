/-
SelfAttention.FixedPatternConcrete — the *concrete* fixed-pattern instance (bridging step
B1, REFERENCE-COMPARISON.md §6).

`FixedPatternBlock.lean` proves the softmax fixed-pattern certificate
(`fixedPattern_robust_derived`) over an *abstract* `FixedPatternAttn`, whose `score`/`V`
maps are opaque function fields; the reference-comparison pass flagged that the certificate's
`hρ`/`hδV` deviation hypotheses are then *assumed* rather than *derived* from the shipped
construction's actual maps
(`ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/fixed_pattern.py`):

  Sᵢⱼ(X) = α⟪Xᵢ, Xⱼ⟫,      Vⱼ(X) = W_V Xⱼ.

This file instantiates those maps as `dotProductAttn α W_V` and **discharges `hρ`/`hδV` from
the already-proved lemmas** (`score_deviation_unit → score_row_deviation`,
`lipschitz_affine_of_opNorm`, `euclid_dist_le_sqrt_card_mul`), so the end-state certificate
`fixedPattern_robust_concrete` carries only *primitive* hypotheses: the weights, the
unit-token normalization `‖X₀ᵢ‖ ≤ 1` (enforced by the construction), the nominal value
bound `Vmax` (data), `0 ≤ ε`, and the margin condition.  No derivable deviation fact remains
a hypothesis — the R1/R2 gap of §4 is closed for this construction.

The token box is the VNN-LIB L∞ ε-box (`dist X X₀ ≤ ε` in the sup metric on
`Fin n → Fin d → ℝ`); the per-token ℓ² deviation `‖ΔXᵢ‖₂ ≤ √d·ε` is the `√d` glue
(`euclid_dist_le_sqrt_card_mul`).  Constants match `compute_L_attn`: `B_S·ε = |α|(2√d·ε +
d·ε²)`, so `ρ = √n·B_S·ε` and the pooled leading coefficient is the honest `n/2`
(`Z_deviation_n2`; edge `attn-Lattn-n4-pooling`).
-/

import Mathlib
import SelfAttention.FixedPatternBlock
import SelfAttention.ConcreteGlue

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib VeriStressGT.LipschitzMargin WithLp

namespace VeriStressGT.SelfAttention

variable {n d dv : ℕ}

/-- **Concrete fixed-pattern attention.**  The shipped `fixed_pattern.py` maps as a
`FixedPatternAttn`: the score row of token `i` is `(α⟪Xᵢ, Xⱼ⟫)ⱼ` and the value of token `j`
is `W_V Xⱼ`.  Tokens `X i : Fin d → ℝ` are read into `EuclideanSpace` via `toLp`. -/
noncomputable def dotProductAttn (α : ℝ)
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv)) :
    FixedPatternAttn n d dv where
  score := fun X i => toLp 2 (fun j => α * (inner ℝ (toLp 2 (X i)) (toLp 2 (X j)) : ℝ))
  V := fun X j => WV (toLp 2 (X j))

@[simp] theorem dotProductAttn_score_apply (α : ℝ)
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X : Fin n → Fin d → ℝ) (i j : Fin n) :
    ofLp ((dotProductAttn α WV).score X i) j
      = α * (inner ℝ (toLp 2 (X i)) (toLp 2 (X j)) : ℝ) := rfl

@[simp] theorem dotProductAttn_V_apply (α : ℝ)
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X : Fin n → Fin d → ℝ) (j : Fin n) :
    (dotProductAttn α WV).V X j = WV (toLp 2 (X j)) := rfl

/--
**Concrete fixed-pattern robustness certificate (B1).**  For the shipped dot-product
attention `dotProductAttn α W_V`, with unit-norm nominal tokens (`‖X₀ᵢ‖ ≤ 1`) and nominal
value bound `Vmax`, if the nominal margin exceeds `2·‖W_head‖·√n·K` for every competitor
— where `K = fpK n ρ δV Vmax`, `ρ = √n·|α|(2√d·ε + d·ε²)`, `δV = ‖W_V‖·√d·ε` are the
construction-level deviations — then `y` wins throughout the L∞ ε-box.

Unlike `fixedPattern_robust_derived`, **`hρ` and `hδV` are not hypotheses**: they are derived
here from `score_deviation_unit`/`score_row_deviation` and `W_V`'s operator norm.  The only
surviving hypotheses are the weights, the unit-token normalization, `Vmax` (data), `0 ≤ ε`,
and the margin condition — matching the reference discipline (R1/R2). -/
theorem fixedPattern_robust_concrete [NeZero n]
    (α : ℝ) (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv)) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε Vmax : ℝ) (hε : 0 ≤ ε) (hVmax0 : 0 ≤ Vmax)
    (hunit : ∀ i, ‖toLp 2 (X₀ i)‖ ≤ 1)
    (hVmax : ∀ j, ‖WV (toLp 2 (X₀ j))‖ ≤ Vmax)
    (hmargin : ∀ k, k ≠ y →
      2 * ‖Whead‖ * (Real.sqrt n *
          fpK n (Real.sqrt n * (|α| * (2 * (Real.sqrt d * ε) + (Real.sqrt d * ε) ^ 2)))
            (‖WV‖ * (Real.sqrt d * ε)) Vmax)
        < (dotProductAttn α WV).margin Whead bhead y k X₀) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y →
      0 < (dotProductAttn α WV).margin Whead bhead y k X := by
  set A := dotProductAttn (n := n) (d := d) (dv := dv) α WV with hA
  set δ : ℝ := Real.sqrt d * ε with hδ
  have hδ0 : 0 ≤ δ := mul_nonneg (Real.sqrt_nonneg _) hε
  set BSε : ℝ := |α| * (2 * δ + δ ^ 2) with hBSε
  have hBSε0 : 0 ≤ BSε := mul_nonneg (abs_nonneg _) (by positivity)
  -- (hρ) score-row deviation, derived from `score_deviation_unit`
  have hρ : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.score X i - A.score X₀ i‖ ≤ Real.sqrt n * BSε := by
    intro X hX i
    refine A.score_row_deviation X X₀ i BSε hBSε0 (fun j => ?_)
    simp only [hA, dotProductAttn_score_apply]
    exact score_deviation_unit α (toLp 2 (X i)) (toLp 2 (X j)) (toLp 2 (X₀ i)) (toLp 2 (X₀ j))
      δ hδ0 (token_l2_dev X X₀ ε hε hX i) (token_l2_dev X X₀ ε hε hX j) (hunit i) (hunit j)
  -- (hδV) value deviation, derived from `W_V`'s operator norm
  have hδV : ∀ X, dist X X₀ ≤ ε → ∀ j, ‖A.V X j - A.V X₀ j‖ ≤ ‖WV‖ * δ := by
    intro X hX j
    exact clm_token_dev WV X X₀ ε hε hX j
  exact fixedPattern_robust_derived A Whead bhead y X₀ ε (Real.sqrt n * BSε) (‖WV‖ * δ) Vmax
    (mul_nonneg (Real.sqrt_nonneg _) hBSε0) (mul_nonneg (norm_nonneg _) hδ0) hVmax0
    hρ hδV hVmax hmargin

end VeriStressGT.SelfAttention
