/-
SelfAttention.DominantKeyCert — Proposition 10 of paper Appendix A.7 (AUDIT4 N2 step 5): the
linear-dominance robustness certificate built on the per-row output-perturbation bound
(`attn_output_perturbation`, Prop. 9) via the `√n` token pooling and the linear head/margin.

Reuses the same pooling+head+margin shape as `LinearDominanceBlock`
(`zflat_deviation`/`margin_deviation`/`linearDominance_robust_derived`), here for the
*attention output* `Zᵢ(X) = ∑ⱼ aᵢⱼ·Vⱼ` with the per-row deviation `Δ_lin` supplied by Prop. 9.
Transcription: `prose/dominant-key-linear-attention.md`.
-/

import Mathlib
import LipschitzMargin.Basic
import ForMathlib.Analysis.OperatorNormLipschitz

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib VeriStressGT.LipschitzMargin WithLp

namespace VeriStressGT.SelfAttention

variable {n d dv : ℕ}

/-- The ℓ²-flattened concatenation of the per-row outputs `Z` — the vector the head acts on. -/
noncomputable def rowsFlat (Z : Fin n → EuclideanSpace ℝ (Fin dv)) :
    EuclideanSpace ℝ (Fin n × Fin dv) := toLp 2 (fun p : Fin n × Fin dv => ofLp (Z p.1) p.2)

/-- **Generic `√n` token pooling.**  If every one of the `n` per-row outputs moves by `≤ K`,
their ℓ²-flattened concatenation moves by `≤ √n·K`.  (The reusable core of
`LinearDominanceBlock.zflat_deviation`, stated directly on per-row deviations.) -/
theorem rowsFlat_pool_le (Z Z₀ : Fin n → EuclideanSpace ℝ (Fin dv)) (K : ℝ) (hK : 0 ≤ K)
    (hZ : ∀ i, ‖Z i - Z₀ i‖ ≤ K) : ‖rowsFlat Z - rowsFlat Z₀‖ ≤ Real.sqrt n * K := by
  rw [← dist_eq_norm, EuclideanSpace.dist_eq,
    show Real.sqrt n * K = Real.sqrt ((n : ℝ) * K ^ 2) from by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK]]
  apply Real.sqrt_le_sqrt
  have key : ∑ p : Fin n × Fin dv, dist (rowsFlat Z p) (rowsFlat Z₀ p) ^ 2
      = ∑ i, ‖Z i - Z₀ i‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [← dist_eq_norm, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
    apply Finset.sum_congr rfl; intro j _; rfl
  rw [key]
  calc ∑ i, ‖Z i - Z₀ i‖ ^ 2
      ≤ ∑ _i : Fin n, K ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        nlinarith [hZ i, norm_nonneg (Z i - Z₀ i)]
    _ = (n : ℝ) * K ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The scalar per-competitor margin of a linear head `W_head·rowsFlat + b_head` (class `y`
vs `k`). -/
noncomputable def rowsMargin {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y k : Fin c) (Z : Fin n → EuclideanSpace ℝ (Fin dv)) : ℝ :=
  (Whead (rowsFlat Z) + bhead) y - (Whead (rowsFlat Z) + bhead) k

/--
**Prop. 10 (paper A.7, eq. 68–71) — the linear-dominance certificate.**  For an attention
block with per-row output `Z X i`, if every row moves by at most `Δ_lin` over the L∞ box
(supplied by Prop. 9, `attn_output_perturbation`) and the nominal margin exceeds
`2·‖W_head‖·√n·Δ_lin` for every competitor, then class `y` wins throughout the box.  The
`√n` is the token pooling (`rowsFlat_pool_le`); the `2·‖W_head‖` is the two-competitor head
sensitivity — the same shape as `linearDominance_robust_derived`. -/
theorem linAttn_dominant_robust {c : ℕ}
    (Z : (Fin n → Fin d → ℝ) → Fin n → EuclideanSpace ℝ (Fin dv))
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε Δlin : ℝ) (hΔlin : 0 ≤ Δlin)
    (hrows : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖Z X i - Z X₀ i‖ ≤ Δlin)
    (hmargin : ∀ k, k ≠ y →
      2 * ‖Whead‖ * (Real.sqrt n * Δlin) < rowsMargin Whead bhead y k (Z X₀)) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y → 0 < rowsMargin Whead bhead y k (Z X) := by
  intro X hX k hk
  refine robust_of_deviation_lt_margin (fun X' => rowsMargin Whead bhead y k (Z X')) X₀ ε
    (2 * ‖Whead‖ * (Real.sqrt n * Δlin)) ?_ (hmargin k hk) X hX
  intro X' hX'
  -- margin deviation ≤ 2‖Whead‖·‖Δrowsflat‖ ≤ 2‖Whead‖·√n·Δlin
  set Δz := rowsFlat (Z X') - rowsFlat (Z X₀) with hΔz
  have hmapY : Whead (rowsFlat (Z X')) y - Whead (rowsFlat (Z X₀)) y = Whead Δz y := by
    rw [hΔz, map_sub]; rfl
  have hmapK : Whead (rowsFlat (Z X')) k - Whead (rowsFlat (Z X₀)) k = Whead Δz k := by
    rw [hΔz, map_sub]; rfl
  have happ : ∀ (u : EuclideanSpace ℝ (Fin c)) (j : Fin c), (u + bhead) j = u j + bhead j :=
    fun _ _ => rfl
  have hdiff : rowsMargin Whead bhead y k (Z X') - rowsMargin Whead bhead y k (Z X₀)
      = Whead Δz y - Whead Δz k := by
    simp only [rowsMargin, happ]; rw [← hmapY, ← hmapK]; ring
  rw [hdiff]
  have hz : ‖Δz‖ ≤ Real.sqrt n * Δlin :=
    rowsFlat_pool_le (Z X') (Z X₀) Δlin hΔlin (fun i => hrows X' hX' i)
  have hop : ‖Whead Δz‖ ≤ ‖Whead‖ * ‖Δz‖ := Whead.le_opNorm Δz
  have hcoordY : |Whead Δz y| ≤ ‖Whead Δz‖ := ForMathlib.abs_apply_le_norm _ _
  have hcoordK : |Whead Δz k| ≤ ‖Whead Δz‖ := ForMathlib.abs_apply_le_norm _ _
  have htri : |Whead Δz y - Whead Δz k| ≤ |Whead Δz y| + |Whead Δz k| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (Whead Δz y) (Whead Δz k)
  have hznn : (0 : ℝ) ≤ Real.sqrt n * Δlin := mul_nonneg (Real.sqrt_nonneg _) hΔlin
  calc |Whead Δz y - Whead Δz k|
      ≤ 2 * ‖Whead Δz‖ := by linarith [htri, hcoordY, hcoordK]
    _ ≤ 2 * (‖Whead‖ * (Real.sqrt n * Δlin)) := by
        have := mul_le_mul_of_nonneg_left hz (norm_nonneg Whead)
        linarith [hop, this]
    _ = 2 * ‖Whead‖ * (Real.sqrt n * Δlin) := by ring

end VeriStressGT.SelfAttention
