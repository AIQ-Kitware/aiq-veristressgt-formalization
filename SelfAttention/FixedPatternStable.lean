/-
SelfAttention.FixedPatternStable — the paper's pattern-stability proposition (Prop. 6),
proved on the concrete dot-product instance (bridging step B2, REFERENCE-COMPARISON.md §6).

`FixedPattern.lean` formalizes only the *arithmetic core* of the pattern-stability condition
(`gap_iff_stability_margin`), and its docstrings carry a `PatternFixed`-proxy caveat: the
shipped `check_certificate` tests the gap inequality at `X₀` only, as a *proxy* for
"the score-row argmax is constant on the box" (edge `attn-fixed-pattern-gap`/SA-3).

This file discharges that caveat for the concrete `dotProductAttn α W_V`: it proves the
genuine proposition — **the argmax of the score row is the same class `π*` for *every* `X` in
the L∞ ε-box** — provided the nominal score gap `Δ_ij = S_{iπ*}(X₀) − S_{ij}(X₀)` exceeds the
box's worst-case gap perturbation `2·B_S·ε` for every competitor `j ≠ π*`.  Proof shape
(paper eq. 44–45): `S_{iπ*}(X) − S_{ij}(X) ≥ Δ_ij − |ΔS_{iπ*}| − |ΔS_{ij}| ≥ Δ_ij − 2·B_S·ε
> 0`, with each entry deviation bounded by `score_deviation_unit`.  `B_S·ε = |α|(2√d·ε +
d·ε²)` matches `compute_L_attn`'s `B_S`.
-/

import Mathlib
import SelfAttention.FixedPatternConcrete
import SelfAttention.ConcreteGlue

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib WithLp

namespace VeriStressGT.SelfAttention

variable {n d dv : ℕ}

/-- **Per-entry score deviation (concrete dot-product attention).**  Over the L∞ ε-box, each
entry of the score row moves by at most `B_S·ε = |α|(2√d·ε + d·ε²)` — the shipped `B_S`
(`fixed_pattern.py:63`), derived from `score_deviation_unit` for `S_{ik} = α⟪Xᵢ, Xₖ⟫`. -/
theorem dotProductAttn_score_entry_dev
    (α : ℝ) (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X₀ : Fin n → Fin d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hunit : ∀ i, ‖toLp 2 (X₀ i)‖ ≤ 1)
    (X : Fin n → Fin d → ℝ) (hX : dist X X₀ ≤ ε) (i k : Fin n) :
    |ofLp ((dotProductAttn α WV).score X i) k - ofLp ((dotProductAttn α WV).score X₀ i) k|
      ≤ |α| * (2 * (Real.sqrt d * ε) + (Real.sqrt d * ε) ^ 2) := by
  simp only [dotProductAttn_score_apply]
  exact score_deviation_unit α (toLp 2 (X i)) (toLp 2 (X k)) (toLp 2 (X₀ i)) (toLp 2 (X₀ k))
    (Real.sqrt d * ε) (mul_nonneg (Real.sqrt_nonneg _) hε)
    (token_l2_dev X X₀ ε hε hX i) (token_l2_dev X X₀ ε hε hX k) (hunit i) (hunit k)

/--
**Pattern stability — paper Prop. 6, on the concrete instance (retires the `PatternFixed`
caveat).**  For the concrete dot-product attention `dotProductAttn α W_V` with unit-norm
nominal tokens, if the nominal score gap to a designated class `π*`,
`Δ_ij = S_{iπ*}(X₀) − S_{ij}(X₀)`, exceeds `2·B_S·ε` for every competitor `j ≠ π*`, then
`π*` is the **strict argmax of the score row `i` for every `X` in the L∞ ε-box** — the
score-attention pattern is genuinely constant on the box, not merely at `X₀`.

Unlike the shipped `check_certificate` (which tests the gap at `X₀` only, as an SA-3 proxy),
this is the quantified "constant on the box" statement.  The box perturbation of the gap is
`≤ 2·B_S·ε` because each of the two score entries moves by `≤ B_S·ε`
(`dotProductAttn_score_entry_dev`). -/
theorem dotProductAttn_pattern_stable
    (α : ℝ) (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X₀ : Fin n → Fin d → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hunit : ∀ i, ‖toLp 2 (X₀ i)‖ ≤ 1) (i πstar : Fin n)
    (hgap : ∀ j, j ≠ πstar →
      2 * (|α| * (2 * (Real.sqrt d * ε) + (Real.sqrt d * ε) ^ 2))
        < ofLp ((dotProductAttn α WV).score X₀ i) πstar
          - ofLp ((dotProductAttn α WV).score X₀ i) j) :
    ∀ X, dist X X₀ ≤ ε → ∀ j, j ≠ πstar →
      ofLp ((dotProductAttn α WV).score X i) j
        < ofLp ((dotProductAttn α WV).score X i) πstar := by
  intro X hX j hj
  have hdev_pi := dotProductAttn_score_entry_dev α WV X₀ ε hε hunit X hX i πstar
  have hdev_j := dotProductAttn_score_entry_dev α WV X₀ ε hε hunit X hX i j
  rw [abs_le] at hdev_pi hdev_j
  linarith [hdev_pi.1, hdev_pi.2, hdev_j.1, hdev_j.2, hgap j hj]

end VeriStressGT.SelfAttention
