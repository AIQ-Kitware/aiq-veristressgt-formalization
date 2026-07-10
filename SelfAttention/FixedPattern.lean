/-
SelfAttention.FixedPattern — softmax attention certificate (harder: needs the
softmax-Jacobian bound and the pattern-stability gap condition).

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/fixed_pattern.py
Certificate (check_certificate, lines 82–114):
  (i)  gap condition   1 − μ > 4ε√d + 2ε²d          (near-orthogonal tokens)
  (ii) margin condition m(X₀) > 2·L_h·√n·L_attn·ε
with L_attn from compute_L_attn (lines 56–71), whose leading `n/4` coefficient is
the aggregated softmax-Jacobian bound `‖diag a − a aᵀ‖ ≤ 1/2` (T2).

Depends on `ForMathlib.softmax_jacobian_opNorm_le_half`.  Edges SA-2 (the `n/4`
accounting) and SA-3 (gap condition ⟹ fixed pattern, a *sufficient* proxy).
This is Med-High difficulty; do `LinearDominance` first.
-/

import Mathlib
import LipschitzMargin.Basic
import ForMathlib.Analysis.SoftmaxJacobianBound

set_option autoImplicit false
open scoped BigOperators NNReal
open VeriStressGT.LipschitzMargin

namespace VeriStressGT.SelfAttention

/--
**Gap condition ⟺ pattern-stability margin (`δ_min > ε·C_max`).**
Let `μ` be the token coherence `max_{i≠j}|⟨x_i,x_j⟩|`, `α > 0` the score scale.
The score's minimum diagonal dominance is `δ_min = α(1−μ)`; the maximum score
perturbation over the box is `ε·C_max = ε·α(4√d + 2εd)`.  The (simplified) gap
condition `1 − μ > 4ε√d + 2ε²d` is **equivalent** to `δ_min > ε·C_max` — the
concrete inequality `check_certificate` tests (`fixed_pattern.py:90-92`,
`gap_ok_actual`), which certifies the softmax argmax pattern cannot flip in the box.
Since `α > 0`, the equivalence is exact (audit F10); we prove the full `↔`.

This is the honest, non-vacuous content of SA-3: a real inequality between the
score margin and the perturbation, not an opaque predicate.  (A fully faithful
`PatternFixed X₀ ε` predicate — "the row-argmax of the score matrix is constant on
the box" — is the eventual target; this inequality is its load-bearing sufficient
condition.) -/
theorem gap_iff_stability_margin
    {d : ℕ} (ε α μ : ℝ) (hα : 0 < α) :
    4 * ε * Real.sqrt d + 2 * ε ^ 2 * d < 1 - μ ↔
      ε * (α * (4 * Real.sqrt d + 2 * ε * d)) < α * (1 - μ) := by
  rw [show ε * (α * (4 * Real.sqrt d + 2 * ε * d))
        = α * (4 * ε * Real.sqrt d + 2 * ε ^ 2 * d) from by ring]
  constructor
  · intro h; exact mul_lt_mul_of_pos_left h hα
  · intro h; exact lt_of_mul_lt_mul_left h hα.le

/-- The forward (used) direction of `gap_iff_stability_margin`. -/
theorem gap_implies_stability_margin
    {d : ℕ} (ε α μ : ℝ) (hα : 0 < α)
    (hgap : 4 * ε * Real.sqrt d + 2 * ε ^ 2 * d < 1 - μ) :
    ε * (α * (4 * Real.sqrt d + 2 * ε * d)) < α * (1 - μ) :=
  (gap_iff_stability_margin ε α μ hα).mp hgap

/--
**Fixed-pattern softmax certificate — margin step.**
*Given* that the margin `g` is Lipschitz with `2·L_h·√n·L_attn`, a margin
`m(X₀) > 2·L_h·√n·L_attn·ε` certifies robustness on the `ε`-ball.

IMPORTANT (honest scope): as in `linearDominance_robust`, the `LipschitzWith` premise
is *assumed here, not derived*.  Deriving `LipschitzWith (2·L_h·√n·L_attn) g` for the
softmax block is the deferred content — it rests on
`ForMathlib.softmax_jacobian_opNorm_le_half` (the `n/4·½` seed — now **proved**) plus
the `compute_L_attn` aggregation and the pattern-stability condition
(`gap_iff_stability_margin`).  So this lemma is the margin step *modulo* the block's
Lipschitz constant (audit F2). -/
theorem fixedPattern_robust
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (Lattn Lh : ℝ) (n : ℕ)
    (hLh : 0 ≤ Lh) (hLattn : 0 ≤ Lattn)   -- Lh = ‖W_head‖ ≥ 0, Lattn ≥ 0 (norm-based)
    (hg : LipschitzWith (2 * Lh * Real.sqrt n * Lattn).toNNReal g)
    (x₀ : E) (ε : ℝ)
    (hmargin : (2 * Lh * Real.sqrt n * Lattn) * ε < g x₀) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x := by
  refine robust_of_margin_gt g _ hg x₀ ε ?_
  have hnn : 0 ≤ 2 * Lh * Real.sqrt n * Lattn :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hLh) (Real.sqrt_nonneg _)) hLattn
  rwa [Real.coe_toNNReal _ hnn]

end VeriStressGT.SelfAttention
