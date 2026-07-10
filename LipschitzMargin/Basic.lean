/-
LipschitzMargin.Basic — the scalar Lipschitz-margin robustness corollary.

Paper: Y. Tsuzuku, I. Sato, M. Sugiyama, "Lipschitz-Margin Training" (NeurIPS
2018, arXiv:1802.04034), scalar-margin form.  Transcription:
prose/lipschitz-margin-certificate.md §1.

The flagship lemma of the whole VeriStressGT thread and the recommended FIRST
Lean target: it is a two-line real-analysis argument over a `LipschitzWith`
hypothesis, no measure theory.  The margin function `g = f_y − f_k` (or the min
over competitors) is the object; robustness on the `ε`-ball follows from
`g x₀ > K·ε`.
-/

import Mathlib

set_option autoImplicit false
open scoped NNReal

namespace VeriStressGT.LipschitzMargin

/--
**Scalar Lipschitz-margin certificate.**
If a real margin function `g` is `K`-Lipschitz in the input metric and its value
at `x₀` exceeds `K·ε`, then `g` stays strictly positive on the whole closed
`ε`-ball around `x₀` — i.e. the certified class never loses to the competitor.

This is the exact hypothesis→conclusion of the corollary in
prose/lipschitz-margin-certificate.md §1.  Expected proof (≈4 lines):
`hg.dist_le_mul` bounds `|g x − g x₀| ≤ K·dist x x₀ ≤ K·ε`, hence
`g x ≥ g x₀ − K·ε > 0`.
-/
theorem robust_of_margin_gt
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (K : ℝ≥0) (hg : LipschitzWith K g)
    (x₀ : E) (ε : ℝ)
    (hmargin : (K : ℝ) * ε < g x₀) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x := by
  intro x hx
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  -- |g x − g x₀| ≤ K·dist x x₀ ≤ K·ε
  have hlip : dist (g x) (g x₀) ≤ (K : ℝ) * dist x x₀ := hg.dist_le_mul x x₀
  have hbound : dist (g x) (g x₀) ≤ (K : ℝ) * ε :=
    hlip.trans (mul_le_mul_of_nonneg_left hx hKnn)
  -- g x₀ − g x ≤ |g x − g x₀|
  have h2 : g x₀ - g x ≤ dist (g x) (g x₀) := by
    rw [Real.dist_eq, abs_sub_comm]; exact le_abs_self _
  have hchain : g x₀ - g x ≤ (K : ℝ) * ε := h2.trans hbound
  linarith

/--
Multi-class form: with a finite competitor set and a per-competitor margin
`gₖ = f_y − f_k`, each `K`-Lipschitz, a uniform margin `> K·ε` certifies that `y`
is the argmax on the whole ball.  (Stated via the min of the `gₖ`.) -/
theorem argmax_stable_of_margin_gt
    {E : Type*} [PseudoMetricSpace E] {ι : Type*}
    (g : ι → E → ℝ) (K : ℝ≥0) (hg : ∀ k, LipschitzWith K (g k))
    (x₀ : E) (ε : ℝ)
    (hmargin : ∀ k, (K : ℝ) * ε < g k x₀) :
    ∀ x, dist x x₀ ≤ ε → ∀ k, 0 < g k x := by
  intro x hx k
  exact robust_of_margin_gt (g k) K (hg k) x₀ ε (hmargin k) x hx

/--
**Total-deviation margin certificate.**
A "box-form" of `robust_of_margin_gt` that takes a *total deviation* bound `D` over
the `ε`-box directly (rather than a per-unit-distance Lipschitz constant times `ε`):
if the margin deviates by at most `D` on the box and `g x₀ > D`, the margin stays
positive.  This is the dimensionally-correct shape for certificates whose bound
already absorbs the perturbation radius (e.g. the linear-dominance `B_max`, in which
`ε` is already inside — `linear_dominance.py:189-196`), avoiding a spurious second
`·ε`. -/
theorem robust_of_deviation_lt_margin
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (x₀ : E) (ε D : ℝ)
    (hdev : ∀ x, dist x x₀ ≤ ε → |g x - g x₀| ≤ D)
    (hmargin : D < g x₀) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x := by
  intro x hx
  have hbound := hdev x hx
  have h2 : g x₀ - g x ≤ |g x - g x₀| := by
    rw [abs_sub_comm]; exact le_abs_self _
  linarith

end VeriStressGT.LipschitzMargin
