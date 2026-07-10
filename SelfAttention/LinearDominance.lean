/-
SelfAttention.LinearDominance — the softmax-free gated-linear attention certificate.

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/linear_dominance.py
The score matrix is engineered so off-diagonal gates are EXACTLY zero
(asserted `< 1e-12`, lines 176–185): the attention pattern is diagonal by
algebraic identity, not by a softmax inequality.  So the certificate is a clean
bilinear product-rule bound — NO transcendental softmax, NO gap inequality:

  per token i:  ‖Z_i(x) − Z_i(x₀)‖ ≤ Δw·(‖V_i‖ + ΔV) + w_{ii}·ΔV  =: B_i
  with  Δw = 2ε(gate+ε),  ΔV = ε√d·σ(W_V)      (linear_dominance.py:187–197)
  cert:  m(X₀) > 2·L_h·√n·B_max                 (line 206)

This is the RECOMMENDED FIRST attention target (edge SA-5): it needs only
`Analysis.Normed` product/`mul` lemmas.  Once proved, the margin step reuses
`LipschitzMargin.robust_of_margin_gt`.
-/

import Mathlib
import LipschitzMargin.Basic

set_option autoImplicit false
open scoped BigOperators NNReal
open VeriStressGT.LipschitzMargin

namespace VeriStressGT.SelfAttention

/--
**Bilinear perturbation bound (per token).**
For a gated-linear attention output `Z_i(x) = w_{ii}(x) · V_i(x)` with the
off-diagonal gates identically zero, if the scalar gate deviates by at most `Δw`
and the value vector by at most `ΔV` on the box, then
`‖Z_i(x) − Z_i(x₀)‖ ≤ Δw·(‖V_i(x₀)‖ + ΔV) + w_{ii}(x₀)·ΔV`.

Pure product-rule: `‖w V − w₀V₀‖ = ‖(w−w₀)V + w₀(V−V₀)‖ ≤ |w−w₀|‖V‖ + |w₀|‖V−V₀‖`,
then bound `‖V‖ ≤ ‖V₀‖ + ΔV`.  No softmax. -/
theorem linearDominance_token_bound
    {d : ℕ}
    (w w₀ : ℝ) (V V₀ : EuclideanSpace ℝ (Fin d))
    (Δw ΔV : ℝ)
    (hw : |w - w₀| ≤ Δw) (hV : ‖V - V₀‖ ≤ ΔV) :
    ‖w • V - w₀ • V₀‖ ≤ Δw * (‖V₀‖ + ΔV) + |w₀| * ΔV := by
  -- product rule: w•V − w₀•V₀ = (w−w₀)•V + w₀•(V−V₀)
  have hsplit : w • V - w₀ • V₀ = (w - w₀) • V + w₀ • (V - V₀) := by
    rw [sub_smul, smul_sub]; abel
  have hVeq : V₀ + (V - V₀) = V := by abel
  have hVnorm : ‖V‖ ≤ ‖V₀‖ + ΔV := by
    have h : ‖V‖ ≤ ‖V₀‖ + ‖V - V₀‖ := by
      calc ‖V‖ = ‖V₀ + (V - V₀)‖ := by rw [hVeq]
        _ ≤ ‖V₀‖ + ‖V - V₀‖ := norm_add_le _ _
    linarith
  have hΔw : 0 ≤ Δw := (abs_nonneg _).trans hw
  calc ‖w • V - w₀ • V₀‖
      = ‖(w - w₀) • V + w₀ • (V - V₀)‖ := by rw [hsplit]
    _ ≤ ‖(w - w₀) • V‖ + ‖w₀ • (V - V₀)‖ := norm_add_le _ _
    _ = |w - w₀| * ‖V‖ + |w₀| * ‖V - V₀‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ Δw * (‖V₀‖ + ΔV) + |w₀| * ΔV := by
          apply add_le_add
          · exact mul_le_mul hw hVnorm (norm_nonneg _) hΔw
          · exact mul_le_mul_of_nonneg_left hV (abs_nonneg _)

/--
**Linear-dominance certificate — margin step (total-deviation form).**
The UCLA check is `m(X₀) > 2·L_h·√n·B_max` with **`ε` already inside `B_max`**
(`B_max` is a *total box deviation*: `dw = 2ε(gate+ε)`, `dV = ε√d·σ_V`,
`linear_dominance.py:189-206`) — it is NOT a per-unit-distance Lipschitz constant, so
one must **not** multiply by `ε` again.  Accordingly this states robustness via the
total-deviation lemma: given a bound `cert_rhs = 2·L_h·√n·B_max` on how far the margin
can move on the `ε`-box, and `m(X₀) > cert_rhs`, the margin stays positive.

This fixes the earlier version's dimensional double-count (audit F3): the previous
`LipschitzWith (2√n·B_max)` premise + `(2√n·B_max)·ε` margin multiplied `ε` twice.
The `hdev` hypothesis is exactly what `linearDominance_token_bound` + a
spectrally-normalised head (`L_h`) give per token, aggregated over `n` tokens; wiring
that derivation to `hdev` is the remaining `token_bound → deviation` work (audit F2). -/
theorem linearDominance_robust
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (n : ℕ) (Lh Bmax : ℝ)
    (x₀ : E) (ε : ℝ)
    (hdev : ∀ x, dist x x₀ ≤ ε → |g x - g x₀| ≤ 2 * Lh * Real.sqrt n * Bmax)
    (hmargin : 2 * Lh * Real.sqrt n * Bmax < g x₀) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x :=
  robust_of_deviation_lt_margin g x₀ ε (2 * Lh * Real.sqrt n * Bmax) hdev hmargin

end VeriStressGT.SelfAttention
