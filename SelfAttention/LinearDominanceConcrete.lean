/-
SelfAttention.LinearDominanceConcrete — the *concrete* linear-dominance instance (bridging
step B1, REFERENCE-COMPARISON.md §6).

`LinearDominanceBlock.lean` proves the linear-dominance certificate
(`linearDominance_robust_derived`) over an *abstract* `GatedAttn`, whose gate `w` and value
`V` are opaque function fields, so the certificate's gate/value deviation hypotheses
`hw`/`hV` are *assumed* rather than *derived* from the shipped construction's actual maps
(`ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/linear_dominance.py`):

  wᵢ(X) = ⟪Q Xᵢ, K Xᵢ⟫   (inner-product gate of affine query/key projections),
  Vⱼ(X) = W_V Xⱼ.

This file instantiates those maps as `innerGate Q K W_V` and **discharges `hw`/`hV` from
already-proved lemmas** (`inner_deviation_bound`, `clm_token_dev`), so the end-state
`linearDominance_robust_concrete` carries only *primitive* hypotheses: the weights, the
nominal query/key/gate scale `g` (data), `0 ≤ ε`, the code's per-token budget `Bmax` with
its dominating condition `hB` (data), and the margin condition.

The derived gate deviation is the honest
  `Δw = ‖Q‖√d·ε·(g + ‖K‖√d·ε) + g·‖K‖√d·ε`,
which — under the construction's unit-scaled projections (`‖Q‖√d = ‖K‖√d = 1`, nominal
scale `g`) — is `≤ 2ε(g+ε)`, exactly `linear_dominance.py`'s `dw` (conservative, safe
direction; see edge `attn-Lattn`).  The value deviation is `ΔV = ‖W_V‖√d·ε`.
-/

import Mathlib
import SelfAttention.LinearDominanceBlock
import SelfAttention.ConcreteGlue

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib VeriStressGT.LipschitzMargin WithLp

namespace VeriStressGT.SelfAttention

variable {n d dq dv : ℕ}

/-- **Concrete linear-dominance attention.**  The shipped `linear_dominance.py` maps as a
`GatedAttn`: the gate of token `i` is the inner product `⟪Q Xᵢ, K Xᵢ⟫` of affine query/key
projections, and the value of token `j` is `W_V Xⱼ`. -/
noncomputable def innerGate
    (Q K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dq))
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv)) :
    GatedAttn n d dv where
  w := fun X i => (inner ℝ (Q (toLp 2 (X i))) (K (toLp 2 (X i))) : ℝ)
  V := fun X j => WV (toLp 2 (X j))

@[simp] theorem innerGate_w_apply
    (Q K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dq))
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X : Fin n → Fin d → ℝ) (i : Fin n) :
    (innerGate Q K WV).w X i = (inner ℝ (Q (toLp 2 (X i))) (K (toLp 2 (X i))) : ℝ) := rfl

@[simp] theorem innerGate_V_apply
    (Q K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dq))
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv))
    (X : Fin n → Fin d → ℝ) (j : Fin n) :
    (innerGate Q K WV).V X j = WV (toLp 2 (X j)) := rfl

/--
**Concrete linear-dominance robustness certificate (B1).**  For the shipped inner-product
gate `innerGate Q K W_V`, with nominal query/key scale `g` (`‖Q X₀ᵢ‖, ‖K X₀ᵢ‖ ≤ g`), the
derived gate deviation `Δw = ‖Q‖√d·ε·(g + ‖K‖√d·ε) + g·‖K‖√d·ε` and value deviation
`ΔV = ‖W_V‖√d·ε`; if the code's per-token budget `Bmax` dominates (`hB`) and the nominal
margin exceeds `2·‖W_head‖·√n·Bmax` for every competitor, then `y` wins throughout the L∞
ε-box.

Unlike `linearDominance_robust_derived`, **`hw` and `hV` are not hypotheses**: they are
derived here from `inner_deviation_bound` and the projections' operator norms. -/
theorem linearDominance_robust_concrete
    (Q K : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dq))
    (WV : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin dv)) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε g Bmax : ℝ) (hε : 0 ≤ ε) (hg0 : 0 ≤ g) (hBmax : 0 ≤ Bmax)
    (hgQ : ∀ i, ‖Q (toLp 2 (X₀ i))‖ ≤ g)
    (hgK : ∀ i, ‖K (toLp 2 (X₀ i))‖ ≤ g)
    (hB : ∀ i,
      (‖Q‖ * (Real.sqrt d * ε) * (g + ‖K‖ * (Real.sqrt d * ε)) + g * (‖K‖ * (Real.sqrt d * ε)))
          * (‖(innerGate Q K WV).V X₀ i‖ + ‖WV‖ * (Real.sqrt d * ε))
        + |(innerGate Q K WV).w X₀ i| * (‖WV‖ * (Real.sqrt d * ε)) ≤ Bmax)
    (hmargin : ∀ k, k ≠ y →
      2 * ‖Whead‖ * (Real.sqrt n * Bmax)
        < (innerGate Q K WV).margin Whead bhead y k X₀) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y →
      0 < (innerGate Q K WV).margin Whead bhead y k X := by
  have hδ0 : (0 : ℝ) ≤ Real.sqrt d * ε := mul_nonneg (Real.sqrt_nonneg _) hε
  -- (hw) gate deviation, derived from `inner_deviation_bound`
  have hw : ∀ X, dist X X₀ ≤ ε → ∀ i,
      |(innerGate Q K WV).w X i - (innerGate Q K WV).w X₀ i|
        ≤ ‖Q‖ * (Real.sqrt d * ε) * (g + ‖K‖ * (Real.sqrt d * ε))
          + g * (‖K‖ * (Real.sqrt d * ε)) := by
    intro X hX i
    show |(inner ℝ (Q (toLp 2 (X i))) (K (toLp 2 (X i))) : ℝ)
          - inner ℝ (Q (toLp 2 (X₀ i))) (K (toLp 2 (X₀ i)))| ≤ _
    have hbil := inner_deviation_bound (d := dq)
      (Q (toLp 2 (X i))) (K (toLp 2 (X i))) (Q (toLp 2 (X₀ i))) (K (toLp 2 (X₀ i)))
    have hdQ : ‖Q (toLp 2 (X i)) - Q (toLp 2 (X₀ i))‖ ≤ ‖Q‖ * (Real.sqrt d * ε) :=
      clm_token_dev Q X X₀ ε hε hX i
    have hdK : ‖K (toLp 2 (X i)) - K (toLp 2 (X₀ i))‖ ≤ ‖K‖ * (Real.sqrt d * ε) :=
      clm_token_dev K X X₀ ε hε hX i
    have hKxi : ‖K (toLp 2 (X i))‖ ≤ g + ‖K‖ * (Real.sqrt d * ε) := by
      have heq : K (toLp 2 (X₀ i)) + (K (toLp 2 (X i)) - K (toLp 2 (X₀ i)))
          = K (toLp 2 (X i)) := by abel
      have h := norm_add_le (K (toLp 2 (X₀ i))) (K (toLp 2 (X i)) - K (toLp 2 (X₀ i)))
      rw [heq] at h
      exact h.trans (add_le_add (hgK i) hdK)
    refine hbil.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hdQ hKxi (norm_nonneg _) (mul_nonneg (norm_nonneg _) hδ0)
    · exact mul_le_mul (hgQ i) hdK (norm_nonneg _) hg0
  -- (hV) value deviation, derived from `W_V`'s operator norm
  have hV : ∀ X, dist X X₀ ≤ ε → ∀ j,
      ‖(innerGate Q K WV).V X j - (innerGate Q K WV).V X₀ j‖ ≤ ‖WV‖ * (Real.sqrt d * ε) :=
    fun X hX j => clm_token_dev WV X X₀ ε hε hX j
  exact linearDominance_robust_derived (innerGate Q K WV) Whead bhead y X₀ ε _ _ Bmax hBmax
    hw hV hB hmargin

end VeriStressGT.SelfAttention
