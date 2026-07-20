/-
SelfAttention.DominantKey — the paper's dominant-key bound (Lemma 8, App. A.7), proved for
general probability weights (bridging step B6, REFERENCE-COMPARISON.md §6 — optional depth).

The linear-dominance construction (`GatedAttn`) is certified only in the exact-diagonal
special case the code enforces. Paper Lemma 8 is the general statement: a softmax-weighted
attention output is close to the *dominant key's* value, with the gap controlled by the
dominance of that key's weight —

  ‖∑ⱼ aⱼ·Vⱼ − V_{j*}‖₂ ≤ (1 − a_{j*}) · max_{j≠j*} ‖Vⱼ − V_{j*}‖₂ .

`attn_dominant_key_bound` proves it for any probability vector `a` (so in particular for
`a = softmax`, whose `softmax_nonneg`/`softmax_sum_one` discharge the hypotheses). Proof:
the attention output minus `V_{j*}` is `∑ⱼ aⱼ·(Vⱼ − V_{j*})`, whose `j*` term vanishes, so
its norm is `≤ ∑_{j≠j*} aⱼ·‖Vⱼ − V_{j*}‖ ≤ (∑_{j≠j*} aⱼ)·M = (1 − a_{j*})·M`. This makes
the linear-dominance thread paper-complete (Lemma 8) rather than code-complete (diagonal
special case).
-/

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace VeriStressGT.SelfAttention

variable {n dv : ℕ}

/--
**Dominant-key bound (paper Lemma 8, App. A.7).**  For a probability vector `a` (`aⱼ ≥ 0`,
`∑ aⱼ = 1`), values `Vⱼ`, and a distinguished key `j*`, the convex combination `∑ⱼ aⱼ·Vⱼ`
lies within `(1 − a_{j*})·M` of `V_{j*}`, where `M` bounds the value spread
`‖Vⱼ − V_{j*}‖` over the competitors `j ≠ j*`.  As the dominant weight `a_{j*} → 1` the
output collapses onto `V_{j*}`; specialised at `a = softmax` this is the paper's linear-
dominance attention bound (generalising the exact-diagonal `GatedAttn` case). -/
theorem attn_dominant_key_bound
    (a : Fin n → ℝ) (hnn : ∀ j, 0 ≤ a j) (hsum : ∑ j, a j = 1)
    (V : Fin n → EuclideanSpace ℝ (Fin dv)) (jstar : Fin n) (M : ℝ)
    (hM : ∀ j, j ≠ jstar → ‖V j - V jstar‖ ≤ M) :
    ‖(∑ j, a j • V j) - V jstar‖ ≤ (1 - a jstar) * M := by
  -- rewrite the deviation as a weighted sum of value differences
  have hrw : ∑ j, a j • (V j - V jstar) = (∑ j, a j • V j) - V jstar := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rw [← hrw]
  -- the `j*` summand is zero, so restrict to the competitors
  have hzero : a jstar • (V jstar - V jstar) = 0 := by rw [sub_self, smul_zero]
  rw [← Finset.sum_erase (f := fun j => a j • (V j - V jstar)) Finset.univ hzero]
  calc ‖∑ j ∈ Finset.univ.erase jstar, a j • (V j - V jstar)‖
      ≤ ∑ j ∈ Finset.univ.erase jstar, ‖a j • (V j - V jstar)‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.univ.erase jstar, a j * ‖V j - V jstar‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn j)]
    _ ≤ ∑ j ∈ Finset.univ.erase jstar, a j * M := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact mul_le_mul_of_nonneg_left (hM j (Finset.mem_erase.mp hj).1) (hnn j)
    _ = (∑ j ∈ Finset.univ.erase jstar, a j) * M := by rw [Finset.sum_mul]
    _ = (1 - a jstar) * M := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ jstar), hsum]

/-! ### Lemma 8 as stated — the dominance-ratio form (AUDIT4 step N2, upgrades J2)

`attn_dominant_key_bound` is the convex-combination *core* of Lemma 8.  The paper states
Lemma 8 for *softmax/linear-attention* weights normalized from unnormalized scores `w`, with
the dominance hypothesis on the unnormalized weights and the conclusion `1/(1+ρ)`.  These
lemmas add the normalization and the ρ-bridge (eq. 59), giving Lemma 8 verbatim.  (Props 9–10
— the three-term insertion bound and the full linear-dominance certificate — remain; they
mirror the `LinearDominanceBlock` pooling/margin machinery.) -/

/-- Normalized linear-attention weight `aⱼ = wⱼ / ∑ₖ wₖ`. -/
noncomputable def linAttnWeight (w : Fin n → ℝ) (j : Fin n) : ℝ := w j / ∑ k, w k

theorem linAttnWeight_nonneg [NeZero n] (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (j : Fin n) :
    0 ≤ linAttnWeight w j :=
  div_nonneg (hw j).le (Finset.sum_pos (fun k _ => hw k) Finset.univ_nonempty).le

theorem linAttnWeight_sum_one [NeZero n] (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) :
    ∑ j, linAttnWeight w j = 1 := by
  have hpos : 0 < ∑ k, w k := Finset.sum_pos (fun k _ => hw k) Finset.univ_nonempty
  unfold linAttnWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hpos)

/-- **Eq. 59 — dominance ⟹ weight lower bound.**  If the dominant key's unnormalized weight
dominates the rest by a factor `ρ` (`ρ·∑_{j≠j*} wⱼ ≤ w_{j*}`), then its *normalized* weight
`a_{j*}` satisfies `1 − a_{j*} ≤ 1/(1+ρ)`. -/
theorem dominant_weight_bound [NeZero n] (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (jstar : Fin n)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hdom : ρ * (∑ j ∈ Finset.univ.erase jstar, w j) ≤ w jstar) :
    1 - linAttnWeight w jstar ≤ 1 / (1 + ρ) := by
  set S := ∑ j ∈ Finset.univ.erase jstar, w j with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun j _ => (hw j).le)
  have hT : ∑ k, w k = w jstar + S := by
    rw [hS, Finset.add_sum_erase _ w (Finset.mem_univ jstar)]
  have hTpos : 0 < w jstar + S := by have := hw jstar; linarith
  have h1ρ : 0 < 1 + ρ := by linarith
  have hlaw : linAttnWeight w jstar = w jstar / (w jstar + S) := by rw [linAttnWeight, hT]
  rw [hlaw, show 1 - w jstar / (w jstar + S) = S / (w jstar + S) from by field_simp; ring,
    div_le_div_iff₀ hTpos h1ρ]
  nlinarith [hdom]

/-- **Lemma 8 (paper A.7, as stated).**  For linear-attention weights normalized from positive
unnormalized scores `w`, if the dominant key `j*` dominates by `ρ`, the attention output lies
within `M/(1+ρ)` of `V_{j*}` (`M` bounds the value spread over competitors).  Composes the
convex-combination core `attn_dominant_key_bound` with the ρ-bridge `dominant_weight_bound`. -/
theorem attn_dominant_key_bound_rho [NeZero n] (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (V : Fin n → EuclideanSpace ℝ (Fin dv)) (jstar : Fin n) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ j, j ≠ jstar → ‖V j - V jstar‖ ≤ M) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hdom : ρ * (∑ j ∈ Finset.univ.erase jstar, w j) ≤ w jstar) :
    ‖(∑ j, linAttnWeight w j • V j) - V jstar‖ ≤ (1 / (1 + ρ)) * M :=
  (attn_dominant_key_bound (linAttnWeight w) (linAttnWeight_nonneg w hw)
    (linAttnWeight_sum_one w hw) V jstar M hM).trans
    (mul_le_mul_of_nonneg_right (dominant_weight_bound w hw jstar ρ hρ hdom) hM0)

end VeriStressGT.SelfAttention
