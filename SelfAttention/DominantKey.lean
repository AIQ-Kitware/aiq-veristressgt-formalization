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

end VeriStressGT.SelfAttention
