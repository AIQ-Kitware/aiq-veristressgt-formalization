/-
ForMathlib.Analysis.SoftmaxTight — the softmax `½` bounds are TIGHT, as theorems
(bridging step B3, REFERENCE-COMPARISON.md §6).

`SoftmaxJacobianBound.lean` / `SoftmaxLipschitz.lean` prove `‖diag a − aaᵀ‖₂ ≤ ½` and
`LipschitzWith ½ softmax`, and the docstrings *claim* both are tight (arXiv:2510.23012).
DRSB proves its sharpness gap internally; this file matches that discipline — the
tightness is now machine-checked, which is what upstream maintainers ask for first.

Witnesses (both at the balanced two-point distribution, `n = 2`):
* `softmaxJac_opNorm_eq_half_witness` — `‖softmaxJac (½,½)‖ = ½`.  The `±1` vector
  `v = (1,−1)` is an eigenvector with eigenvalue `½` (`J v = ½ v`, since `∑ aⱼ vⱼ = 0`), so
  the operator norm attains the bound: `½ ≤ ‖J‖ ≤ ½`.
* `lipschitzWith_softmax_optimal` — no `K < ½` is a Lipschitz constant of `softmax`.  The
  Fréchet derivative at `s = 0` is `toEuclideanCLM (softmaxJac (softmax 0)) =
  toEuclideanCLM (softmaxJac (½,½))`, of norm `½`; any Lipschitz constant dominates the
  derivative norm (`HasFDerivAt.le_of_lipschitz`), so `½ ≤ K`.

Cross-ref: prose/self-attention-lipschitz.md §1; the softmax comparator candidate
(`Challenge/`) — sharpness materially strengthens the Mathlib PR.
-/

import Mathlib
import ForMathlib.Analysis.SoftmaxLipschitz

set_option autoImplicit false
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator
open Matrix WithLp

namespace VeriStressGT.ForMathlib

/-- **The softmax-Jacobian spectral bound `½` is tight.**  At the balanced two-point
distribution `a = (½,½)`, the `±1` vector `v = (1,−1)` is an eigenvector of
`J = diag a − aaᵀ` with eigenvalue `½` (the pooled mean `∑ aⱼvⱼ = 0` kills the rank-one
term), so `‖J‖₂ = ½` — equality in `softmax_jacobian_opNorm_le_half`. -/
theorem softmaxJac_opNorm_eq_half_witness :
    ‖softmaxJac (fun _ : Fin 2 => (1 / 2 : ℝ))‖ = 1 / 2 := by
  set a : Fin 2 → ℝ := fun _ => 1 / 2 with ha
  have hnn : ∀ i, 0 ≤ a i := fun _ => by norm_num
  have hsum : ∑ i, a i = 1 := by rw [Fin.sum_univ_two]; norm_num
  refine le_antisymm (softmax_jacobian_opNorm_le_half a hnn hsum) ?_
  -- eigenvector `v = (1,−1)`: `J v = ½ v`
  set v : Fin 2 → ℝ := ![1, -1] with hv
  have hJv : softmaxJac a *ᵥ v = (1 / 2 : ℝ) • v := by
    funext i
    rw [softmaxJac_mulVec]
    have hs : ∑ j, a j * v j = 0 := by rw [Fin.sum_univ_two, hv]; simp [ha]
    rw [hs, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul]
  -- pass to the operator on `EuclideanSpace`
  rw [← l2_opNorm_toEuclideanCLM (softmaxJac a)]
  set T := toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (softmaxJac a) with hT
  -- the eigenvector's norm is `√2 > 0`
  have hnormx : ‖(toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    norm_num [hv, Real.norm_eq_abs]
  have hxpos : 0 < ‖(toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ := by rw [hnormx]; positivity
  -- `T (toLp v) = ½ • toLp v`
  have hTx : T (toLp 2 v) = (1 / 2 : ℝ) • (toLp 2 v : EuclideanSpace ℝ (Fin 2)) := by
    apply (WithLp.equiv 2 (Fin 2 → ℝ)).injective
    show softmaxJac a *ᵥ ofLp (toLp 2 v) = ofLp ((1 / 2 : ℝ) • (toLp 2 v : EuclideanSpace ℝ (Fin 2)))
    rw [WithLp.ofLp_toLp, hJv]
    rfl
  -- `½‖v‖ = ‖T v‖ ≤ ‖T‖·‖v‖` ⟹ `½ ≤ ‖T‖`
  have hle : ‖T (toLp 2 v)‖ ≤ ‖T‖ * ‖(toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ := T.le_opNorm _
  rw [hTx, norm_smul, Real.norm_eq_abs, show |(1 / 2 : ℝ)| = 1 / 2 from by norm_num] at hle
  exact le_of_mul_le_mul_right hle hxpos

/-- **The softmax Lipschitz constant `½` is optimal.**  No `K < ½` is a Lipschitz constant
of `softmax` on `EuclideanSpace ℝ (Fin 2)`: the Fréchet derivative at the uniform point
`s = 0` has operator norm `½` (`hasFDerivAt_softmax` + `softmaxJac_opNorm_eq_half_witness`),
and any Lipschitz constant dominates it (`HasFDerivAt.le_of_lipschitz`).  Together with
`lipschitzWith_softmax` this pins the constant to exactly `½`. -/
theorem lipschitzWith_softmax_optimal (K : ℝ≥0) (hK : LipschitzWith K (softmax (n := 2))) :
    (1 / 2 : ℝ) ≤ K := by
  have hd := hasFDerivAt_softmax (0 : EuclideanSpace ℝ (Fin 2))
  have huniform : ofLp (softmax (0 : EuclideanSpace ℝ (Fin 2))) = fun _ : Fin 2 => (1 / 2 : ℝ) := by
    funext i
    rw [softmax_apply]
    simp only [WithLp.ofLp_zero, Pi.zero_apply, Real.exp_zero, Fin.sum_univ_two]
    norm_num
  have hnorm : ‖toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (softmaxJac (ofLp (softmax (0 : EuclideanSpace ℝ (Fin 2)))))‖ = 1 / 2 := by
    rw [l2_opNorm_toEuclideanCLM, huniform]
    exact softmaxJac_opNorm_eq_half_witness
  have hbound := hd.le_of_lipschitz hK
  rwa [hnorm] at hbound

end VeriStressGT.ForMathlib
