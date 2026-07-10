/-
ForMathlib.Analysis.SoftmaxLipschitz — softmax is ½-Lipschitz (audit F2-B, CLOSED).

This file is the *consumer* of `softmax_jacobian_opNorm_le_half` (R1, proved): it defines
`softmax` on `EuclideanSpace`, discharges R1's probability-vector hypotheses
(`softmax_nonneg`, `softmax_sum_one`), proves the softmax Fréchet derivative
`hasFDerivAt_softmax` (= `toEuclideanCLM` of the Jacobian `diag a − a aᵀ`, `a = softmax s`)
directly on `EuclideanSpace` via `hasFDerivWithinAt_piLp` + the scalar quotient rule, and
concludes `lipschitzWith_softmax : LipschitzWith ½ softmax` UNCONDITIONALLY (mean-value
inequality + R1).  No hypotheses are assumed; this is the completed F2-B result.

Math provenance of the ½ constant (tight): "Softmax is ½-Lipschitz: a tight bound across
all ℓ_p norms" (arXiv:2510.23012); the L² case is the operator-norm bound R1.
Cross-ref: prose/self-attention-lipschitz.md §1, edge SA-2.  Status: formalization.yaml.
-/

import Mathlib
import ForMathlib.Analysis.SoftmaxJacobianBound

set_option autoImplicit false
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator
open Matrix WithLp

namespace VeriStressGT.ForMathlib

variable {n : ℕ}

/-- The softmax map on Euclidean space: `softmax(s)ᵢ = exp(sᵢ) / Σⱼ exp(sⱼ)`. -/
noncomputable def softmax (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun i => Real.exp (ofLp s i) / ∑ j, Real.exp (ofLp s j))

/-- Coordinate formula (definitional, through the `toLp`/`ofLp` roundtrip). -/
theorem softmax_apply (s : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ofLp (softmax s) i = Real.exp (ofLp s i) / ∑ j, Real.exp (ofLp s j) := rfl

/-- The softmax denominator is strictly positive (needs at least one class). -/
theorem softmax_denom_pos [NeZero n] (s : EuclideanSpace ℝ (Fin n)) :
    0 < ∑ j, Real.exp (ofLp s j) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- Softmax outputs are nonnegative — the first probability-vector hypothesis of R1. -/
theorem softmax_nonneg (s : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    0 ≤ ofLp (softmax s) i := by
  rw [softmax_apply]; positivity

/-- Softmax outputs sum to one — the second probability-vector hypothesis of R1. -/
theorem softmax_sum_one [NeZero n] (s : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ofLp (softmax s) i = 1 := by
  simp_rw [softmax_apply, ← Finset.sum_div]
  exact div_self (ne_of_gt (softmax_denom_pos s))

/-- The softmax Jacobian at `softmax s` has spectral norm `≤ ½` — R1 with its
probability-vector hypotheses discharged by `softmax_nonneg` / `softmax_sum_one`.
(`softmaxJac`/`softmaxJac_mulVec` are reused from `SoftmaxJacobianBound` — audit G6.) -/
theorem softmaxJac_opNorm_le_half [NeZero n] (s : EuclideanSpace ℝ (Fin n)) :
    ‖softmaxJac (ofLp (softmax s))‖ ≤ (1 : ℝ) / 2 :=
  softmax_jacobian_opNorm_le_half _ (softmax_nonneg s) (softmax_sum_one s)

/--
**Softmax Fréchet derivative (audit F2-B `hderiv`).**
`softmax`'s derivative at `s` is `toEuclideanCLM` of its Jacobian `diag a − a aᵀ`
(`a = softmax s`).  Proved directly on `EuclideanSpace` (no `equiv` detour) via
`hasFDerivWithinAt_piLp` (coordinatewise into the `PiLp` codomain) and the scalar
quotient rule (`PiLp.hasFDerivAt_apply` + `HasFDerivAt.exp`/`.sum`/`.mul` +
`hasDerivAt_inv`); the resulting covector is matched to the Jacobian row by
`softmaxJac_mulVec` (the identity `∂ⱼ softmaxᵢ = aᵢ(δᵢⱼ − aⱼ)`). -/
theorem hasFDerivAt_softmax [NeZero n] (s : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt softmax
      (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (softmaxJac (ofLp (softmax s)))) s := by
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  rw [hasFDerivWithinAt_univ]
  -- component `x ↦ softmax x i` is defeq to `x ↦ exp (x i) * (∑ exp (x j))⁻¹`
  have hfun : (fun x : EuclideanSpace ℝ (Fin n) => softmax x i)
      = fun x : EuclideanSpace ℝ (Fin n) =>
          Real.exp (ofLp x i) * (∑ j, Real.exp (ofLp x j))⁻¹ := by
    funext x; rw [softmax_apply, div_eq_mul_inv]
  rw [hfun]
  -- calculus: quotient rule for `exp(xᵢ) · (Σ exp(xⱼ))⁻¹`
  have hN : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (ofLp x i))
      (Real.exp (ofLp s i) • EuclideanSpace.proj i) s :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := s)).exp
  have hZ : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => ∑ j, Real.exp (ofLp x j))
      (∑ j, Real.exp (ofLp s j) • EuclideanSpace.proj j) s :=
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => ((EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := s)).exp)
  have hZ0 : (∑ j, Real.exp (ofLp s j)) ≠ 0 := ne_of_gt (softmax_denom_pos s)
  have hd : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => (∑ j, Real.exp (ofLp x j))⁻¹)
      ((-((∑ j, Real.exp (ofLp s j)) ^ 2)⁻¹) •
        (∑ j, Real.exp (ofLp s j) • EuclideanSpace.proj j)) s :=
    (hasDerivAt_inv hZ0).comp_hasFDerivAt s hZ
  have hmul := hN.mul hd
  -- The Mathlib-produced covector equals the Jacobian row `∂ⱼ softmaxᵢ = aᵢ(δᵢⱼ − aⱼ)`.
  have hDeq : (PiLp.proj 2 (fun _ : Fin n => ℝ) i).comp
        (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (softmaxJac (ofLp (softmax s))))
      = Real.exp (ofLp s i) • ((-((∑ j, Real.exp (ofLp s j)) ^ 2)⁻¹) •
            (∑ j, Real.exp (ofLp s j) • EuclideanSpace.proj j))
        + (∑ j, Real.exp (ofLp s j))⁻¹ • (Real.exp (ofLp s i) • EuclideanSpace.proj i) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply,
      _root_.sum_apply, smul_eq_mul, EuclideanSpace.coe_proj, ofLp_toEuclideanCLM,
      softmaxJac_mulVec, softmax_apply, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    field_simp
    ring
  rw [hDeq]
  exact hmul

/--
**Softmax is `LipschitzWith ½` — FORMAL REDUCTION to the Fréchet derivative (audit F2-B).**

Given only that softmax's Fréchet derivative at every `s` is `toEuclideanCLM` of its
Jacobian `diag a − a aᵀ` (`a = softmax s`), softmax is `½`-Lipschitz on `EuclideanSpace`.
The proof is the mean-value inequality `lipschitzWith_of_nnnorm_fderiv_le`, with the fderiv
norm bounded by `‖toEuclideanCLM (softmaxJac a)‖ = ‖softmaxJac a‖ ≤ ½` (R1,
`softmaxJac_opNorm_le_half`).

The derivative fact is `hasFDerivAt_softmax` (proved above, directly on `EuclideanSpace`);
combined with the Jacobian spectral bound R1 (`softmaxJac_opNorm_le_half`) and the mean-
value inequality `lipschitzWith_of_nnnorm_fderiv_le`, softmax is unconditionally
`½`-Lipschitz.  The ½ constant is tight (arXiv:2510.23012).  This is the completed F2-B
consumer of `softmax_jacobian_opNorm_le_half` and the ForMathlib upstream candidate. -/
theorem lipschitzWith_softmax [NeZero n] :
    LipschitzWith (1 / 2 : ℝ≥0) (softmax (n := n)) := by
  refine lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hasFDerivAt_softmax x).differentiableAt) (fun x => ?_)
  rw [(hasFDerivAt_softmax x).fderiv]
  have hb : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (softmaxJac (ofLp (softmax x)))‖
      ≤ (1 : ℝ) / 2 := by
    rw [l2_opNorm_toEuclideanCLM]; exact softmaxJac_opNorm_le_half x
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  simpa using hb

end VeriStressGT.ForMathlib
