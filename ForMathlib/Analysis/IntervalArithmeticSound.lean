/-
ForMathlib candidate: soundness of interval bound propagation (IBP).  Interval
arithmetic through an affine layer and through ReLU each *contains* the true
image of the input box; hence the propagated output box contains the true output
range (T4, Gowal et al. 2018).

Status: NOT IN MATHLIB as a neural-network IBP statement; the primitives
(`Set.OrdConnected`, interval images, monotonicity of `x ↦ max 0 x`) are present.
The reusable core is the affine + ReLU containment step; the whole-network
soundness is its induction.

This lemma is doubly load-bearing: it is the theory behind the Difficulty
Profile's `unstable_frac`/`ibp_relative_gap`, AND it discharges the `(l,u)`
validity hypothesis of the exact-MILP oracle (see `../ExactMILP`, edge MILP-1).

Cross-ref: prose/ibp-relaxation-barrier-linear-regions.md §1.
-/

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace VeriStressGT.ForMathlib

/-- Per-entry lower bound: `max w 0 · l + min w 0 · u ≤ w · x` when `l ≤ x ≤ u`.
Case split on the sign of `w`; the active part uses the monotone direction. -/
private lemma ibp_term_lb (w l u x : ℝ) (hlx : l ≤ x) (hxu : x ≤ u) :
    max w 0 * l + min w 0 * u ≤ w * x := by
  rcases le_total 0 w with h | h
  · rw [max_eq_left h, min_eq_right h, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left hlx h
  · rw [max_eq_right h, min_eq_left h, zero_mul, zero_add]
    exact mul_le_mul_of_nonpos_left hxu h

/-- Per-entry upper bound: `w · x ≤ max w 0 · u + min w 0 · l` when `l ≤ x ≤ u`. -/
private lemma ibp_term_ub (w l u x : ℝ) (hlx : l ≤ x) (hxu : x ≤ u) :
    w * x ≤ max w 0 * u + min w 0 * l := by
  rcases le_total 0 w with h | h
  · rw [max_eq_left h, min_eq_right h, zero_mul, add_zero]
    exact mul_le_mul_of_nonneg_left hxu h
  · rw [max_eq_right h, min_eq_left h, zero_mul, zero_add]
    exact mul_le_mul_of_nonpos_left hlx h

/-- Sound interval for an affine map applied to a box.  With `l ≤ x ≤ u`
(componentwise) and `W` split into `W⁺ = max W 0`, `W⁻ = min W 0`, the interval
`[W⁺l + W⁻u + b, W⁺u + W⁻l + b]` contains `W x + b`. -/
theorem ibp_affine_sound
    {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (l u x : Fin n → ℝ) (hlx : ∀ j, l j ≤ x j) (hxu : ∀ j, x j ≤ u j) :
    ∀ i,
      (∑ j, (max (W i j) 0 * l j + min (W i j) 0 * u j)) + b i
        ≤ (W.mulVec x + b) i
      ∧ (W.mulVec x + b) i
        ≤ (∑ j, (max (W i j) 0 * u j + min (W i j) 0 * l j)) + b i := by
  intro i
  -- `(W *ᵥ x) i = W i ⬝ᵥ x = ∑ j, W i j * x j` by unfolding mulVec/dotProduct
  have hmv : (W.mulVec x + b) i = (∑ j, W i j * x j) + b i := rfl
  rw [hmv]
  constructor
  · gcongr with j
    exact ibp_term_lb (W i j) (l j) (u j) (x j) (hlx j) (hxu j)
  · gcongr with j
    exact ibp_term_ub (W i j) (l j) (u j) (x j) (hlx j) (hxu j)

/-- Sound interval for ReLU: `max 0 ·` is monotone, so `[max 0 l, max 0 u]`
contains `max 0 x` whenever `l ≤ x ≤ u`. -/
theorem ibp_relu_sound
    (l u x : ℝ) (hlx : l ≤ x) (hxu : x ≤ u) :
    max 0 l ≤ max 0 x ∧ max 0 x ≤ max 0 u :=
  ⟨max_le_max le_rfl hlx, max_le_max le_rfl hxu⟩

end VeriStressGT.ForMathlib
