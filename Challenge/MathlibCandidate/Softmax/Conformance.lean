/-
# Softmax: tight ½-Lipschitz + Loewner Jacobian bounds (Mathlib candidate 01)

`Conformance.lean` imports only Mathlib and states the leaf theorem(s) as `sorry`;
`Leaderboard.lean` imports the project and supplies the proofs.  Only the leaf
(top-level) theorems are listed — `#print axioms` on a leaf transitively certifies its
whole proof tree (here: the softmax Fréchet derivative `hasFDerivAt_softmax`, the spectral
Jacobian bound `softmax_jacobian_opNorm_le_half`, and the variance lemmas).

These results are **absent from Mathlib** (there is no `softmax` at all — any type, any
name — nor its derivative, Lipschitz constant, or Jacobian norm/Loewner bounds).  Verified
twice with disjoint tooling: `EXTERNAL-LEAN-SURVEY.md` (2026-07-09) and the independent
prior-art audit of 2026-07-13 (survey §10: Mathlib master rev `4a7edd35ec` grep, Loogle
statement-shape queries, LeanSearch, mathlib4 PR/issue search — all 0).  Related work, not
prior art: SciLean's `SciLean.ML.softMax` is a computational, temperature-scaled softmax
on `R^ι` whose derivative rules are commented out / `sorry_proof`-backed — no verified
softmax exists anywhere in Lean 4.  The definitions below are exactly the ones a Mathlib
PR would add; the statements are stated in pure Mathlib vocabulary.
-/
import Mathlib

set_option autoImplicit false
open scoped BigOperators NNReal Matrix Matrix.Norms.L2Operator MatrixOrder
open Matrix WithLp

namespace VeriStressGT.ForMathlib

variable {n : ℕ}

/-- The softmax map on Euclidean space: `softmax(s)ᵢ = exp(sᵢ) / Σⱼ exp(sⱼ)`. -/
noncomputable def softmax (s : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun i => Real.exp (ofLp s i) / ∑ j, Real.exp (ofLp s j))

/-- The softmax Jacobian matrix `J = diag a − a aᵀ`. -/
noncomputable def softmaxJac (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal a - Matrix.of (fun i j => a i * a j)

/-- **Softmax is `½`-Lipschitz** (tight; arXiv:2510.23012).  Leaf: transitively certifies the
softmax Fréchet derivative and the spectral Jacobian bound `‖diag a − a aᵀ‖₂ ≤ ½`. -/
theorem lipschitzWith_softmax [NeZero n] :
    LipschitzWith (1 / 2 : ℝ≥0) (softmax (n := n)) := by
  sorry

/-- **`0 ≤ J`** (Loewner): the softmax Jacobian is positive semidefinite. -/
theorem softmaxJac_posSemidef (a : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    (softmaxJac a).PosSemidef := by
  sorry

/-- **`2•J ≤ 1`** (Loewner): every eigenvalue of the softmax Jacobian is `≤ ½`. -/
theorem two_smul_softmaxJac_le_one (a : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = 1) :
    (2 : ℝ) • softmaxJac a ≤ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  sorry

end VeriStressGT.ForMathlib
