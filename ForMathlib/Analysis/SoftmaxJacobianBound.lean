/-
ForMathlib candidate: the softmax Jacobian `diag a − a aᵀ` of a probability vector
`a` has L²-operator (spectral) norm `≤ 1/2`.  This is the seed constant of every
self-attention Lipschitz bound (T2, Kim–Papamakarios–Mnih 2021) and the
`n/4 = n·(1/2)/2` coefficient in VeriStressGT's `compute_L_attn`.

Proof route (self-adjoint operator norm = sup Rayleigh quotient):
  ‖J‖₂ = ‖toEuclideanCLM J‖ = ⨆ x, |⟪Jx,x⟫/‖x‖²|   (J Hermitian ⇒ symmetric CLM)
  ⟪Jx,x⟫ = Var_a(x) := ∑ aᵢxᵢ² − (∑ aᵢxᵢ)²          (`softmaxJac_quad`)
  0 ≤ Var_a(x) ≤ (1/2)‖x‖²                           (`sj_var_nonneg`, `sj_var_le`, Popoviciu)
so every Rayleigh quotient is in `[0, 1/2]`, hence the sup is `≤ 1/2`.

Status: NOT in Mathlib in this packaged form; a clean, self-contained linear-algebra
fact — a strong upstream candidate.

Cross-ref: prose/self-attention-lipschitz.md §1 (Fact 2), edge SA-2.
-/

import Mathlib

set_option autoImplicit false
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder
open Matrix RCLike WithLp

namespace VeriStressGT.ForMathlib

variable {n : ℕ}

/-- The softmax-Jacobian matrix `J = diag a − a aᵀ`.  Public: reused by
`SoftmaxLipschitz` (`hasFDerivAt_softmax`); the derivative-fact consumer of this file. -/
noncomputable def softmaxJac (a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal a - Matrix.of (fun i j => a i * a j)

/-- Pointwise value of `J *ᵥ v` (the softmax Jacobian's action). -/
theorem softmaxJac_mulVec (a v : Fin n → ℝ) (i : Fin n) :
    ((softmaxJac a) *ᵥ v) i = a i * v i - a i * (∑ j, a j * v j) := by
  simp only [softmaxJac, Matrix.mulVec, Matrix.sub_apply, Matrix.diagonal, Matrix.of_apply, dotProduct]
  rw [show (∑ x, ((if i = x then a i else 0) - a i * a x) * v x)
        = ∑ x, ((if i = x then a i * v x else 0) - a i * a x * v x) from by
      apply Finset.sum_congr rfl; intro x _; split_ifs <;> ring,
    Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  congr 1; apply Finset.sum_congr rfl; intro j _; ring

/-- The quadratic form `⟪Jv,v⟫ = v ⬝ᵥ (J *ᵥ v)` is the (weighted) variance of `v`. -/
private theorem softmaxJac_quad (a v : Fin n → ℝ) :
    v ⬝ᵥ ((softmaxJac a) *ᵥ v) = (∑ i, a i * (v i)^2) - (∑ i, a i * v i)^2 := by
  rw [dotProduct]
  rw [show (∑ i, v i * (softmaxJac a *ᵥ v) i)
        = ∑ i, (a i * (v i)^2 - v i * a i * (∑ j, a j * v j)) from by
      apply Finset.sum_congr rfl; intro i _; rw [softmaxJac_mulVec]; ring,
    Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_mul, pow_two]
  congr 1
  apply Finset.sum_congr rfl; intro i _; ring

/-- The variance is nonnegative:  `Var_a(v) = ∑ aᵢ (vᵢ − v̄)² ≥ 0`. -/
private theorem sj_var_nonneg (a v : Fin n → ℝ) (hnn : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    0 ≤ (∑ i, a i * (v i)^2) - (∑ i, a i * v i)^2 := by
  set S := ∑ j, a j * v j with hS
  have exp : ∑ i, a i * (v i - S)^2
      = (∑ i, a i * (v i)^2) - 2*S*(∑ i, a i * v i) + S^2 := by
    rw [Finset.sum_congr rfl (fun i _ => by ring :
        ∀ i ∈ Finset.univ, a i * (v i - S)^2
          = a i * (v i)^2 - 2*S*(a i * v i) + S^2 * a i),
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum, mul_one]
  have hSeq : (∑ i, a i * v i) = S := hS.symm
  have hnn2 : 0 ≤ ∑ i, a i * (v i - S)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hnn i) (sq_nonneg _))
  nlinarith [exp, hnn2, hSeq]

/-- Popoviciu-type bound:  `Var_a(v) ≤ (1/2) ∑ vᵢ²`. -/
private theorem sj_var_le (a v : Fin n → ℝ) (hnn : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    (∑ i, a i * (v i)^2) - (∑ i, a i * v i)^2 ≤ (1/2) * ∑ i, (v i)^2 := by
  rcases isEmpty_or_nonempty (Fin n) with he | hne
  · rw [Finset.univ_eq_empty]; simp
  · have hune : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    obtain ⟨iM, -, hM⟩ := Finset.exists_max_image Finset.univ v hune
    obtain ⟨im, -, hm⟩ := Finset.exists_min_image Finset.univ v hune
    set c := (v iM + v im) / 2 with hc
    have expand : ∑ i, a i * (v i - c)^2
        = (∑ i, a i * (v i)^2) - 2*c*(∑ i, a i * v i) + c^2 := by
      rw [Finset.sum_congr rfl (fun i _ => by ring :
          ∀ i ∈ Finset.univ, a i * (v i - c)^2
            = a i * (v i)^2 - 2*c*(a i * v i) + c^2 * a i),
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hsum, mul_one]
    have hA : (∑ i, a i * (v i)^2) - (∑ i, a i * v i)^2 ≤ ∑ i, a i * (v i - c)^2 := by
      rw [expand]; nlinarith [sq_nonneg ((∑ i, a i * v i) - c)]
    have hB : ∑ i, a i * (v i - c)^2 ≤ ((v iM - v im)/2)^2 := by
      have hle : ∑ i, a i * (v i - c)^2 ≤ ∑ i, a i * ((v iM - v im)/2)^2 := by
        apply Finset.sum_le_sum; intro i _
        apply mul_le_mul_of_nonneg_left _ (hnn i)
        have h1 : v im ≤ v i := hm i (Finset.mem_univ i)
        have h2 : v i ≤ v iM := hM i (Finset.mem_univ i)
        nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h2) (sub_nonneg.mpr h1)]
      rwa [← Finset.sum_mul, hsum, one_mul] at hle
    have hC : ((v iM - v im)/2)^2 ≤ (1/2) * ∑ i, (v i)^2 := by
      have hsq : (v iM - v im)^2 ≤ 2 * ∑ i, (v i)^2 := by
        by_cases hEq : iM = im
        · subst hEq; simp; positivity
        · have hpair : (v iM)^2 + (v im)^2 ≤ ∑ i, (v i)^2 := by
            have hsub : ∑ i ∈ ({iM, im} : Finset (Fin n)), (v i)^2 ≤ ∑ i, (v i)^2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun i _ _ => sq_nonneg _)
            rwa [Finset.sum_pair hEq] at hsub
          nlinarith [hpair, sq_nonneg (v iM + v im)]
      rw [div_pow]; nlinarith [hsq]
    linarith [hA, hB, hC]

/-- `J = diag a − a aᵀ` is Hermitian (real symmetric). -/
private theorem softmaxJac_isHermitian (a : Fin n → ℝ) : (softmaxJac a).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · -- diagonal of real entries is Hermitian
    -- FLAG(build): if `Matrix.isHermitian_diagonal` is misnamed, prove via
    -- `show (diagonal a)ᴴ = diagonal a; ext i j; simp [conjTranspose_apply, diagonal]`.
    exact Matrix.isHermitian_diagonal a
  · show (Matrix.of (fun i j => a i * a j))ᴴ = Matrix.of (fun i j => a i * a j)
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.of_apply, mul_comm]

/--
**Softmax Jacobian spectral bound.**
For a probability vector `a` (with `0 ≤ aᵢ` and `∑ aᵢ = 1`), the L²-operator norm of
`J = diag a − a aᵀ` is at most `1/2` (tight: equality at `a = (½,½)`). -/
theorem softmax_jacobian_opNorm_le_half
    (a : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    ‖Matrix.diagonal a - Matrix.of (fun i j => a i * a j)‖ ≤ (1 : ℝ) / 2 := by
  show ‖softmaxJac a‖ ≤ (1 : ℝ) / 2
  rw [← l2_opNorm_toEuclideanCLM (softmaxJac a)]
  set T := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (softmaxJac a) with hT
  -- T is a symmetric operator (J Hermitian)
  have hsym : (↑T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)).IsSymmetric := by
    intro x y
    exact isSymmetric_toEuclideanLin_iff.mpr (softmaxJac_isHermitian a) x y
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient T hsym]
  apply ciSup_le
  intro x
  -- goal: |T.rayleighQuotient x| ≤ 1/2
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0, ContinuousLinearMap.rayleighQuotient]
  · have hxsq : (0:ℝ) < ‖x‖ ^ 2 := by positivity
    -- ⟪T x, x⟫ = Var_a(ofLp x)
    have hip : (inner ℝ (T x) x : ℝ) = (ofLp x) ⬝ᵥ ((softmaxJac a) *ᵥ ofLp x) := by
      show (inner ℝ (toLp 2 ((softmaxJac a) *ᵥ ofLp x)) (toLp 2 (ofLp x)) : ℝ) = _
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
    have hvar : (T.reApplyInnerSelf x)
        = (∑ i, a i * (ofLp x i)^2) - (∑ i, a i * (ofLp x i))^2 := by
      rw [ContinuousLinearMap.reApplyInnerSelf_apply, re_to_real, hip, softmaxJac_quad]
    have hnormsq : ‖x‖ ^ 2 = ∑ i, (ofLp x i)^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl; intro i _; rw [Real.norm_eq_abs, sq_abs]
    have hsumsq : (0:ℝ) < ∑ i, (ofLp x i)^2 := hnormsq ▸ hxsq
    -- assemble: |Var / ‖x‖²| ≤ 1/2  (rayleighQuotient is defeq to reApplyInnerSelf/‖x‖²)
    show |T.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ 1 / 2
    rw [hvar, hnormsq, abs_div,
      abs_of_nonneg (sj_var_nonneg a (ofLp x) hnonneg hsum),
      abs_of_nonneg (le_of_lt hsumsq), div_le_iff₀ hsumsq]
    linarith [sj_var_le a (ofLp x) hnonneg hsum]

/-! ### Loewner-order form (Mathlib-PR-facing statements, audit AUDIT2.md G8)

The pair `0 ≤ J ∧ 2•J ≤ 1` (Loewner order) is the standard, upstream-preferred way to state
the spectral fact; the `½` operator-norm bound above is a generic C\*-corollary of it — but
*only over ℂ*: `Matrix n n ℝ` is **not** a `CStarAlgebra` in Mathlib (verified: the
`CStarAlgebra`-order↔norm bridge fails to synthesize over `ℝ`), so we keep the Rayleigh
route for the norm and add these Loewner statements as the reusable primary facts.  Both go
straight to the already-proved variance lemmas via `posSemidef_iff_dotProduct_mulVec`. -/

/-- **`0 ≤ J`** (Loewner).  The softmax Jacobian is positive semidefinite — the variance
`⟪x, Jx⟫ = Var_a(x) ≥ 0` (`sj_var_nonneg`). -/
theorem softmaxJac_posSemidef (a : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    (softmaxJac a).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨softmaxJac_isHermitian a, fun x => ?_⟩
  have hstar : star x = x := by funext i; exact star_trivial (x i)
  rw [hstar, softmaxJac_quad]
  exact sj_var_nonneg a x hnonneg hsum

/-- **`2•J ≤ 1`** (Loewner), i.e. every eigenvalue of `J` is `≤ ½` — the Popoviciu variance
bound `Var_a(x) ≤ ½‖x‖²` (`sj_var_le`).  With `softmaxJac_posSemidef` this is the pair
`0 ≤ J ∧ 2•J ≤ 1`; over a complex C\*-algebra `‖J‖ ≤ ½` would follow generically, but here
it is the Rayleigh theorem above. -/
theorem two_smul_softmaxJac_le_one (a : Fin n → ℝ) (hnonneg : ∀ i, 0 ≤ a i)
    (hsum : ∑ i, a i = 1) :
    (2 : ℝ) • softmaxJac a ≤ (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [Matrix.le_iff]
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.isHermitian_one.sub ((softmaxJac_isHermitian a).smul (IsSelfAdjoint.all 2)),
      fun x => ?_⟩
  have hstar : star x = x := by funext i; exact star_trivial (x i)
  rw [hstar, sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    softmaxJac_quad, smul_eq_mul,
    show x ⬝ᵥ x = ∑ i, (x i) ^ 2 from by
      rw [dotProduct]; apply Finset.sum_congr rfl; intro i _; rw [sq]]
  linarith [sj_var_le a x hnonneg hsum]

end VeriStressGT.ForMathlib
