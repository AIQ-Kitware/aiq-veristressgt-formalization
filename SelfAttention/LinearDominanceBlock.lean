/-
SelfAttention.LinearDominanceBlock — the DERIVED linear-dominance certificate (audit F2,
linear construction).

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/linear_dominance.py

`LinearDominance.lean` proves the margin step *assuming* a total-deviation bound on the
margin.  This file closes the gap: it models the diagonal gated-linear block and DERIVES
that deviation bound from the block's own intermediate quantities — the per-token gate
deviation `Δw` (= code `dw`) and value deviation `ΔV` (= code `dV`), aggregated through
the `√n` token pooling and the head operator norm `L_h = ‖W_head‖`.  The result,
`linearDominance_robust_derived`, has NO assumed Lipschitz constant: the only seams are
`hw`/`hV`/`hB`, which are exactly the numbers `linear_dominance.py:189-197` computes.

Key faithfulness points (audit F3): every hypothesis is a *deviation over the ε-box*, so
`ε` is already inside `Δw`/`ΔV`/`Bmax` and never multiplied again.  The certificate
condition `m(X₀) > 2·L_h·√n·B_max` (line 206) carries no spurious `ε` factor.
-/

import Mathlib
import LipschitzMargin.Basic
import SelfAttention.LinearDominance

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.LipschitzMargin WithLp

namespace VeriStressGT.SelfAttention

variable {n d dv : ℕ}

/-- A single coordinate of a Euclidean vector is bounded by its norm. -/
private theorem abs_apply_le_norm {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (j : ι) : |v j| ≤ ‖v‖ := by
  have h : ‖v j‖ ≤ ‖v‖ := by
    rw [EuclideanSpace.norm_eq,
      show ‖v j‖ = Real.sqrt (‖v j‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rwa [Real.norm_eq_abs] at h

/--
**Diagonal gated-linear attention.**  Per-token output `Z i = w(X) i • V(X) i` with an
arbitrary scalar gate `w` and value map `V`.  The construction's engineered structure
enters only through the deviation hypotheses (`Δw`, `ΔV`) of the theorems below — the
block itself is modelled abstractly (audit F2's "assume the code's intermediate
quantities, derive everything downstream"). -/
structure GatedAttn (n d dv : ℕ) where
  w : (Fin n → Fin d → ℝ) → Fin n → ℝ
  V : (Fin n → Fin d → ℝ) → Fin n → EuclideanSpace ℝ (Fin dv)

/-- Per-token output `Z i = w(X) i • V(X) i`. -/
def GatedAttn.Z (A : GatedAttn n d dv) (X : Fin n → Fin d → ℝ) (i : Fin n) :
    EuclideanSpace ℝ (Fin dv) := A.w X i • A.V X i

/-- The flattened head-input vector `zflat X (i,j) = (Z i)ⱼ`, in the ℓ²-aggregated space
`EuclideanSpace ℝ (Fin n × Fin dv)` — the concatenation the head matrix acts on. -/
def GatedAttn.zflat (A : GatedAttn n d dv) (X : Fin n → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin n × Fin dv) := toLp 2 (fun p : Fin n × Fin dv => A.Z X p.1 p.2)

/--
**Per-token deviation** — where `linearDominance_token_bound` is finally consumed.
Given the code's gate/value deviation bounds `Δw`/`ΔV` over the ε-box and the per-token
budget `hB` (`Bmax := maxᵢ Bᵢ`, `linear_dominance.py:192-197`), every token output moves
by at most `Bmax`. -/
theorem token_deviation (A : GatedAttn n d dv) (X₀ : Fin n → Fin d → ℝ)
    (ε Δw ΔV Bmax : ℝ)
    (hw : ∀ X, dist X X₀ ≤ ε → ∀ i, |A.w X i - A.w X₀ i| ≤ Δw)
    (hV : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.V X i - A.V X₀ i‖ ≤ ΔV)
    (hB : ∀ i, Δw * (‖A.V X₀ i‖ + ΔV) + |A.w X₀ i| * ΔV ≤ Bmax) :
    ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.Z X i - A.Z X₀ i‖ ≤ Bmax :=
  fun X hX i =>
    (linearDominance_token_bound _ _ _ _ _ _ (hw X hX i) (hV X hX i)).trans (hB i)

/--
**Aggregate deviation** — the `√n` token pooling.  The ℓ²-concatenated head input moves by
at most `√n · Bmax` over the box (each of `n` tokens moves by `≤ Bmax`, aggregated in
ℓ²).  This is the honest source of the `√n` in the certificate constant. -/
theorem zflat_deviation (A : GatedAttn n d dv) (X₀ : Fin n → Fin d → ℝ)
    (ε Δw ΔV Bmax : ℝ) (hBmax : 0 ≤ Bmax)
    (hw : ∀ X, dist X X₀ ≤ ε → ∀ i, |A.w X i - A.w X₀ i| ≤ Δw)
    (hV : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.V X i - A.V X₀ i‖ ≤ ΔV)
    (hB : ∀ i, Δw * (‖A.V X₀ i‖ + ΔV) + |A.w X₀ i| * ΔV ≤ Bmax) :
    ∀ X, dist X X₀ ≤ ε → ‖A.zflat X - A.zflat X₀‖ ≤ Real.sqrt n * Bmax := by
  intro X hX
  have htok := token_deviation A X₀ ε Δw ΔV Bmax hw hV hB X hX
  -- Work through `dist`/`EuclideanSpace.dist_eq` to avoid PiLp subtraction-indexing.
  rw [← dist_eq_norm, EuclideanSpace.dist_eq,
    show Real.sqrt n * Bmax = Real.sqrt ((n : ℝ) * Bmax ^ 2) from by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hBmax]]
  apply Real.sqrt_le_sqrt
  have key : ∑ p : Fin n × Fin dv, dist (A.zflat X p) (A.zflat X₀ p) ^ 2
      = ∑ i, ‖A.Z X i - A.Z X₀ i‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [← dist_eq_norm, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
    apply Finset.sum_congr rfl; intro j _; rfl
  rw [key]
  calc ∑ i, ‖A.Z X i - A.Z X₀ i‖ ^ 2
      ≤ ∑ _i : Fin n, Bmax ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        nlinarith [htok i, norm_nonneg (A.Z X i - A.Z X₀ i)]
    _ = (n : ℝ) * Bmax ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The per-competitor margin of a linear head `W_head · zflat + b_head` (class `y` vs
`k`).  `L_h := ‖W_head‖` is the head's operator norm. -/
def GatedAttn.margin (A : GatedAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y k : Fin c) (X : Fin n → Fin d → ℝ) : ℝ :=
  (Whead (A.zflat X) + bhead) y - (Whead (A.zflat X) + bhead) k

/--
**Margin deviation.**  The head bias cancels in the difference; the two competitor
coordinates each move by at most `‖W_head‖·‖Δzflat‖`, so the margin moves by at most
`2·‖W_head‖·√n·Bmax`.  This is the `hdev` hypothesis of `robust_of_deviation_lt_margin`,
now DERIVED (not assumed as a Lipschitz constant — audit F2/F3). -/
theorem margin_deviation (A : GatedAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y k : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε Δw ΔV Bmax : ℝ) (hBmax : 0 ≤ Bmax)
    (hw : ∀ X, dist X X₀ ≤ ε → ∀ i, |A.w X i - A.w X₀ i| ≤ Δw)
    (hV : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.V X i - A.V X₀ i‖ ≤ ΔV)
    (hB : ∀ i, Δw * (‖A.V X₀ i‖ + ΔV) + |A.w X₀ i| * ΔV ≤ Bmax) :
    ∀ X, dist X X₀ ≤ ε →
      |A.margin Whead bhead y k X - A.margin Whead bhead y k X₀|
        ≤ 2 * ‖Whead‖ * (Real.sqrt n * Bmax) := by
  intro X hX
  set Δz := A.zflat X - A.zflat X₀ with hΔz
  have hmapY : Whead (A.zflat X) y - Whead (A.zflat X₀) y = Whead Δz y := by
    rw [hΔz, map_sub]; rfl
  have hmapK : Whead (A.zflat X) k - Whead (A.zflat X₀) k = Whead Δz k := by
    rw [hΔz, map_sub]; rfl
  have happ : ∀ (u : EuclideanSpace ℝ (Fin c)) (j : Fin c), (u + bhead) j = u j + bhead j :=
    fun _ _ => rfl
  have hdiff : A.margin Whead bhead y k X - A.margin Whead bhead y k X₀
      = Whead Δz y - Whead Δz k := by
    simp only [GatedAttn.margin, happ]
    rw [← hmapY, ← hmapK]; ring
  rw [hdiff]
  have hz : ‖Δz‖ ≤ Real.sqrt n * Bmax :=
    zflat_deviation A X₀ ε Δw ΔV Bmax hBmax hw hV hB X hX
  have hop : ‖Whead Δz‖ ≤ ‖Whead‖ * ‖Δz‖ := Whead.le_opNorm Δz
  have hcoordY : |Whead Δz y| ≤ ‖Whead Δz‖ := abs_apply_le_norm _ _
  have hcoordK : |Whead Δz k| ≤ ‖Whead Δz‖ := abs_apply_le_norm _ _
  have htri : |Whead Δz y - Whead Δz k| ≤ |Whead Δz y| + |Whead Δz k| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (Whead Δz y) (Whead Δz k)
  have hznn : (0 : ℝ) ≤ Real.sqrt n * Bmax := mul_nonneg (Real.sqrt_nonneg _) hBmax
  calc |Whead Δz y - Whead Δz k|
      ≤ |Whead Δz y| + |Whead Δz k| := htri
    _ ≤ ‖Whead Δz‖ + ‖Whead Δz‖ := add_le_add hcoordY hcoordK
    _ = 2 * ‖Whead Δz‖ := by ring
    _ ≤ 2 * (‖Whead‖ * (Real.sqrt n * Bmax)) := by
        have hstep : ‖Whead‖ * ‖Δz‖ ≤ ‖Whead‖ * (Real.sqrt n * Bmax) :=
          mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        linarith [hop, hstep]
    _ = 2 * ‖Whead‖ * (Real.sqrt n * Bmax) := by ring

/--
**Linear-dominance certificate — DERIVED (audit F2, linear case).**
From the per-token gate/value deviations (`hw`/`hV` = code `dw`/`dV`) and the budget
`hB` (= code `B_max`), if the nominal margin exceeds `2·L_h·√n·B_max` for every
competitor, then `y` wins throughout the ε-box.  The margin condition is exactly
`linear_dominance.py:206` and carries **no** `ε` factor (audit F3); NO Lipschitz constant
is assumed — the deviation is derived by `margin_deviation`. -/
theorem linearDominance_robust_derived (A : GatedAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε Δw ΔV Bmax : ℝ) (hBmax : 0 ≤ Bmax)
    (hw : ∀ X, dist X X₀ ≤ ε → ∀ i, |A.w X i - A.w X₀ i| ≤ Δw)
    (hV : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.V X i - A.V X₀ i‖ ≤ ΔV)
    (hB : ∀ i, Δw * (‖A.V X₀ i‖ + ΔV) + |A.w X₀ i| * ΔV ≤ Bmax)
    (hmargin : ∀ k, k ≠ y →
      2 * ‖Whead‖ * (Real.sqrt n * Bmax) < A.margin Whead bhead y k X₀) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y → 0 < A.margin Whead bhead y k X := by
  intro X hX k hk
  refine robust_of_deviation_lt_margin (A.margin Whead bhead y k) X₀ ε
    (2 * ‖Whead‖ * (Real.sqrt n * Bmax)) ?_ (hmargin k hk) X hX
  intro X' hX'
  exact margin_deviation A Whead bhead y k X₀ ε Δw ΔV Bmax hBmax hw hV hB X' hX'

end VeriStressGT.SelfAttention
