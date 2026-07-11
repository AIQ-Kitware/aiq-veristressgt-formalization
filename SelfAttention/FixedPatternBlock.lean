/-
SelfAttention.FixedPatternBlock — the softmax fixed-pattern construction, derived pieces
(audit F2-C).

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/attention/fixed_pattern.py
compute_L_attn (lines 56–71); transcription prose/self-attention-lipschitz.md §2.

The fixed-pattern block's sensitivity `L_attn` decomposes into three stages:
  (C.1) score deviation      Sᵢⱼ = α⟪Xᵢ, Xⱼ⟫   →  |ΔSᵢⱼ| ≤ α(2√d·ε + d·ε²) = B_S·ε
  (C.2) softmax + values     aᵢ = softmax(α·row Sᵢ), Zᵢ = Σⱼ (aᵢ)ⱼ • Vⱼ
  (C.3) aggregation          the leading coefficient of ‖ΔZ‖

This file formalizes the full three-stage derivation (audit AUDIT2.md G1):

* `score_deviation_unit` (C.1) — the bilinear inner-product perturbation bound, the same
  product-rule pattern as `linearDominance_token_bound` with `⟪·,·⟫` in place of `•`.
  Softmax-free; matches `compute_L_attn`'s `B_S` exactly.

* `FixedPatternAttn.attn_deviation` (C.2) — the softmax-row contraction
  `‖aᵢ(X) − aᵢ(X₀)‖ ≤ ½·‖ΔSᵢ‖`, the consumer of `ForMathlib.lipschitzWith_softmax`.

* `FixedPatternAttn.Z_deviation` / `Z_deviation_n2` (C.3, the assembled bound) — the
  product-rule output bound `‖ΔZᵢ‖ ≤ √n·(½ρ)·(Vmax+δV) + δV`, whose leading coefficient
  (with `ρ = √n·B_S·ε`) **is n/2** — the honest coefficient the code's `n/4` under-estimates.
  `Z_deviation_n2` exhibits the `n/2` explicitly and is the Lean anchor for the Family-A
  edge `attn-Lattn-n4-pooling`.  `pooling_leading_coeff` is the supporting arithmetic
  identity `√n·½·√n = n/2`.

The `√n` pooling uses Mathlib's `sq_sum_le_card_mul_sum_sq` (Cauchy–Schwarz / Chebyshev);
the middle value term is coefficient-free because `‖softmax row‖₁ = 1`
(`softmax_sum_one`/`softmax_nonneg`).
-/

import Mathlib
import LipschitzMargin.Basic
import ForMathlib.Analysis.SoftmaxLipschitz

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib VeriStressGT.LipschitzMargin WithLp

namespace VeriStressGT.SelfAttention

/--
**Bilinear (inner-product) perturbation bound.**
`|⟪Xᵢ,Xⱼ⟫ − ⟪X₀ᵢ,X₀ⱼ⟫| ≤ ‖ΔXᵢ‖·‖Xⱼ‖ + ‖X₀ᵢ‖·‖ΔXⱼ‖`, the two-sided product rule for a
bilinear form (Cauchy–Schwarz on each term).  This is the score-sensitivity core of the
fixed-pattern construction, and the exact analogue of `linearDominance_token_bound` with
the inner product replacing scalar multiplication. -/
theorem inner_deviation_bound {d : ℕ}
    (Xi Xj Xi0 Xj0 : EuclideanSpace ℝ (Fin d)) :
    |(inner ℝ Xi Xj : ℝ) - inner ℝ Xi0 Xj0|
      ≤ ‖Xi - Xi0‖ * ‖Xj‖ + ‖Xi0‖ * ‖Xj - Xj0‖ := by
  have hsplit : (inner ℝ Xi Xj : ℝ) - inner ℝ Xi0 Xj0
      = inner ℝ (Xi - Xi0) Xj + inner ℝ Xi0 (Xj - Xj0) := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [hsplit]
  calc |(inner ℝ (Xi - Xi0) Xj : ℝ) + inner ℝ Xi0 (Xj - Xj0)|
      ≤ |(inner ℝ (Xi - Xi0) Xj : ℝ)| + |(inner ℝ Xi0 (Xj - Xj0) : ℝ)| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (inner ℝ (Xi - Xi0) Xj : ℝ) (inner ℝ Xi0 (Xj - Xj0) : ℝ)
    _ ≤ ‖Xi - Xi0‖ * ‖Xj‖ + ‖Xi0‖ * ‖Xj - Xj0‖ :=
        add_le_add
          (by rw [← Real.norm_eq_abs]; exact norm_inner_le_norm (Xi - Xi0) Xj)
          (by rw [← Real.norm_eq_abs]; exact norm_inner_le_norm Xi0 (Xj - Xj0))

/--
**Score deviation for unit nominal tokens (C.1 = `compute_L_attn`'s `B_S`).**
With unit-norm nominal tokens (`‖X₀ᵢ‖, ‖X₀ⱼ‖ ≤ 1`, enforced by the construction) and per-
token ℓ² deviation `δ`, the score `α⟪Xᵢ,Xⱼ⟫` moves by at most `|α|(2δ + δ²)`.  With
`δ = √d·ε` this is exactly `fixed_pattern.py:63`'s `B_S·ε`, `B_S = α(2√d + εd)` — a
*deviation over the box*, not a Lipschitz constant (so no double `·ε`, audit F3). -/
theorem score_deviation_unit {d : ℕ} (α : ℝ)
    (Xi Xj Xi0 Xj0 : EuclideanSpace ℝ (Fin d)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hi : ‖Xi - Xi0‖ ≤ δ) (hj : ‖Xj - Xj0‖ ≤ δ)
    (hui : ‖Xi0‖ ≤ 1) (huj : ‖Xj0‖ ≤ 1) :
    |α * (inner ℝ Xi Xj : ℝ) - α * (inner ℝ Xi0 Xj0)| ≤ |α| * (2 * δ + δ ^ 2) := by
  have hbil := inner_deviation_bound Xi Xj Xi0 Xj0
  have hXj : ‖Xj‖ ≤ 1 + δ := by
    have heq : Xj0 + (Xj - Xj0) = Xj := by abel
    have h := norm_add_le Xj0 (Xj - Xj0)
    rw [heq] at h
    linarith
  rw [show α * (inner ℝ Xi Xj : ℝ) - α * (inner ℝ Xi0 Xj0)
        = α * ((inner ℝ Xi Xj : ℝ) - inner ℝ Xi0 Xj0) from by ring, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg α)
  calc |(inner ℝ Xi Xj : ℝ) - inner ℝ Xi0 Xj0|
      ≤ ‖Xi - Xi0‖ * ‖Xj‖ + ‖Xi0‖ * ‖Xj - Xj0‖ := hbil
    _ ≤ δ * (1 + δ) + 1 * δ := by
        apply add_le_add
        · exact mul_le_mul hi hXj (norm_nonneg _) hδ
        · exact mul_le_mul hui hj (norm_nonneg _) (by norm_num)
    _ = 2 * δ + δ ^ 2 := by ring

/--
**The honest aggregate leading coefficient is `n/2`, not `n/4` (audit F2-C.3).**
Assembling the fixed-pattern bound stage by stage — row score bound `√n·B_S·ε`
(ℓ² over `n` competitors), softmax contraction `½` (`softmax_jacobian_opNorm_le_half`),
and the ℓ¹→ℓ² value aggregation `√n` (`‖c‖₁ ≤ √n·‖c‖₂`) — the leading term of `‖ΔZ‖`
carries the coefficient

  `√n · (1/2) · √n = n/2`.

`compute_L_attn` (`fixed_pattern.py:66-70`) uses **`n/4`** on this term; the prose
(prose/self-attention-lipschitz.md §2) attributes the extra `½` to "the symmetric
attention structure" but transcribes no argument, and edge SA-2 flags the pooling as the
crux.  The suspicious numerology is that `¼ = maxₐ a(1−a)` is the *entrywise* softmax-
Jacobian bound — the spectral-vs-entrywise trap (AGENTS.md §6) — so a `¼`-seeded
derivation on UCLA's side is plausible.

If no valid halving argument exists in Kim et al. (arXiv:2006.04710) or the VeriStressGT
paper, the certified `L_attn` is ~2× too small on this term — the **unsafe** direction
(a false-UNSAT instance could ship, cushioned only by `margin_slack`).  That is exactly
the class of finding this program exists to surface: it is tracked as the new Family-A
edge `attn-Lattn-n4-pooling` (high) and should be raised with UCLA alongside the
Appendix-A power-iteration item.  This lemma records the honest coefficient the proof
actually yields, so any downstream certificate is stated with `n/2` (or carries the gap
`L_attn_code ≥ derived_bound` as an explicit hypothesis-edge), never the code's constant
on trust. -/
theorem pooling_leading_coeff (n : ℕ) :
    Real.sqrt n * (1 / 2 : ℝ) * Real.sqrt n = (n : ℝ) / 2 := by
  have h : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  linear_combination (1 / 2 : ℝ) * h

/-! ### The assembled fixed-pattern output bound (audit AUDIT2.md G1) -/

variable {n d dv : ℕ}

/-- ℓ¹ ≤ √m · (ℓ² = distance) for the coordinatewise differences of two Euclidean vectors
— Cauchy–Schwarz via Mathlib's `sq_sum_le_card_mul_sum_sq`.  This is the provenance of the
honest `√n` in the pooling coefficient. -/
private theorem l1_le_sqrt_mul_dist {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) :
    ∑ j, |ofLp u j - ofLp v j| ≤ Real.sqrt m * dist u v := by
  have hcard : ((Finset.univ : Finset (Fin m)).card : ℝ) = m := by simp
  have hsq : (∑ j, |ofLp u j - ofLp v j|) ^ 2
      ≤ (m : ℝ) * ∑ j, |ofLp u j - ofLp v j| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin m)))
      (f := fun j => |ofLp u j - ofLp v j|)
    simpa [hcard] using this
  have hdist : dist u v = Real.sqrt (∑ j, |ofLp u j - ofLp v j| ^ 2) := by
    rw [EuclideanSpace.dist_eq]; congr 1
  have h1 : (0 : ℝ) ≤ ∑ j, |ofLp u j - ofLp v j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  calc ∑ j, |ofLp u j - ofLp v j|
      = Real.sqrt ((∑ j, |ofLp u j - ofLp v j|) ^ 2) := (Real.sqrt_sq h1).symm
    _ ≤ Real.sqrt ((m : ℝ) * ∑ j, |ofLp u j - ofLp v j| ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt m * dist u v := by rw [Real.sqrt_mul (by positivity), ← hdist]

/-- Convex-combination norm bound `‖∑ⱼ cⱼ • vⱼ‖ ≤ ∑ⱼ |cⱼ|·‖vⱼ‖`. -/
private theorem norm_sum_smul_le {m dv : ℕ} (c : Fin m → ℝ)
    (v : Fin m → EuclideanSpace ℝ (Fin dv)) :
    ‖∑ j, c j • v j‖ ≤ ∑ j, |c j| * ‖v j‖ := by
  calc ‖∑ j, c j • v j‖ ≤ ∑ j, ‖c j • v j‖ := norm_sum_le _ _
    _ = ∑ j, |c j| * ‖v j‖ := by
        apply Finset.sum_congr rfl; intro j _; rw [norm_smul, Real.norm_eq_abs]

/--
**Fixed-pattern attention block.**  `score X i` is the (α-scaled) score row of token `i`;
the attention weights are `softmax` of that row, and the output is the convex combination
`Zᵢ = ∑ⱼ aᵢⱼ · Vⱼ`.  As with `GatedAttn`, the construction's engineered structure enters
only through the deviation hypotheses (`ρ`, `δV`, `Vmax`) of the theorems below. -/
structure FixedPatternAttn (n d dv : ℕ) where
  score : (Fin n → Fin d → ℝ) → Fin n → EuclideanSpace ℝ (Fin n)
  V : (Fin n → Fin d → ℝ) → Fin n → EuclideanSpace ℝ (Fin dv)

/-- Attention weights of row `i`: `softmax` of the score row. -/
noncomputable def FixedPatternAttn.attn (A : FixedPatternAttn n d dv)
    (X : Fin n → Fin d → ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  softmax (A.score X i)

/-- Output of token `i`: `Zᵢ = ∑ⱼ aᵢⱼ · Vⱼ`. -/
noncomputable def FixedPatternAttn.Z (A : FixedPatternAttn n d dv)
    (X : Fin n → Fin d → ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin dv) :=
  ∑ j, ofLp (A.attn X i) j • A.V X j

/--
**Softmax-row contraction (C.2).**  The attention-weight row moves by at most half the
score-row deviation — the direct consumer of `ForMathlib.lipschitzWith_softmax`. -/
theorem FixedPatternAttn.attn_dist_le [NeZero n] (A : FixedPatternAttn n d dv)
    (X X₀ : Fin n → Fin d → ℝ) (i : Fin n) :
    dist (A.attn X i) (A.attn X₀ i) ≤ (1 / 2 : ℝ) * ‖A.score X i - A.score X₀ i‖ := by
  have h := (lipschitzWith_softmax (n := n)).dist_le_mul (A.score X i) (A.score X₀ i)
  have h2 : dist (A.attn X i) (A.attn X₀ i)
      ≤ (1 / 2 : ℝ) * dist (A.score X i) (A.score X₀ i) := by
    simpa [FixedPatternAttn.attn] using h
  rwa [dist_eq_norm] at h2

/-- The softmax weight row is a probability vector: `∑ⱼ |aᵢⱼ| = 1`. -/
theorem FixedPatternAttn.attn_l1 [NeZero n] (A : FixedPatternAttn n d dv)
    (X : Fin n → Fin d → ℝ) (i : Fin n) :
    ∑ j, |ofLp (A.attn X i) j| = 1 := by
  rw [show (∑ j, |ofLp (A.attn X i) j|) = ∑ j, ofLp (A.attn X i) j from
    Finset.sum_congr rfl (fun j _ => abs_of_nonneg (softmax_nonneg (A.score X i) j))]
  exact softmax_sum_one (A.score X i)

/--
**Assembled output deviation (C.3, audit G1).**  From the score-row deviation `ρ`, the
value deviation `δV`, and the nominal value norm bound `Vmax`, the fixed-pattern output of
token `i` moves by at most `√n·(½ρ)·(Vmax+δV) + δV`.  The `√n` is the ℓ²→ℓ¹ pooling of the
attention weights (`l1_le_sqrt_mul_dist`); the standalone `δV` (no `n` factor) is the value
path, coefficient-free because `‖aᵢ‖₁ = 1` (`attn_l1`).  Product rule:
`ΔZᵢ = Σⱼ Δaᵢⱼ·Vⱼ + Σⱼ a₀ᵢⱼ·ΔVⱼ`. -/
theorem FixedPatternAttn.Z_deviation [NeZero n] (A : FixedPatternAttn n d dv)
    (X X₀ : Fin n → Fin d → ℝ) (i : Fin n) (ρ δV Vmax : ℝ) (hδV0 : 0 ≤ δV)
    (hρ : ‖A.score X i - A.score X₀ i‖ ≤ ρ)
    (hδV : ∀ j, ‖A.V X j - A.V X₀ j‖ ≤ δV)
    (hVmax : ∀ j, ‖A.V X₀ j‖ ≤ Vmax) :
    ‖A.Z X i - A.Z X₀ i‖ ≤ Real.sqrt n * ((1 / 2) * ρ) * (Vmax + δV) + δV := by
  have hVnn : (0 : ℝ) ≤ Vmax :=
    le_trans (norm_nonneg _) (hVmax (Classical.arbitrary (Fin n)))
  have hVδnn : (0 : ℝ) ≤ Vmax + δV := by linarith
  -- softmax-row contraction bound
  have hda : dist (A.attn X i) (A.attn X₀ i) ≤ (1 / 2) * ρ :=
    (A.attn_dist_le X X₀ i).trans (by apply mul_le_mul_of_nonneg_left hρ (by norm_num))
  -- pointwise value norm bound
  have hVb : ∀ j, ‖A.V X j‖ ≤ Vmax + δV := by
    intro j
    have heq : A.V X₀ j + (A.V X j - A.V X₀ j) = A.V X j := by abel
    have h := norm_add_le (A.V X₀ j) (A.V X j - A.V X₀ j)
    rw [heq] at h
    exact le_trans h (add_le_add (hVmax j) (hδV j))
  -- product-rule split
  have hsplit : A.Z X i - A.Z X₀ i
      = (∑ j, (ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j) • A.V X j)
        + ∑ j, ofLp (A.attn X₀ i) j • (A.V X j - A.V X₀ j) := by
    simp only [FixedPatternAttn.Z]
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; rw [sub_smul, smul_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hbound1 : ‖∑ j, (ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j) • A.V X j‖
      ≤ Real.sqrt n * ((1 / 2) * ρ) * (Vmax + δV) := by
    calc ‖∑ j, (ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j) • A.V X j‖
        ≤ ∑ j, |ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j| * ‖A.V X j‖ :=
          norm_sum_smul_le _ _
      _ ≤ ∑ j, |ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j| * (Vmax + δV) := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hVb j) (abs_nonneg _)
      _ = (∑ j, |ofLp (A.attn X i) j - ofLp (A.attn X₀ i) j|) * (Vmax + δV) := by
          rw [← Finset.sum_mul]
      _ ≤ (Real.sqrt n * dist (A.attn X i) (A.attn X₀ i)) * (Vmax + δV) :=
          mul_le_mul_of_nonneg_right (l1_le_sqrt_mul_dist _ _) hVδnn
      _ ≤ (Real.sqrt n * ((1 / 2) * ρ)) * (Vmax + δV) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hda (Real.sqrt_nonneg _)) hVδnn
  have hbound2 : ‖∑ j, ofLp (A.attn X₀ i) j • (A.V X j - A.V X₀ j)‖ ≤ δV := by
    calc ‖∑ j, ofLp (A.attn X₀ i) j • (A.V X j - A.V X₀ j)‖
        ≤ ∑ j, |ofLp (A.attn X₀ i) j| * ‖A.V X j - A.V X₀ j‖ := norm_sum_smul_le _ _
      _ ≤ ∑ j, |ofLp (A.attn X₀ i) j| * δV := by
          apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_left (hδV j) (abs_nonneg _)
      _ = (∑ j, |ofLp (A.attn X₀ i) j|) * δV := by rw [← Finset.sum_mul]
      _ = δV := by rw [A.attn_l1, one_mul]
  linarith [hbound1, hbound2]

/--
**Assembled output deviation with the `n/2` coefficient exhibited (audit G1/G2).**  The
same bound as `Z_deviation`, with the score-row deviation written in the code's form
`ρ = √n·B_S·ε`: the leading term carries **`n/2`** (`√n·½·√n = n`), the honest coefficient
that `compute_L_attn`'s `n/4` under-estimates by 2× (edge `attn-Lattn-n4-pooling`).  This
is the Lean anchor the edge claim now rests on — the derived bound, not the standalone
arithmetic identity `pooling_leading_coeff`. -/
theorem FixedPatternAttn.Z_deviation_n2 [NeZero n] (A : FixedPatternAttn n d dv)
    (X X₀ : Fin n → Fin d → ℝ) (i : Fin n) (BS ε δV Vmax : ℝ) (hδV0 : 0 ≤ δV)
    (hρ : ‖A.score X i - A.score X₀ i‖ ≤ Real.sqrt n * BS * ε)
    (hδV : ∀ j, ‖A.V X j - A.V X₀ j‖ ≤ δV)
    (hVmax : ∀ j, ‖A.V X₀ j‖ ≤ Vmax) :
    ‖A.Z X i - A.Z X₀ i‖ ≤ ((n : ℝ) / 2) * BS * ε * (Vmax + δV) + δV := by
  have h := A.Z_deviation X X₀ i (Real.sqrt n * BS * ε) δV Vmax hδV0 hρ hδV hVmax
  have hcoef : Real.sqrt n * ((1 / 2) * (Real.sqrt n * BS * ε))
      = ((n : ℝ) / 2) * BS * ε := by
    have hs : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
    linear_combination (BS * ε / 2) * hs
  rwa [hcoef] at h

/-! ### Full fixed-pattern robustness certificate (AUDIT2 §5 step 1e) -/

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

/-- The flattened fixed-pattern output over all tokens (ℓ²-aggregated). -/
noncomputable def FixedPatternAttn.zflat (A : FixedPatternAttn n d dv)
    (X : Fin n → Fin d → ℝ) : EuclideanSpace ℝ (Fin n × Fin dv) :=
  toLp 2 (fun p : Fin n × Fin dv => ofLp (A.Z X p.1) p.2)

/-- ℓ²-pooling of the per-token output deviations: `‖Δzflat‖ ≤ √n · K`. -/
theorem FixedPatternAttn.zflat_deviation [NeZero n] (A : FixedPatternAttn n d dv)
    (X X₀ : Fin n → Fin d → ℝ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i, ‖A.Z X i - A.Z X₀ i‖ ≤ K) :
    ‖A.zflat X - A.zflat X₀‖ ≤ Real.sqrt n * K := by
  rw [← dist_eq_norm, EuclideanSpace.dist_eq,
    show Real.sqrt n * K = Real.sqrt ((n : ℝ) * K ^ 2) from by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hK0]]
  apply Real.sqrt_le_sqrt
  have key : ∑ p : Fin n × Fin dv, dist (A.zflat X p) (A.zflat X₀ p) ^ 2
      = ∑ i, ‖A.Z X i - A.Z X₀ i‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro i _
    rw [← dist_eq_norm, EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
    apply Finset.sum_congr rfl; intro j _; rfl
  rw [key]
  calc ∑ i, ‖A.Z X i - A.Z X₀ i‖ ^ 2
      ≤ ∑ _i : Fin n, K ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        nlinarith [hK i, norm_nonneg (A.Z X i - A.Z X₀ i)]
    _ = (n : ℝ) * K ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Per-competitor margin of a linear head `W_head · zflat + b_head` (class `y` vs `k`). -/
noncomputable def FixedPatternAttn.margin (A : FixedPatternAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y k : Fin c) (X : Fin n → Fin d → ℝ) : ℝ :=
  (Whead (A.zflat X) + bhead) y - (Whead (A.zflat X) + bhead) k

/-- The per-token output-deviation budget `K = √m·(½ρ)·(Vmax+δV) + δV` (from `Z_deviation`,
`m` = number of tokens). -/
private noncomputable def fpK (m : ℕ) (ρ δV Vmax : ℝ) : ℝ :=
  Real.sqrt m * ((1 / 2) * ρ) * (Vmax + δV) + δV

/--
**Fixed-pattern margin deviation.**  The head bias cancels; the two competitor coordinates
each move by `≤ ‖W_head‖·‖Δzflat‖ ≤ ‖W_head‖·√n·K`, with `K` the per-token output budget
(`Z_deviation`, consuming `lipschitzWith_softmax`).  The outer `√n` is the token pooling
(matching the paper's eq. 55 `√n·L_attn·ε`). -/
theorem FixedPatternAttn.margin_deviation [NeZero n] (A : FixedPatternAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y k : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε ρ δV Vmax : ℝ) (hρ0 : 0 ≤ ρ) (hδV0 : 0 ≤ δV)
    (hVmax0 : 0 ≤ Vmax)
    (hρ : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.score X i - A.score X₀ i‖ ≤ ρ)
    (hδV : ∀ X, dist X X₀ ≤ ε → ∀ j, ‖A.V X j - A.V X₀ j‖ ≤ δV)
    (hVmax : ∀ j, ‖A.V X₀ j‖ ≤ Vmax) :
    ∀ X, dist X X₀ ≤ ε →
      |A.margin Whead bhead y k X - A.margin Whead bhead y k X₀|
        ≤ 2 * ‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax) := by
  intro X hX
  have hK0 : 0 ≤ fpK n ρ δV Vmax := by
    have : 0 ≤ Real.sqrt n * ((1 / 2) * ρ) * (Vmax + δV) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by linarith)
    simp only [fpK]; linarith
  have hKtok : ∀ i, ‖A.Z X i - A.Z X₀ i‖ ≤ fpK n ρ δV Vmax := fun i =>
    A.Z_deviation X X₀ i ρ δV Vmax hδV0 (hρ X hX i) (hδV X hX) hVmax
  set Δz := A.zflat X - A.zflat X₀ with hΔz
  have hmapY : Whead (A.zflat X) y - Whead (A.zflat X₀) y = Whead Δz y := by
    rw [hΔz, map_sub]; rfl
  have hmapK : Whead (A.zflat X) k - Whead (A.zflat X₀) k = Whead Δz k := by
    rw [hΔz, map_sub]; rfl
  have happ : ∀ (u : EuclideanSpace ℝ (Fin c)) (j : Fin c), (u + bhead) j = u j + bhead j :=
    fun _ _ => rfl
  have hdiff : A.margin Whead bhead y k X - A.margin Whead bhead y k X₀
      = Whead Δz y - Whead Δz k := by
    simp only [FixedPatternAttn.margin, happ]
    rw [← hmapY, ← hmapK]; ring
  rw [hdiff]
  have hz : ‖Δz‖ ≤ Real.sqrt n * fpK n ρ δV Vmax :=
    A.zflat_deviation X X₀ (fpK n ρ δV Vmax) hK0 hKtok
  have hop : ‖Whead Δz‖ ≤ ‖Whead‖ * ‖Δz‖ := Whead.le_opNorm Δz
  have htri : |Whead Δz y - Whead Δz k| ≤ |Whead Δz y| + |Whead Δz k| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (Whead Δz y) (Whead Δz k)
  have hznn : (0 : ℝ) ≤ Real.sqrt n * fpK n ρ δV Vmax := mul_nonneg (Real.sqrt_nonneg _) hK0
  calc |Whead Δz y - Whead Δz k|
      ≤ |Whead Δz y| + |Whead Δz k| := htri
    _ ≤ ‖Whead Δz‖ + ‖Whead Δz‖ := add_le_add (abs_apply_le_norm _ _) (abs_apply_le_norm _ _)
    _ = 2 * ‖Whead Δz‖ := by ring
    _ ≤ 2 * (‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax)) := by
        have hstep : ‖Whead‖ * ‖Δz‖ ≤ ‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax) :=
          mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        linarith [hop, hstep]
    _ = 2 * ‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax) := by ring

/--
**Fixed-pattern robustness certificate — DERIVED (AUDIT2 G1, full cert).**
From the score/value deviations (`hρ`/`hδV` = the code's `B_S·ε`/`√d·σ_V·ε` seams) and the
nominal value bound, if the nominal margin exceeds `2·‖W_head‖·√n·K` for every competitor,
then `y` wins throughout the ε-box.  NO Lipschitz constant is assumed — the softmax
contraction is derived via `lipschitzWith_softmax`.  This is the fixed-pattern analogue of
`linearDominance_robust_derived`; `K = fpK` carries the honest `n/2` pooling (`Z_deviation_n2`). -/
theorem fixedPattern_robust_derived [NeZero n] (A : FixedPatternAttn n d dv) {c : ℕ}
    (Whead : EuclideanSpace ℝ (Fin n × Fin dv) →L[ℝ] EuclideanSpace ℝ (Fin c))
    (bhead : EuclideanSpace ℝ (Fin c)) (y : Fin c)
    (X₀ : Fin n → Fin d → ℝ) (ε ρ δV Vmax : ℝ) (hρ0 : 0 ≤ ρ) (hδV0 : 0 ≤ δV)
    (hVmax0 : 0 ≤ Vmax)
    (hρ : ∀ X, dist X X₀ ≤ ε → ∀ i, ‖A.score X i - A.score X₀ i‖ ≤ ρ)
    (hδV : ∀ X, dist X X₀ ≤ ε → ∀ j, ‖A.V X j - A.V X₀ j‖ ≤ δV)
    (hVmax : ∀ j, ‖A.V X₀ j‖ ≤ Vmax)
    (hmargin : ∀ k, k ≠ y →
      2 * ‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax) < A.margin Whead bhead y k X₀) :
    ∀ X, dist X X₀ ≤ ε → ∀ k, k ≠ y → 0 < A.margin Whead bhead y k X := by
  intro X hX k hk
  refine robust_of_deviation_lt_margin (A.margin Whead bhead y k) X₀ ε
    (2 * ‖Whead‖ * (Real.sqrt n * fpK n ρ δV Vmax)) ?_ (hmargin k hk) X hX
  intro X' hX'
  exact A.margin_deviation Whead bhead y k X₀ ε ρ δV Vmax hρ0 hδV0 hVmax0 hρ hδV hVmax X' hX'

end VeriStressGT.SelfAttention
