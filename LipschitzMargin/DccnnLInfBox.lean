/-
LipschitzMargin.DccnnLInfBox — the honest L∞-box Lipschitz-margin certificate with the
`√d` dimension factor made explicit (bridging step B4, REFERENCE-COMPARISON.md §6), and the
single-layer bridge unifying `IntervalBounds.Layer` with `LipschitzMargin.AffLayer`.

**The LM-4 seam (edge `dccnn-linf-sqrtd-metric`).**  The DCCNN Lipschitz constant
`L = σ_proj·λ^D·‖w_out‖` is a *spectral* (ℓ²→ℓ²) operator-norm chain (power iteration =
largest singular value; `netLipschitz`).  But the VNN-LIB query is an **L∞** box: every
input coordinate ranges independently over `[x₀ᵢ − ε, x₀ᵢ + ε]` (`_write_vnnlib`,
`deep_contractive_cnn.py:390-397`).  An adversary can push *all* `d` coordinates to the
corner, so the honest ℓ² perturbation radius is `‖x − x₀‖₂ = √d·ε`, and the correct
robustness threshold for an ℓ²-Lipschitz margin is

    g(x₀) > L·√d·ε.

The shipped `cert_bound = σ_proj·λ^D·2ε·‖w_out‖₁` (`deep_contractive_cnn.py:227`) uses `L·2ε`
with **no `√d`** — the `2` is an ℓ∞ *diameter* convention, not the ℓ∞→ℓ² conversion.  For
input dimension `d > 4` the honest `√d·ε` exceeds `2ε`, so the code *under*-certifies the
perturbation (margin `B` set too small) — the **unsafe** direction, a candidate false-UNSAT.
See `FINDING-dccnn-linf-sqrtd.md`.  `dccnn_robust_linf_box` is the machine-checked anchor:
the `√d` is a *derived* quantity, exactly as `Z_deviation_n2`'s `n/2` anchors the
`attn-Lattn-n4-pooling` finding.

The single-layer bridge `Layer.toAffLayer_eval` shows the concrete `IntervalBounds.Layer`
(which drives IBP/MILP on `Fin n → ℝ` with the sup metric) and the abstract `AffLayer`
(which drives the T1′ spectral chain on `EuclideanSpace`) compute the *same* map — the two
network models are one object, so the ℓ∞-box (IBP) and ℓ²-spectral (T1′) bookkeeping meet on
a shared network.
-/

import Mathlib
import LipschitzMargin.Basic
import LipschitzMargin.DeepContractiveCNN
import LipschitzMargin.DeepContractiveCNNConcrete
import IntervalBounds.Basic

set_option autoImplicit false
open scoped BigOperators NNReal
open Matrix WithLp

namespace VeriStressGT.LipschitzMargin

variable {d : ℕ}

/-- **L∞-box → ℓ² radius.**  If every coordinate of `x − x₀` has magnitude `≤ ε`, the
Euclidean distance is `≤ √d·ε` — the ℓ∞→ℓ² conversion the DCCNN certificate needs to apply a
*spectral* Lipschitz constant to the VNN-LIB L∞ box.  (Same Cauchy–Schwarz content as
`SelfAttention.euclid_dist_le_sqrt_card_mul`; restated here to keep `LipschitzMargin`
independent of the attention libraries.) -/
theorem dist_le_sqrt_dim_mul_linf (x x₀ : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ i, |ofLp x i - ofLp x₀ i| ≤ ε) : dist x x₀ ≤ Real.sqrt d * ε := by
  rw [EuclideanSpace.dist_eq,
    show Real.sqrt d * ε = Real.sqrt ((d : ℝ) * ε ^ 2) from by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hε]]
  apply Real.sqrt_le_sqrt
  calc ∑ i, dist (ofLp x i) (ofLp x₀ i) ^ 2
      ≤ ∑ _i : Fin d, ε ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        rw [Real.dist_eq]; nlinarith [h i, abs_nonneg (ofLp x i - ofLp x₀ i)]
    _ = (d : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/--
**Honest L∞-box Lipschitz-margin certificate (edge LM-4 anchor).**
For an ℓ²-Lipschitz margin `g` with constant `L` (e.g. the DCCNN product
`σ_proj·λ^D·‖w_out‖`, a spectral operator-norm chain), robustness on the VNN-LIB **L∞**
ε-box requires the dimension-corrected threshold

    g(x₀) > L·√d·ε,

because the box's worst-case ℓ² radius is `√d·ε` (`dist_le_sqrt_dim_mul_linf`).  The `√d` is
the factor the shipped `cert_bound = L·2ε` omits — for `d > 4` the code's threshold is below
this honest one (unsafe).  Reduces to `robust_of_margin_gt` at perturbation radius `√d·ε`. -/
theorem dccnn_robust_linf_box (g : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0)
    (hg : LipschitzWith L g) (x₀ : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : (L : ℝ) * (Real.sqrt d * ε) < g x₀) :
    ∀ x : EuclideanSpace ℝ (Fin d), (∀ i, |ofLp x i - ofLp x₀ i| ≤ ε) → 0 < g x :=
  fun x hx =>
    robust_of_margin_gt g L hg x₀ (Real.sqrt d * ε) hB x
      (dist_le_sqrt_dim_mul_linf x x₀ ε hε hx)

/-! ### Single-layer model bridge (B4 unification) -/

/-- Map a concrete `IntervalBounds.Layer` to a `LipschitzMargin.AffLayer` on
`EuclideanSpace`: an affine layer `x ↦ Wx + b` becomes `toEuclideanCLM W`/`toLp b` with the
identity activation; a ReLU layer becomes the identity affine part with `reluMap`. -/
noncomputable def Layer.toAffLayer {n : ℕ} :
    IntervalBounds.Layer n → AffLayer (EuclideanSpace ℝ (Fin n))
  | .affine W b =>
      { W := toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W, b := toLp 2 b, act := id,
        hact := LipschitzWith.id }
  | .relu =>
      { W := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)), b := 0, act := reluMap n,
        hact := lipschitzWith_reluMap n }

/-- **The two layer models compute the same map.**  Reading raw vectors into `EuclideanSpace`
via `toLp`, the abstract `AffLayer.map` of `Layer.toAffLayer` agrees with the concrete
`IntervalBounds.Layer.eval` — so the T1′ (spectral, `EuclideanSpace`) and IBP/MILP (sup-metric,
`Fin n → ℝ`) network formalizations are one object. -/
theorem Layer.toAffLayer_eval {n : ℕ} (L : IntervalBounds.Layer n) (x : Fin n → ℝ) :
    ofLp ((Layer.toAffLayer L).map (toLp 2 x)) = L.eval x := by
  cases L with
  | affine W b =>
    funext i
    show ofLp (toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W (toLp 2 x) + toLp 2 b) i
      = (W.mulVec x + b) i
    rfl
  | relu =>
    funext i
    simp only [Layer.toAffLayer, AffLayer.map, IntervalBounds.Layer.eval, add_zero,
      ContinuousLinearMap.id_apply, reluMap_apply]
    exact max_comm _ _

end VeriStressGT.LipschitzMargin
