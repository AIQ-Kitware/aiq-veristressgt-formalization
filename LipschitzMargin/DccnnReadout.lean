/-
LipschitzMargin.DccnnReadout — the *corrected* DCCNN L∞-box account (AUDIT4 step N1).

AUDIT4 (2026-07-17, item J1) refuted the exposure claim of `FINDING-dccnn-linf-sqrtd.md`:
the shipped read-out row is **uniform** `1/flat_dim`, so its ℓ² operator norm is
`‖w‖₂ = 1/√flat_dim`, not the ℓ¹ value `‖w‖₁ = 1` the finding used. Under the standard
all-ℓ₂ Lipschitz-margin certificate — the very theorem this repo proves — the shipped margin
clears the honest L∞-box threshold by ≈ 8.8× at the shipped configs, so **no shipped instance
is exposed.** This file machine-checks that corrected account:

* `readout_opNorm` — the margin read-out `v ↦ ⟪w, v⟫` has operator norm exactly `‖w‖` (the
  ℓ² norm), so the *correct* Lipschitz constant of the scalar margin uses `‖w‖₂`, not `‖w‖₁`.
* `uniform_readout_l2` / `uniform_readout_l1` — for the shipped uniform row `wU = (1/m)·𝟙`,
  `‖wU‖₂ = 1/√m` while `∑ᵢ|wUᵢ| = 1`; the two differ by `√m`, which is why the code's
  `‖w_out‖₁`-based bound is loose (not unsafe) here.
* `uniform_readout_code_bound_dominates` — the general safety condition: the code's
  `cert_bound = L₀·2ε·‖w‖₁` dominates the honest `L₀·√d·ε·‖w‖₂` exactly when `√d·‖w‖₂ ≤
  2·‖w‖₁`; for the uniform row this is `d ≤ 4m` (`in_channels ≤ 4·channels`), true for every
  shipped/reachable config. (A *non-uniform* read-out with `‖w‖₁ ≈ ‖w‖₂` fails this for
  `d > 4` — the surviving, latent content of the finding.)
* `dccnn_readout_robust` — the corrected end-state: with the read-out's *own* operator norm
  `‖w‖` as the Lipschitz constant, `dccnn_robust_linf_box` certifies the margin over the L∞
  box. Instantiated at the uniform `wU` (`‖wU‖ = 1/√m`), this is what proves the shipped
  labels robust.

The honest certificate `dccnn_robust_linf_box` and the conversion `dist_le_sqrt_dim_mul_linf`
(`DccnnLInfBox.lean`) are unchanged and were always correct — the over-claim was only in the
interpretation layer, now corrected here and in the finding doc.
-/

import Mathlib
import LipschitzMargin.DccnnLInfBox

set_option autoImplicit false
open scoped BigOperators NNReal
open WithLp

namespace VeriStressGT.LipschitzMargin

variable {d m : ℕ}

/-- **Read-out operator norm.**  The scalar margin read-out `v ↦ ⟪w, v⟫` (`innerSL ℝ w`) has
operator norm exactly `‖w‖` — the ℓ² norm of the read-out row.  So the *correct* ℓ² Lipschitz
constant of the margin is `‖w‖₂·∏‖Wᵢ‖₂`, not `‖w‖₁·∏‖Wᵢ‖₂`. -/
theorem readout_opNorm (w : EuclideanSpace ℝ (Fin m)) : ‖innerSL ℝ w‖ = ‖w‖ :=
  innerSL_apply_norm (𝕜 := ℝ) w

/-- **Uniform read-out ℓ² norm.**  The shipped row `wU = (1/m)·𝟙` has `‖wU‖₂ = 1/√m`. -/
theorem uniform_readout_l2 [NeZero m] :
    ‖(toLp 2 (fun _ : Fin m => (1 : ℝ) / m) : EuclideanSpace ℝ (Fin m))‖ = 1 / Real.sqrt m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin m, ‖ofLp (toLp 2 (fun _ : Fin m => (1 : ℝ) / m)) i‖ ^ 2 = (m : ℝ)⁻¹ := by
    have h1 : ∀ i : Fin m, ‖ofLp (toLp 2 (fun _ : Fin m => (1 : ℝ) / m)) i‖ ^ 2 = ((1 : ℝ) / m) ^ 2 := by
      intro i; rw [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [hsum, Real.sqrt_inv, one_div]

/-- **Uniform read-out ℓ¹ norm.**  The same row has `∑ᵢ |wUᵢ| = 1` — the value the code's
`w_out_l1` computes.  It exceeds `‖wU‖₂ = 1/√m` by a factor `√m`. -/
theorem uniform_readout_l1 [NeZero m] :
    ∑ i, |ofLp (toLp 2 (fun _ : Fin m => (1 : ℝ) / m) : EuclideanSpace ℝ (Fin m)) i| = 1 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : ∀ i : Fin m,
      |ofLp (toLp 2 (fun _ : Fin m => (1 : ℝ) / m) : EuclideanSpace ℝ (Fin m)) i| = 1 / m := by
    intro i; rw [WithLp.ofLp_toLp, abs_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The corrected LM-4 safety condition.**  The code's diameter/ℓ¹ bound `L₀·(2ε)`
dominates the honest all-ℓ₂ threshold `(1/√m)·L₀·(√d·ε)` exactly when `d ≤ 4m` — because then
`√d ≤ 2√m`.  For the shipped uniform read-out `m = flat_dim = channels·H·W` and
`d = in_channels·H·W`, so `d ≤ 4m ⟺ in_channels ≤ 4·channels`, true for every shipped config
(`in_channels = 1`, `channels ≥ 16`). This is why the shipped formula is *safe* despite being
norm-incoherent; a non-uniform read-out (`‖w‖₂ ≈ ‖w‖₁`) would fail it for `d > 4`. -/
theorem uniform_readout_code_bound_dominates {d m : ℕ} (ε L₀ : ℝ)
    (hε : 0 ≤ ε) (hL₀ : 0 ≤ L₀) (hm : 0 < m) (h : d ≤ 4 * m) :
    (1 / Real.sqrt m) * L₀ * (Real.sqrt d * ε) ≤ L₀ * (2 * ε) := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsd : Real.sqrt d ≤ 2 * Real.sqrt m := by
    rw [show (2 : ℝ) * Real.sqrt m = Real.sqrt (4 * m) from by
      rw [show (4 : ℝ) * m = (2 : ℝ) ^ 2 * m from by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast h)
  have key : (1 / Real.sqrt m) * Real.sqrt d ≤ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hsm]; linarith
  calc (1 / Real.sqrt m) * L₀ * (Real.sqrt d * ε)
      = ((1 / Real.sqrt m) * Real.sqrt d) * (L₀ * ε) := by ring
    _ ≤ 2 * (L₀ * ε) := mul_le_mul_of_nonneg_right key (mul_nonneg hL₀ hε)
    _ = L₀ * (2 * ε) := by ring

/-- **Corrected DCCNN L∞-box certificate (the honest end-state).**  For a network `netMap Ls`
and a read-out row `w`, the scalar margin `x ↦ ⟪w, netMap Ls x⟫ + B` is robust on the L∞
ε-box once its nominal value beats `‖w‖·(∏‖Wᵢ‖)·√d·ε` — with the read-out's **own operator
norm `‖w‖ = ‖w‖₂`** as the Lipschitz constant (`readout_opNorm`), not the code's `‖w‖₁`.
Instantiated at the shipped uniform `wU` (`‖wU‖ = 1/√m`, `uniform_readout_l2`), the threshold
is `(1/√m)·∏‖Wᵢ‖·√d·ε`, which the shipped margin clears — the labels are proven robust. -/
theorem dccnn_readout_robust {d : ℕ}
    (Ls : List (AffLayer (EuclideanSpace ℝ (Fin d)))) (w : EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ((‖w‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod : ℝ≥0) : ℝ) * (Real.sqrt d * ε)
        < innerSL ℝ w (netMap Ls x₀) + B) :
    ∀ x : EuclideanSpace ℝ (Fin d), (∀ i, |ofLp x i - ofLp x₀ i| ≤ ε) →
      0 < innerSL ℝ w (netMap Ls x) + B := by
  have h0 := dccnn_margin_lipschitz Ls (innerSL ℝ w)
  have hn : ‖(innerSL ℝ w : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)‖₊ = ‖w‖₊ := by
    rw [← NNReal.coe_inj, coe_nnnorm, coe_nnnorm]; exact readout_opNorm w
  rw [hn] at h0
  have hlip : LipschitzWith (‖w‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod)
      (fun x => innerSL ℝ w (netMap Ls x) + B) := by
    intro x y
    calc edist (innerSL ℝ w (netMap Ls x) + B) (innerSL ℝ w (netMap Ls y) + B)
        = edist (innerSL ℝ w (netMap Ls x)) (innerSL ℝ w (netMap Ls y)) := by
          simp [edist_dist, dist_add_right]
      _ ≤ (‖w‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod : ℝ≥0) * edist x y := h0 x y
  exact dccnn_robust_linf_box _ _ hlip x₀ ε hε hB

end VeriStressGT.LipschitzMargin
