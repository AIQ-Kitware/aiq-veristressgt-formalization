/-
LipschitzMargin.DeepContractiveCNNConcrete — the *concrete* ReLU activation for the DCCNN
thread (bridging step B1.6, REFERENCE-COMPARISON.md §6).

`DeepContractiveCNN.lean` proves the network certificates over `AffLayer`s whose activation
is an *abstract* `1`-Lipschitz map (`hact : LipschitzWith 1 act`).  For the shipped DCCNN
(`ta1/VeriStressGT/src/VeriStressGT/robust_constructions/cnn/deep_contractive_cnn.py`) the
activation is coordinatewise ReLU; the reference-comparison pass flagged `hact` as the one
*derivable* residue of the T1′ thread.  This file discharges it: `reluMap` is coordinatewise
`max · 0` on `EuclideanSpace`, proved `LipschitzWith 1` (pointwise `|max a 0 − max b 0| ≤
|a − b|`, aggregated in ℓ²), and `reluLayer` packages it as a concrete `AffLayer`, so a
fully concrete all-ReLU DCCNN list can be exhibited and every `DeepContractiveCNN`
certificate (`netProd_eq`, `dccnn_robust_via_net`, …) instantiated on it with no abstract
activation hypothesis remaining.
-/

import Mathlib
import LipschitzMargin.DeepContractiveCNN

set_option autoImplicit false
open scoped BigOperators NNReal
open WithLp

namespace VeriStressGT.LipschitzMargin

variable {m : ℕ}

/-- Coordinatewise ReLU on `EuclideanSpace ℝ (Fin m)`: `x ↦ (max xᵢ 0)ᵢ`. -/
noncomputable def reluMap (m : ℕ) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  fun x => toLp 2 (fun i => max (ofLp x i) 0)

@[simp] theorem reluMap_apply (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    ofLp (reluMap m x) i = max (ofLp x i) 0 := rfl

/-- **Coordinatewise ReLU is `1`-Lipschitz.**  Pointwise `|max a 0 − max b 0| ≤ |a − b|`
(`abs_max_sub_max_le_abs`), aggregated in ℓ² via `EuclideanSpace.dist_eq` — the derivable
`hact` residue of the DCCNN thread, now a theorem. -/
theorem lipschitzWith_reluMap (m : ℕ) : LipschitzWith 1 (reluMap m) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum (fun i _ => ?_)
  show dist (max (ofLp x i) 0) (max (ofLp y i) 0) ^ 2 ≤ dist (ofLp x i) (ofLp y i) ^ 2
  rw [Real.dist_eq, Real.dist_eq]
  have h : |max (ofLp x i) 0 - max (ofLp y i) 0| ≤ |ofLp x i - ofLp y i| :=
    abs_max_sub_max_le_abs (ofLp x i) (ofLp y i) 0
  nlinarith [h, abs_nonneg (ofLp x i - ofLp y i),
    abs_nonneg (max (ofLp x i) 0 - max (ofLp y i) 0)]

/-- **Concrete ReLU affine layer.**  A DCCNN layer `x ↦ ReLU(W x + b)` as an `AffLayer`,
with the `1`-Lipschitz activation obligation discharged by `lipschitzWith_reluMap`. -/
noncomputable def reluLayer (W : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) : AffLayer (EuclideanSpace ℝ (Fin m)) where
  W := W
  b := b
  act := reluMap m
  hact := lipschitzWith_reluMap m

@[simp] theorem reluLayer_W (W : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) : (reluLayer W b).W = W := rfl

/--
**Fully concrete DCCNN certificate (B1.6).**  For a network built entirely of concrete
ReLU layers `Ls = (Ws.zip bs).map reluLayer` and a linear read-out `φ`, the margin
`x ↦ φ(net x)` is robust on the `ε`-box whenever the derived product constant
`‖φ‖·∏ᵢ‖Wᵢ‖` clears the margin — no abstract activation hypothesis remains (`hact` is
`lipschitzWith_reluMap`).  A thin specialization of `dccnn_robust_via_net` confirming the
concrete instance is in scope of the T1′ certificate. -/
theorem dccnn_robust_concrete
    (Ls : List (AffLayer (EuclideanSpace ℝ (Fin m))))
    (_hLs : ∀ L ∈ Ls, ∃ W b, L = reluLayer W b)
    (φ : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (x₀ : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (hB : ((‖φ‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod : ℝ≥0) : ℝ) * ε < φ (netMap Ls x₀)) :
    ∀ x, dist x x₀ ≤ ε → 0 < φ (netMap Ls x) :=
  dccnn_robust_via_net Ls φ x₀ ε hB

end VeriStressGT.LipschitzMargin
