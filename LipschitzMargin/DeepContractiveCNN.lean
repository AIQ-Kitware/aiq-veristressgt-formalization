/-
LipschitzMargin.DeepContractiveCNN — instantiate the scalar margin certificate on
the deep contractive CNN construction.

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/cnn/deep_contractive_cnn.py
Construction: `f = fc ∘ (ReLU∘Conv)^D ∘ ReLU∘Proj`, each conv rescaled to spectral
norm `λ ∈ (0,1)`, so the global Lipschitz constant is
`L = σ_proj · λ^D · ‖w_out‖₁` (compute_true_lipschitz_bound, line 235).

This file states the specialized certificate and, crucially, carries the
`dccnn-L-power-iter` EDGE as an explicit hypothesis: the certificate needs an
*upper* bound `L̂ ≥ L`, but the shipped `L̂` from 20-step power iteration is a
*lower* bound (edges Appendix A).  Making that a named hypothesis is the honest
seam between "proved for the ideal `L`" and "shipped with `L̂`".
-/

import Mathlib
import LipschitzMargin.Basic
import ForMathlib.Analysis.OperatorNormLipschitz

set_option autoImplicit false
open scoped NNReal
open VeriStressGT.ForMathlib

namespace VeriStressGT.LipschitzMargin

/-! ### T1′ — the spectral-norm composition bound, formalized

The margin `g` in the certificates below is the read-out of a feed-forward network
`fc ∘ (ReLU∘Conv)^D ∘ ReLU∘Proj`.  This section builds that network concretely as a
list of affine-plus-`1`-Lipschitz-activation layers and proves its Lipschitz
constant is the **product of the layers' operator norms** — so the constant
`L = σ_proj · λ^D · ‖w_out‖` of `compute_true_lipschitz_bound`
(`deep_contractive_cnn.py:235`) appears in Lean as `∏ᵢ ‖Wᵢ‖₊`, not as an opaque
hypothesis.  (Constant width: the layers are self-maps of one space `E`; genuinely
heterogeneous shapes embed by zero-padding, which preserves each `‖Wᵢ‖`.) -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One feed-forward layer: an affine map `x ↦ W x + b` followed by a `1`-Lipschitz
activation (e.g. ReLU). -/
structure AffLayer (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  W : E →L[ℝ] E
  b : E
  act : E → E
  hact : LipschitzWith 1 act

/-- The function computed by one layer. -/
def AffLayer.map (L : AffLayer E) : E → E := fun x => L.act (L.W x + L.b)

/-- One layer is `‖W‖₊`-Lipschitz (activation is `1`-Lipschitz; affine part is
`‖W‖₊`-Lipschitz by `lipschitz_affine_of_opNorm`). -/
theorem AffLayer.map_lipschitz (L : AffLayer E) : LipschitzWith ‖L.W‖₊ L.map := by
  have h := L.hact.comp (lipschitz_affine_of_opNorm L.W L.b)
  rw [one_mul] at h
  exact h  -- `L.map` is defeq to `L.act ∘ (fun x => L.W x + L.b)`

/-- The whole network: the composition of the layers' maps.

Orientation note (audit AUDIT2.md G7): `foldr (· ∘ ·) id` makes the list *head* the
*outermost* map — applied *last*. So the architecture-order forward pass `x ↦ w_out(λ…(σ_proj x))`
corresponds to the list `[w_out, …, σ_proj]` (output-first). The norm product `∏ᵢ ‖Wᵢ‖₊`
is orientation-independent (multiplication commutes), so `netProd_eq` and every certificate
below hold regardless; only the *reading* of the list order differs. -/
def netMap (Ls : List (AffLayer E)) : E → E := (Ls.map AffLayer.map).foldr (· ∘ ·) id

/-- **`netLipschitz` (T1′).**  The network is Lipschitz with the *product of the
layers' operator norms* `∏ᵢ ‖Wᵢ‖₊` — via `ForMathlib.lipschitzWith_listComp`. -/
theorem netLipschitz (Ls : List (AffLayer E)) :
    LipschitzWith ((Ls.map (fun L => ‖L.W‖₊)).prod) (netMap Ls) := by
  unfold netMap
  apply lipschitzWith_listComp
  induction Ls with
  | nil => exact List.Forall₂.nil
  | cons L Ls ih => exact List.Forall₂.cons L.map_lipschitz ih

/-- The product of the layer norms equals `σ_proj · λ^D · w_out` when the norms are
exactly `[σ_proj, λ, …(D times)…, λ, w_out]` — the DCCNN normalization.  This is the
Lean form of `compute_true_lipschitz_bound`. -/
theorem netProd_eq (Ls : List (AffLayer E)) (σp lam wout : ℝ≥0) (D : ℕ)
    (hnorms : Ls.map (fun L => ‖L.W‖₊) = σp :: (List.replicate D lam ++ [wout])) :
    (Ls.map (fun L => ‖L.W‖₊)).prod = σp * lam ^ D * wout := by
  rw [hnorms]
  simp [List.prod_cons, List.prod_append, List.prod_replicate, mul_assoc]

/-- **Margin read-out is `‖φ‖₊ · ∏‖Wᵢ‖₊`-Lipschitz.**  For a bounded linear read-out
`φ` (e.g. the margin functional `v ↦ v y − v k`), the scalar margin `x ↦ φ(net x)`
is Lipschitz with `‖φ‖₊` times the network's product constant. -/
theorem dccnn_margin_lipschitz (Ls : List (AffLayer E)) (φ : E →L[ℝ] ℝ) :
    LipschitzWith (‖φ‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod) (fun x => φ (netMap Ls x)) :=
  (φ.lipschitz).comp (netLipschitz Ls)

/--
**DCCNN certificate with `L` DISCHARGED by the composition bound.**
Unlike `dccnn_robust_of_true_L` (which *assumes* `LipschitzWith L g`), here the margin
`g x = φ(net x)` and its Lipschitz constant is the *derived* product
`‖φ‖₊ · ∏ᵢ ‖Wᵢ‖₊`.  So `L = σ_proj·λ^D·‖w_out‖` (via `netProd_eq`) genuinely appears,
and the `dccnn-L-power-iter` edge premise `L ≤ L̂` (next lemma) attaches to that
product. -/
theorem dccnn_robust_via_net (Ls : List (AffLayer E)) (φ : E →L[ℝ] ℝ)
    (x₀ : E) (ε : ℝ)
    (hB : ((‖φ‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod : ℝ≥0) : ℝ) * ε < φ (netMap Ls x₀)) :
    ∀ x, dist x x₀ ≤ ε → 0 < φ (netMap Ls x) :=
  robust_of_margin_gt _ _ (dccnn_margin_lipschitz Ls φ) x₀ ε hB

/--
**The `dccnn-L-power-iter` edge, now anchored to the actual product.**
The shipped `L̂` (power-iteration) must upper-bound the *true* Lipschitz constant
`‖φ‖₊ · ∏ᵢ ‖Wᵢ‖₊`.  Since power iteration under-estimates each `‖Wᵢ‖₂` (edges
Appendix A), the shipped `L̂` does *not* satisfy `hupper` — that is the edge, now
stated against the genuine product rather than an abstract `L`. -/
theorem dccnn_robust_via_net_upper (Ls : List (AffLayer E)) (φ : E →L[ℝ] ℝ) (Lhat : ℝ≥0)
    (hupper : ‖φ‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod ≤ Lhat)
    (x₀ : E) (ε : ℝ) (hB : (Lhat : ℝ) * ε < φ (netMap Ls x₀)) :
    ∀ x, dist x x₀ ≤ ε → 0 < φ (netMap Ls x) :=
  robust_of_margin_gt _ Lhat ((dccnn_margin_lipschitz Ls φ).weaken hupper) x₀ ε hB

/--
**Deep contractive CNN certificate (idealized).**
Given the true global Lipschitz constant `L` of the margin `g` (supplied by the
spectral-norm composition bound `L = σ_proj · λ^D · ‖w_out‖₁`) and a certified
margin `B := g x₀ > L·2ε`, the instance is robust on the `L∞` `ε`-box.

The `2ε` (vs. `ε`) is the box *diameter* the code folds into `cert_bound`
(deep_contractive_cnn.py:227).  Reduces directly to `robust_of_margin_gt`. -/
theorem dccnn_robust_of_true_L
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (L : ℝ≥0) (hg : LipschitzWith L g)
    (x₀ : E) (ε : ℝ)
    (hB : (L : ℝ) * (2 * ε) < g x₀) :
    ∀ x, dist x x₀ ≤ 2 * ε → 0 < g x :=
  robust_of_margin_gt g L hg x₀ (2 * ε) hB

/--
**The `dccnn-L-power-iter` edge, as a hypothesis.**
The construction ships `L̂` (power-iteration estimate) and certifies against it.
The certificate is sound ONLY IF `L̂` is a genuine *upper* bound on the true `L`.
This theorem is deliberately stated with `hupper : L ≤ L̂` as an explicit premise
— the premise the shipped `L̂` does *not* satisfy (it is a lower bound; see
edges Appendix A).  A newcomer reading this sees exactly what must be discharged
to make the shipped instance's label a theorem. -/
theorem dccnn_robust_of_upper_bound
    {E : Type*} [PseudoMetricSpace E]
    (g : E → ℝ) (L Lhat : ℝ≥0) (hg : LipschitzWith L g) (hupper : L ≤ Lhat)
    (x₀ : E) (ε : ℝ)
    (hB : (Lhat : ℝ) * (2 * ε) < g x₀) :
    ∀ x, dist x x₀ ≤ 2 * ε → 0 < g x :=
  -- upgrade the Lipschitz constant `L ≤ L̂`, then apply the margin corollary
  robust_of_margin_gt g Lhat (hg.weaken hupper) x₀ (2 * ε) hB

end VeriStressGT.LipschitzMargin
