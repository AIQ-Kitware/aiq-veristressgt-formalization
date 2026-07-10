/-
IntervalBounds.Basic — whole-network IBP soundness over a concrete layer list, by
induction on `ForMathlib.ibp_affine_sound` + `ForMathlib.ibp_relu_sound`.

Paper: Gowal et al. 2018 (arXiv:1810.12715).  Transcription:
prose/ibp-relaxation-barrier-linear-regions.md §1.  One of the three recommended
first Lean targets: high value (feeds two consumers), pure order/monotonicity.

The network is a `List` of constant-width layers (affine or ReLU); the propagation
functions thread the box `(l, u)` and the point `x` in lockstep so soundness is a
real induction, not an assumption.
-/

import Mathlib
import ForMathlib.Analysis.IntervalArithmeticSound

set_option autoImplicit false
open scoped BigOperators
open VeriStressGT.ForMathlib

namespace VeriStressGT.IntervalBounds

/-- A constant-width layer: an affine map `x ↦ W x + b`, or an elementwise ReLU. -/
inductive Layer (n : ℕ)
  | affine (W : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
  | relu

namespace Layer

/-- Concrete forward evaluation of one layer. -/
def eval {n : ℕ} : Layer n → (Fin n → ℝ) → (Fin n → ℝ)
  | affine W b, x => W.mulVec x + b
  | relu,       x => fun i => max 0 (x i)

/-- Lower endpoint of the propagated box after one layer, given input box `[l,u]`
(the IBP rules of `ForMathlib.ibp_affine_sound` / `ibp_relu_sound`). -/
def propLower {n : ℕ} : Layer n → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  | affine W b, l, u => fun i => (∑ j, (max (W i j) 0 * l j + min (W i j) 0 * u j)) + b i
  | relu,       l, _ => fun i => max 0 (l i)

/-- Upper endpoint of the propagated box after one layer. -/
def propUpper {n : ℕ} : Layer n → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  | affine W b, l, u => fun i => (∑ j, (max (W i j) 0 * u j + min (W i j) 0 * l j)) + b i
  | relu,       _, u => fun i => max 0 (u i)

end Layer

/-- Forward evaluation of a whole network (list of layers). -/
def netEval {n : ℕ} : List (Layer n) → (Fin n → ℝ) → (Fin n → ℝ)
  | [],       x => x
  | L :: rest, x => netEval rest (L.eval x)

/-- Propagate an input box `(l,u)` through the whole network. -/
def netProp {n : ℕ} :
    List (Layer n) → (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)
  | [],       l, u => (l, u)
  | L :: rest, l, u => netProp rest (L.propLower l u) (L.propUpper l u)

/-- Single-layer soundness: propagating `[l,u]` through one layer contains
`eval`, from the per-layer `ForMathlib` containment lemmas. -/
theorem Layer.sound {n : ℕ} (L : Layer n) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    ∀ i, L.propLower l u i ≤ L.eval x i ∧ L.eval x i ≤ L.propUpper l u i := by
  intro i
  cases L with
  | affine W b => exact ibp_affine_sound W b l u x hlx hxu i
  | relu       => exact ibp_relu_sound (l i) (u i) (x i) (hlx i) (hxu i)

/--
**IBP soundness (whole network).**
If `l ≤ x ≤ u` (componentwise), then the propagated output box contains the true
output: `(netProp net l u).1 ≤ netEval net x ≤ (netProp net l u).2`.  Proved by
induction over `net`, each step a `Layer.sound` (i.e. `ForMathlib.ibp_affine_sound`
/ `ibp_relu_sound`) containment.  Non-tautological: the conclusion is a real
geometric fact about the concrete `eval`/`prop` functions above. -/
theorem ibp_network_sound {n : ℕ} (net : List (Layer n)) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    ∀ i, (netProp net l u).1 i ≤ netEval net x i
       ∧ netEval net x i ≤ (netProp net l u).2 i := by
  induction net generalizing l u x with
  | nil => intro i; exact ⟨hlx i, hxu i⟩
  | cons L rest ih =>
    have hs := L.sound l u x hlx hxu
    intro i
    exact ih (L.propLower l u) (L.propUpper l u) (L.eval x)
      (fun k => (hs k).1) (fun k => (hs k).2) i

/--
**Sufficient IBP certificate.** If the propagated lower bound of output coordinate
`i` is positive, so is the true output there — the incomplete certificate CROWN
strengthens (prose §2).  Proved directly *from* `ibp_network_sound` (no new
`sorry`): positivity transports along the containment. -/
theorem robust_of_ibp_lower_pos {n : ℕ} (net : List (Layer n)) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) (i : Fin n)
    (hpos : 0 < (netProp net l u).1 i) :
    0 < netEval net x i :=
  lt_of_lt_of_le hpos (ibp_network_sound net l u x hlx hxu i).1

/-! ### Every-stage IBP validity (audit F4b)

`ibp_network_sound` speaks only about the *final* output.  The exact-MILP encoding,
however, needs each *intermediate* pre-activation to lie inside its propagated box (that
is precisely the `l ≤ s ≤ u` premise of `ExactMILP.bigM_relu_complete`).  `netTrace` /
`netBoxes` record the whole forward trace and the whole box trace, and
`netTrace_mem_netBoxes` is the every-stage strengthening: each trace value lies in its
box.  This is the artifact that lets `Layer.sound` discharge the MILP's bounds premises;
`ExactMILP/Network.lean` consumes it in the big-M completeness induction. -/

/-- The full forward trace: the input followed by the value after every layer.
Mirrors `netEval` (whose result is `(netTrace net x).getLast`). Length `net.length + 1`. -/
def netTrace {n : ℕ} : List (Layer n) → (Fin n → ℝ) → List (Fin n → ℝ)
  | [],        x => [x]
  | L :: rest, x => x :: netTrace rest (L.eval x)

/-- The full box trace: the input box followed by the propagated box after every layer.
Mirrors `netProp` (whose result is `(netBoxes net l u).getLast`). Length `net.length + 1`. -/
def netBoxes {n : ℕ} :
    List (Layer n) → (Fin n → ℝ) → (Fin n → ℝ) → List ((Fin n → ℝ) × (Fin n → ℝ))
  | [],        l, u => [(l, u)]
  | L :: rest, l, u => (l, u) :: netBoxes rest (L.propLower l u) (L.propUpper l u)

/--
**IBP soundness, every stage (audit F4b).**
If `l ≤ x ≤ u`, then *every* value of the true forward trace lies inside the
corresponding propagated box.  The pointwise strengthening of `ibp_network_sound`: same
induction, each step a `Layer.sound` containment.  This is the standalone every-stage
record; `ExactMILP.Network.bigMReach_complete` re-runs the *same* `Layer.sound` induction
inline (threading the box through its own recursion rather than consuming this list form),
so the two are parallel witnesses of the same fact — this one exposes it as an explicit
`Forall₂` over the whole trace. -/
theorem netTrace_mem_netBoxes {n : ℕ} (net : List (Layer n)) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    List.Forall₂ (fun (v : Fin n → ℝ) (b : (Fin n → ℝ) × (Fin n → ℝ)) =>
        ∀ i, b.1 i ≤ v i ∧ v i ≤ b.2 i)
      (netTrace net x) (netBoxes net l u) := by
  induction net generalizing l u x with
  | nil => exact List.Forall₂.cons (fun i => ⟨hlx i, hxu i⟩) List.Forall₂.nil
  | cons L rest ih =>
    have hs := L.sound l u x hlx hxu
    exact List.Forall₂.cons (fun i => ⟨hlx i, hxu i⟩)
      (ih (L.propLower l u) (L.propUpper l u) (L.eval x)
        (fun k => (hs k).1) (fun k => (hs k).2))

end VeriStressGT.IntervalBounds
