/-
ExactMILP.Network — the whole-network big-M encoding, wired to IBP box propagation
(audit F4b).

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/mlp_relu/milp/exact_radius.py
Transcription: prose/exact-milp-and-npcompleteness.md (Theorem A).

This is the file that makes `import IntervalBounds` load-bearing from the MILP side —
before it, no Lean file consumed `IntervalBounds` in the exact-radius thread.  It closes
audit F4b:

* `advSet` — the TRUE adversarial set in `IntervalBounds.Layer`/`netEval` vocabulary.
  On `Fin n → ℝ` the default `Pi` metric IS the sup (L∞) metric (`dist_pi_le_iff`), so
  `Metric.infDist x₀ (advSet net y)` is *literally* the exact L∞ robustness radius `r*`
  of `exact_radius.py`, and `Metric.closedBall x₀ ε` is the VNN-LIB ε-box.
* `robust_of_lt_infDist_advSet` / `label_sound_net_of_optimal` — the geometric
  label-soundness endpoint over the concrete set (the F4 docstring, now a Lean fact on
  `netEval`).
* `infDist_inter_closedBall_of_exists_mem_ball` — the `milp-rmax-clamp` edge as a lemma:
  a non-binding search radius does not change the infimum distance.
* `BigMReach` + `bigMReach_sound` / `bigMReach_complete` — whole-network encoding
  soundness / completeness.  Soundness is bounds-free (the big-M constraints alone pin
  `z = max 0 s`); completeness is where IBP earns its keep — its per-stage `l ≤ s ≤ u`
  premises are discharged by `IntervalBounds.Layer.sound`.  `bigM_feasible_iff_netEval`
  is the capstone (prose Theorem A minus Gurobi).
-/

import Mathlib
import IntervalBounds
import ExactMILP.Basic

set_option autoImplicit false
open scoped BigOperators

namespace VeriStressGT.ExactMILP

open VeriStressGT.IntervalBounds

variable {n : ℕ}

/-! ### F4b-1 — the true adversarial set, in the network vocabulary -/

/-- The TRUE adversarial set of `net` w.r.t. certified class `y`: inputs where some
competitor's logit reaches `y`'s.  On `Fin n → ℝ` the default `Pi` metric is the sup
(L∞) metric (`dist_pi_le_iff`), so `Metric.infDist x₀ (advSet net y)` is the exact L∞
robustness radius `r*`, and `Metric.closedBall x₀ ε` is the VNN-LIB ε-box — the whole
MILP thread lives in the correct metric for free. -/
def advSet (net : List (Layer n)) (y : Fin n) : Set (Fin n → ℝ) :=
  {x | ∃ k, k ≠ y ∧ netEval net x y ≤ netEval net x k}

/-! ### F4b-2 — geometric label soundness over the concrete set -/

/--
**Label soundness from the exact radius (geometric form, audit F4/F4b).**
If `ε` is strictly below the infimum distance to `advSet`, then no point of the closed
`ε`-box is adversarial: every competitor logit stays strictly below `y`'s throughout the
box.  This is the geometric endpoint the abstract `label_sound_of_optimal` produces as
ball-disjointness, here specialized to the concrete `netEval` adversarial set. -/
theorem robust_of_lt_infDist_advSet (net : List (Layer n))
    (x₀ : Fin n → ℝ) (y : Fin n) (ε : ℝ)
    (h : ε < Metric.infDist x₀ (advSet net y)) :
    ∀ x, dist x x₀ ≤ ε → ∀ k, k ≠ y → netEval net x k < netEval net x y := by
  intro x hx k hk
  by_contra hle
  have hmem : x ∈ advSet net y := ⟨k, hk, not_lt.mp hle⟩
  have h1 : Metric.infDist x₀ (advSet net y) ≤ dist x₀ x :=
    Metric.infDist_le_dist_of_mem hmem
  have h2 : dist x₀ x ≤ ε := by rw [dist_comm]; exact hx
  exact absurd (h1.trans h2) (not_le.mpr h)

/--
**Label soundness given OPTIMAL — concrete-set form.**
The MILP's `rStar` equals `Metric.infDist x₀ (advSet net y)` only under an OPTIMAL solve
(edge `milp-incomplete-label`); under that premise `ε < rStar` certifies UNSAT.  Content
lives in the premise `hoptimal`; this is the consumer on `IntervalBounds.netEval`. -/
theorem label_sound_net_of_optimal (net : List (Layer n))
    (x₀ : Fin n → ℝ) (y : Fin n) (rStar ε : ℝ)
    (hoptimal : Metric.infDist x₀ (advSet net y) = rStar)
    (hε : ε < rStar) :
    ∀ x, dist x x₀ ≤ ε → ∀ k, k ≠ y → netEval net x k < netEval net x y :=
  robust_of_lt_infDist_advSet net x₀ y ε (hoptimal ▸ hε)

/-! ### F4b-3 — the `milp-rmax-clamp` edge as a lemma -/

/--
**Non-binding search radius (edge `milp-rmax-clamp`).**
If some adversary lies within the search radius `R`, clamping the search to the `R`-ball
does not change the infimum distance.  This is the formal content of "the MILP's `Rmax`
was non-binding": OPTIMAL with incumbent `rStar < Rmax` supplies the witness `hy`, so the
box-restricted infimum the solver computes equals the true `r*`.  Generalizes Mathlib's
`Metric.infDist_inter_closedBall_of_mem` (fixed radius `dist y x`) to any `R ≥ dist y x₀`. -/
theorem infDist_inter_closedBall_of_exists_mem_ball
    {E : Type*} [PseudoMetricSpace E] (s : Set E) (x₀ : E) {R : ℝ}
    (hy : ∃ y ∈ s, dist y x₀ ≤ R) :
    Metric.infDist x₀ (s ∩ Metric.closedBall x₀ R) = Metric.infDist x₀ s := by
  obtain ⟨y, hys, hyR⟩ := hy
  have hymem : y ∈ s ∩ Metric.closedBall x₀ R :=
    ⟨hys, Metric.mem_closedBall.mpr hyR⟩
  refine le_antisymm ?_ ?_
  · -- infDist over the R-box ≤ infDist over s, via the exact-radius sub-ball
    have hsub_small : s ∩ Metric.closedBall x₀ (dist y x₀) ⊆ s ∩ Metric.closedBall x₀ R :=
      fun z hz => ⟨hz.1, Metric.closedBall_subset_closedBall hyR hz.2⟩
    have hne_small : (s ∩ Metric.closedBall x₀ (dist y x₀)).Nonempty :=
      ⟨y, hys, Metric.mem_closedBall.mpr le_rfl⟩
    calc Metric.infDist x₀ (s ∩ Metric.closedBall x₀ R)
        ≤ Metric.infDist x₀ (s ∩ Metric.closedBall x₀ (dist y x₀)) :=
          Metric.infDist_le_infDist_of_subset hsub_small hne_small
      _ = Metric.infDist x₀ s := Metric.infDist_inter_closedBall_of_mem hys
  · exact Metric.infDist_le_infDist_of_subset Set.inter_subset_left ⟨y, hymem⟩

/--
**INFEASIBLE verdict soundness.**
If no adversary lies in the search box, every point of any smaller box is correctly
classified.  This is the formal meaning of a Gurobi INFEASIBLE verdict and sidesteps the
`Metric.infDist ∅ = 0` artifact (audit F9) for this thread. -/
theorem robust_of_no_adv_in_ball (net : List (Layer n)) (x₀ : Fin n → ℝ) (y : Fin n)
    (Rmax ε : ℝ) (hε : ε ≤ Rmax)
    (hempty : advSet net y ∩ Metric.closedBall x₀ Rmax = ∅) :
    ∀ x, dist x x₀ ≤ ε → ∀ k, k ≠ y → netEval net x k < netEval net x y := by
  intro x hx k hk
  by_contra hle
  have hxmem : x ∈ advSet net y := ⟨k, hk, not_lt.mp hle⟩
  have hxball : x ∈ Metric.closedBall x₀ Rmax :=
    Metric.mem_closedBall.mpr (hx.trans hε)
  have hmem : x ∈ advSet net y ∩ Metric.closedBall x₀ Rmax := ⟨hxmem, hxball⟩
  rw [hempty] at hmem
  exact hmem

/-! ### F4b-5 — the whole-network big-M relation (prose Theorem A) -/

/-- `BigMReach net l u v out`: from intermediate value `v` (with propagated box `[l,u]`),
some big-M–feasible assignment of the remaining layers reaches output `out`.  Affine
layers are equality constraints (no binary choice); ReLU layers introduce the four big-M
constraints with the `Layer.propLower`/`propUpper` bounds and a binary `a ∈ {0,1}`.

Faithfulness note (vs `exact_radius.py:264-287`): the code short-circuits *stable* neurons
(`u ≤ 0 ⟹ z = 0`, `l ≥ 0 ⟹ z = s`) and spends a binary only on *unstable* ones; this
encoding spends a binary at every ReLU neuron.  The feasible sets coincide — the four
constraints force the same `z = max 0 s` regardless (that is exactly `bigM_relu_faithful`)
— so nothing is unsound; the encodings differ only in binary count. -/
def BigMReach : List (Layer n) → (Fin n → ℝ) → (Fin n → ℝ) →
    (Fin n → ℝ) → (Fin n → ℝ) → Prop
  | [],                         _, _, v, out => out = v
  | (Layer.affine W b) :: rest, l, u, v, out =>
      BigMReach rest ((Layer.affine W b).propLower l u)
        ((Layer.affine W b).propUpper l u) (W.mulVec v + b) out
  | Layer.relu :: rest,         l, u, v, out =>
      ∃ z a : Fin n → ℝ,
        (∀ i, (a i = 0 ∨ a i = 1) ∧ 0 ≤ z i ∧ v i ≤ z i
          ∧ z i ≤ u i * a i ∧ z i ≤ v i - l i * (1 - a i))
        ∧ BigMReach rest (Layer.relu.propLower l u) (Layer.relu.propUpper l u) z out

/--
**Encoding SOUNDNESS.**
Any big-M–feasible assignment computes the true network output.  Per-neuron this is
`bigM_relu_faithful`; note it needs NO bounds validity — the four constraints alone pin
`z = max 0 s`, so the induction never touches `l`, `u`. -/
theorem bigMReach_sound (net : List (Layer n)) (l u v out : Fin n → ℝ) :
    BigMReach net l u v out → out = netEval net v := by
  induction net generalizing l u v out with
  | nil => intro h; exact h
  | cons L rest ih =>
    cases L with
    | affine W b => intro h; exact ih _ _ _ _ h
    | relu =>
        intro h
        obtain ⟨z, a, hcon, hrest⟩ := h
        have hz : z = Layer.relu.eval v := by
          funext i
          obtain ⟨hai, h1, h2, h3, h4⟩ := hcon i
          exact bigM_relu_faithful (l i) (u i) (v i) (z i) (a i) hai h1 h2 h3 h4
        rw [ih _ _ _ _ hrest, hz]
        simp only [netEval]

/--
**Encoding COMPLETENESS — the F4b wiring.**
The true forward trace is big-M feasible.  The ReLU step is `bigM_relu_complete`, and its
`l ≤ s ≤ u` premises are supplied by `IntervalBounds.Layer.sound` — i.e. by IBP box
validity propagating along the induction.  This is the precise sense in which
`ibp_network_sound`/`Layer.sound` "discharges the `(l,u)` validity of the exact-MILP
oracle." -/
theorem bigMReach_complete (net : List (Layer n)) (l u x : Fin n → ℝ)
    (hlx : ∀ i, l i ≤ x i) (hxu : ∀ i, x i ≤ u i) :
    BigMReach net l u x (netEval net x) := by
  induction net generalizing l u x with
  | nil => rfl
  | cons L rest ih =>
    cases L with
    | affine W b =>
        have hs := (Layer.affine W b).sound l u x hlx hxu
        exact ih ((Layer.affine W b).propLower l u) ((Layer.affine W b).propUpper l u)
          ((Layer.affine W b).eval x) (fun i => (hs i).1) (fun i => (hs i).2)
    | relu =>
        have hs := Layer.relu.sound l u x hlx hxu
        refine ⟨fun i => max 0 (x i), fun i => if x i ≤ 0 then (0 : ℝ) else 1,
          fun i => ?_, ?_⟩
        · dsimp only
          refine ⟨?_, le_max_left _ _, le_max_right _ _, ?_, ?_⟩
          · by_cases h : x i ≤ 0 <;> simp [h]
          · by_cases h : x i ≤ 0
            · simp [if_pos h, max_eq_left h]
            · rw [if_neg h, mul_one, max_eq_right (not_le.mp h).le]; exact hxu i
          · by_cases h : x i ≤ 0
            · rw [if_pos h, max_eq_left h]; simp only [sub_zero, mul_one]; linarith [hlx i]
            · simp [if_neg h, max_eq_right (not_le.mp h).le]
        · exact ih (Layer.relu.propLower l u) (Layer.relu.propUpper l u) (Layer.relu.eval x)
            (fun i => (hs i).1) (fun i => (hs i).2)

/--
**Capstone (prose Theorem A minus Gurobi).**
Inside the search box, the big-M feasible set is *exactly* the true network map: an output
`out` is big-M reachable from `x` iff it equals `netEval net x`.  The box hypotheses come
from `dist_pi_le_iff` (default `Pi` metric = L∞).  The only remaining unformalized trust
is "Gurobi returns the true optimum of the stated MILP" plus float-vs-real arithmetic —
edges `milp-incomplete-label` and `float32-export`. -/
theorem bigM_feasible_iff_netEval (net : List (Layer n)) (x₀ : Fin n → ℝ) (R : ℝ)
    (x : Fin n → ℝ) (hx : dist x x₀ ≤ R) (out : Fin n → ℝ) :
    BigMReach net (fun i => x₀ i - R) (fun i => x₀ i + R) x out ↔ out = netEval net x := by
  have hR : 0 ≤ R := le_trans dist_nonneg hx
  have hpi := (dist_pi_le_iff hR).mp hx
  constructor
  · exact bigMReach_sound net _ _ x out
  · intro h; subst h
    refine bigMReach_complete net _ _ x (fun i => ?_) (fun i => ?_)
    · have hi := abs_le.mp (Real.dist_eq (x i) (x₀ i) ▸ hpi i); linarith [hi.1]
    · have hi := abs_le.mp (Real.dist_eq (x i) (x₀ i) ▸ hpi i); linarith [hi.2]

/--
**Feasible ∧ misclassified ⟺ genuine adversary in the box.**
Chaining the capstone with `advSet`: the MILP's feasible-and-adversarial region inside the
search box is exactly `advSet net y ∩ Metric.closedBall x₀ R`.  Together with
`label_sound_net_of_optimal` / `infDist_inter_closedBall_of_exists_mem_ball` this is the
complete formal story of the exact-radius oracle. -/
theorem bigM_adversary_iff (net : List (Layer n)) (x₀ : Fin n → ℝ) (R : ℝ) (y : Fin n)
    (x : Fin n → ℝ) (hx : dist x x₀ ≤ R) :
    (∃ out, BigMReach net (fun i => x₀ i - R) (fun i => x₀ i + R) x out
        ∧ ∃ k, k ≠ y ∧ out y ≤ out k)
      ↔ x ∈ advSet net y := by
  constructor
  · rintro ⟨out, hreach, k, hk, hle⟩
    rw [(bigM_feasible_iff_netEval net x₀ R x hx out).mp hreach] at hle
    exact ⟨k, hk, hle⟩
  · rintro ⟨k, hk, hle⟩
    exact ⟨netEval net x, (bigM_feasible_iff_netEval net x₀ R x hx _).mpr rfl, k, hk, hle⟩

end VeriStressGT.ExactMILP
