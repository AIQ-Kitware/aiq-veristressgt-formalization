/-
ExactMILP.Basic — faithfulness of the big-M ReLU encoding, and label soundness
given an OPTIMAL solve.

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/mlp_relu/milp/exact_radius.py
Transcription: prose/exact-milp-and-npcompleteness.md.

The formalizable core is NOT "Gurobi is correct" but "the encoding is faithful":
the big-M constraints exactly characterise `z = max(0,s)` on `[l,u]`.  NP-completeness
(Katz) is cited context, not a target.  Edges MILP-1 (Rmax box validity, supplied
by `IntervalBounds`) and MILP-2 (OPTIMAL required — self-declared in the code).
-/

import Mathlib

set_option autoImplicit false

namespace VeriStressGT.ExactMILP

/--
**Big-M ReLU encoding — soundness.**
The big-M constraints
  `z ≥ 0`, `z ≥ s`, `z ≤ u·a`, `z ≤ s − l·(1−a)`,  `a ∈ {0,1}`
force `z = max 0 s`.  This is the *soundness* half of encoding faithfulness (any
feasible point carries the correct ReLU value); the *completeness* half — that
`max 0 s` is itself feasible for a suitable `a`, given `l ≤ s ≤ u` — is
`bigM_relu_complete` below.  Together they show the feasible set is exactly
`{(max 0 s, indicator)}`, which is what exact_radius.py:277–287 relies on.

Note: soundness needs only the four constraints + `a ∈ {0,1}`; the interval bounds
`l < 0 < u` (the unstable regime where the MILP spends a binary) are used only in
the completeness direction, so they are omitted here. -/
theorem bigM_relu_faithful
    (l u s z : ℝ) (a : ℝ) (ha : a = 0 ∨ a = 1)
    (h1 : 0 ≤ z) (h2 : s ≤ z) (h3 : z ≤ u * a) (h4 : z ≤ s - l * (1 - a)) :
    z = max 0 s := by
  rcases ha with ha | ha
  · -- a = 0: h3 forces z ≤ 0, with 0 ≤ z gives z = 0; and s ≤ z = 0 so max 0 s = 0
    subst ha
    rw [mul_zero] at h3
    have hz : z = 0 := le_antisymm h3 h1
    have hs : s ≤ 0 := by rw [← hz]; exact h2
    rw [hz, max_eq_left hs]
  · -- a = 1: h4 forces z ≤ s, with s ≤ z gives z = s; and 0 ≤ z = s so max 0 s = s
    subst ha
    rw [sub_self, mul_zero, sub_zero] at h4
    have hz : z = s := le_antisymm h4 h2
    have hs : 0 ≤ s := by rw [← hz]; exact h1
    rw [hz, max_eq_right hs]

/--
**Big-M ReLU encoding — completeness (feasibility of the true value).**
Given valid interval bounds `l ≤ s ≤ u`, the true ReLU value `z = max 0 s` satisfies
all four big-M constraints for a suitable `a ∈ {0,1}` (`a = 0` when `s ≤ 0`, `a = 1`
when `s ≥ 0`).  This is the direction that *uses the interval bounds*: `l ≤ s` makes
the `a = 0` branch's `z ≤ s − l` hold, and `s ≤ u` makes the `a = 1` branch's `z ≤ u`
hold.  With `bigM_relu_faithful` this pins the feasible set to the correct ReLU. -/
theorem bigM_relu_complete (l u s : ℝ) (hls : l ≤ s) (hsu : s ≤ u) :
    ∃ a : ℝ, (a = 0 ∨ a = 1) ∧ 0 ≤ max 0 s ∧ s ≤ max 0 s
      ∧ max 0 s ≤ u * a ∧ max 0 s ≤ s - l * (1 - a) := by
  rcases le_total s 0 with h | h
  · refine ⟨0, Or.inl rfl, le_max_left _ _, le_max_right _ _, ?_, ?_⟩
    · simp [max_eq_left h]
    · rw [max_eq_left h]; simp only [sub_zero, mul_one]; linarith
  · refine ⟨1, Or.inr rfl, le_max_left _ _, le_max_right _ _, ?_, ?_⟩
    · rw [max_eq_right h, mul_one]; exact hsu
    · simp [max_eq_right h]

/--
**Label soundness given OPTIMAL — geometric form.**
`advSet` is the true adversarial set (points in `E` misclassified relative to `x₀`);
`Metric.infDist x₀ advSet` is the exact robustness radius.  The MILP's `rStar` equals
this infDist *only when it solves to `OPTIMAL`* (not clamped at `Rmax`, not
`TIME_LIMIT`).  Under that premise, `ε < rStar` ⟹ **the closed `ε`-box is disjoint from
`advSet`** — i.e. the box genuinely contains no adversary and UNSAT is the correct label.

The conclusion is the geometric endpoint (via `Metric.disjoint_closedBall_of_lt_infDist`),
not merely `ε < infDist` (audit F4).  The content still lives in the premise
`hoptimal : infDist = rStar` — the edge `milp-incomplete-label` (MILP-2): `OPTIMAL` buys
the equality, `TIME_LIMIT`/`INCOMPLETE` breaks it (the code warns the label is "NOT
reliable" then); and the `milp-rmax-clamp` edge (MILP-1) is the *other* way this premise
can fail (a clamped `r* = Rmax` gives a lower bound, not the true infDist).

NOTE (audit F4b, CLOSED): `advSet` is abstract *here*, but `ExactMILP/Network.lean` ties it
to `IntervalBounds`' `Layer`/`netEval` vocabulary (`advSet net y`,
`label_sound_net_of_optimal`) and discharges the `(l,u)`-validity via `Layer.sound` in
`bigMReach_complete`. This lemma is the abstract-metric core those concrete results
specialize. -/
theorem label_sound_of_optimal
    {E : Type*} [PseudoMetricSpace E]
    (advSet : Set E) (x₀ : E) (rStar ε : ℝ)
    (hoptimal : Metric.infDist x₀ advSet = rStar)   -- OPTIMAL: exact radius, not clamped
    (hε : ε < rStar) :
    Disjoint (Metric.closedBall x₀ ε) advSet := by
  apply Metric.disjoint_closedBall_of_lt_infDist
  rw [hoptimal]; exact hε

end VeriStressGT.ExactMILP
