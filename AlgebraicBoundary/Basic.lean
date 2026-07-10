/-
AlgebraicBoundary.Basic — the metric core of polynomial-network robustness.

Empirical code:
ta1/VeriStressGT/src/VeriStressGT/robust_constructions/polynomial/algebraic_boundary.py
Transcription: prose/ed-degree-polynomial-verification.md.

Formalizable core: a pure metric-geometry lemma — `dist(x₀, 𝒱) > ε` ⟹ the class
is constant on the box.  The ED-degree machinery (polar classes, homotopy
continuation) that makes the exact distance COMPUTABLE is cited context, far
outside Mathlib.  Edge ED-1: the code ships a numerical multi-start "found no
closer boundary point", NOT the exact distance — so the `dist > ε` hypothesis is
witnessed empirically, not proved.
-/

import Mathlib

set_option autoImplicit false

namespace VeriStressGT.AlgebraicBoundary

/--
**Class label constant on the box when `x₀` is far from the boundary.**
Let `g : E → ℝ` be the (continuous) margin, `𝒱 = g⁻¹{0}` the decision boundary
(closed since `g` continuous).  If `g x₀ > 0` and `ε < dist(x₀, 𝒱)`, then `g > 0`
on the whole closed `ε`-ball: no boundary point is reachable, so the class cannot
flip.  Uses `Metric.disjoint_closedBall_of_lt_infDist` (Mathlib) — the ball misses
`𝒱` — plus connectedness/IVT of `g` on the ball (a sign change would force a zero
in the ball, contradicting disjointness).

NOTE (audit F9): Mathlib sets `Metric.infDist x₀ ∅ = 0`, so on the *trivially robust*
case where `g` has no zeros at all (`g ⁻¹' {0} = ∅`) the hypothesis `ε < infDist`
becomes `ε < 0` and the lemma is inapplicable — precisely where robustness is easiest.
Read `hdist` as "the boundary is nonempty and farther than `ε`", not "infinitely far".
For the UCLA use the decision boundaries are nonempty, so this is harmless. -/
theorem robust_of_lt_dist_boundary
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : Continuous g)
    (x₀ : E) (hx₀ : 0 < g x₀) (ε : ℝ)
    (hdist : ε < Metric.infDist x₀ (g ⁻¹' {0})) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x := by
  intro x hx
  by_contra hgx
  rw [not_lt] at hgx                                -- hgx : g x ≤ 0
  have hε : 0 ≤ ε := dist_nonneg.trans hx
  -- the closed ε-ball is convex, hence preconnected
  set s := Metric.closedBall x₀ ε with hs_def
  have hpre : IsPreconnected s := (convex_closedBall x₀ ε).isPreconnected
  have hx₀s : x₀ ∈ s := Metric.mem_closedBall_self hε
  have hxs : x ∈ s := Metric.mem_closedBall.mpr hx
  -- IVT: 0 ∈ [g x, g x₀] ⊆ g '' s, so g hits 0 somewhere in the ball
  have hsub : Set.Icc (g x) (g x₀) ⊆ g '' s :=
    hpre.intermediate_value hxs hx₀s hg.continuousOn
  obtain ⟨z, hzs, hgz⟩ := hsub ⟨hgx, hx₀.le⟩        -- 0 ∈ Icc (g x) (g x₀)
  -- z is a boundary point (g z = 0) inside the ball, contradicting ε < infDist
  have hz0 : z ∈ g ⁻¹' {0} := by simp [Set.mem_preimage, hgz]
  have h1 : Metric.infDist x₀ (g ⁻¹' {0}) ≤ dist x₀ z :=
    Metric.infDist_le_dist_of_mem hz0
  have h2 : dist x₀ z ≤ ε := by rw [dist_comm]; exact Metric.mem_closedBall.mp hzs
  linarith

/--
**The ED-1 edge, as a hypothesis.**
The construction accepts an instance when a 50-restart local search fails to find
a boundary point within `ε` (`nearest_boundary_check`).  That establishes a
*numerical lower bound* `distHat` on `dist(x₀,𝒱)`, NOT the exact ED distance.  The
label is sound iff `distHat ≤ dist(x₀,𝒱)` — an under-estimate hypothesis the
multi-start search does not prove (it could miss a nearer real critical point;
edge ED-1).  arXiv:2602.06105's exact ED-degree method is what would discharge it. -/
theorem robust_of_numerical_lower_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (hg : Continuous g) (x₀ : E) (hx₀ : 0 < g x₀)
    (ε distHat : ℝ)
    (hlb : distHat ≤ Metric.infDist x₀ (g ⁻¹' {0}))   -- the UNPROVEN premise (ED-1)
    (hε : ε < distHat) :
    ∀ x, dist x x₀ ≤ ε → 0 < g x :=
  -- transports `ε < distHat ≤ infDist` into the metric certificate
  robust_of_lt_dist_boundary g hg x₀ hx₀ ε (lt_of_lt_of_le hε hlb)

end VeriStressGT.AlgebraicBoundary
