# Euclidean-distance degree & distance-to-the-algebraic-boundary certification

**Primary sources:**
- Y. Alexandr, H. Duan, G. Montúfar, *Robustness Verification of Polynomial
  Neural Networks*. **arXiv:2602.06105** (the UCLA "verifier evaluation" paper
  the smoke test mixes in).
- J. Draisma, E. Horobeţ, G. Ottaviani, B. Sturmfels, R. Thomas, *The Euclidean
  Distance Degree of an Algebraic Variety*, Found. Comput. Math. 2016.
  **arXiv:1309.0049** (the foundational ED-degree theorem the paper builds on).

**Grounds:** `robust_constructions/polynomial/algebraic_boundary.py`, and the
already-banked `aiq-evaluations` card `Debug/UCLA/AlgebraicPNNVerification/…`.
This is a *different mathematical universe* from the ReLU constructions: no
Lipschitz constant, no ReLU big-M — the network is a **polynomial map** and
robustness is an **algebraic-geometry** question.

---

## 1. The setup: robustness = distance to a variety

The construction's network is the shallow **polynomial** net
`f(x) = W₂ (W₁x + b₁)^{deg} + b₂` (algebraic_boundary.py:204–211, `degree=10`).
The binary decision boundary is the real variety
`𝒱 = { x : g(x) = f₀(x) − f₁(x) = 0 }`, an algebraic hypersurface of degree
`deg`. For a point `x₀` with `g(x₀) ≠ 0`, the **exact `L?` robustness radius** is
the distance from `x₀` to `𝒱`:

> `r*(x₀) = dist(x₀, 𝒱) = min { ‖x₀ − z‖ : g(z) = 0 }`.

Certifying robustness at radius `ε` is exactly `ε < r*(x₀)` — "no boundary point
within `ε`," i.e. the class cannot flip. This reframes verification as
**computing the distance to an algebraic variety**.

## 2. The ED-degree theorem (how hard is that distance?)

> **Theorem (Draisma et al. 2016).** For a variety `𝒱`, the **Euclidean-distance
> degree** `EDdeg(𝒱)` is the number of complex critical points of the squared
> distance `z ↦ ‖x₀ − z‖²` restricted to `𝒱`, for generic `x₀`. It is an
> intrinsic invariant: it counts the candidate stationary points any exact
> nearest-point solver must consider, and there are closed formulas for it in
> terms of polar/Chern classes of `𝒱`.

The 2602.06105 paper specialises this to polynomial-network decision boundaries:
`certify a robustness radius = compute the distance to the algebraic decision
boundary`, and uses `EDdeg` as the **intrinsic complexity measure** of that
computation, with symbolic (elimination) and numerical (homotopy-continuation)
methods to find the real nearest critical point. Empirically it finds that
"lightning self-attention" boundaries have *strictly smaller* ED degree than a
generic cubic — i.e. some attention architectures are *easier* to certify exactly.

**Argument chain (why ED-degree governs cost).** The nearest point `z*∈𝒱`
satisfies the Lagrange condition `x₀ − z* ⟂ T_{z*}𝒱` (normal to the tangent
space). This is a polynomial system; its number of complex solutions is
`EDdeg(𝒱)` by Bézout-type counting on the polar variety. Exact certification =
solve that system and take the real solution of minimum norm. So `EDdeg` is a
*mathematical* hardness coordinate, the algebraic analogue of `unstable_frac`.

## 3. What the construction actually ships (the honest gap)

`algebraic_boundary.py` does **not** compute `EDdeg` or solve the critical system.
It does a **numerical surrogate** (docstring lines 4–11, `create_instance`):
1. sample boundary points `p` by 1-D root-finding along random lines
   (`sample_boundary_points`, `brentq`, line 344);
2. step off `p` along the `L∞` normal `sign(∇g)` to get `x₀` at known distance
   (`perturb_normal_linf`, line 393);
3. set `ε = ‖x₀−p‖∞ − δ'` (a hair inside the known boundary point);
4. **accept** `x₀` only if a **50-restart L-BFGS-B** search over the `ε`-box fails
   to drive `|g(z)|²` below a tolerance (`nearest_boundary_check`, line 405) —
   i.e. "no closer boundary point *found*."

So the shipped `certificate_type` is literally
`"numerical_multistart_lbfgsb_nearest_boundary_check"` (line 610), and the code is
scrupulously explicit: *"No verifier was run… accepted because the multi-start
search did not find a closer boundary point"* (line 611). The **ground truth is a
numerical non-existence claim, not the ED-degree exact distance.**

## 4. Hypotheses to scrutinize (edge candidates `ED-#`)

- **ED-1 (exact distance-to-variety → multi-start local search).** The theorem
  gives an *exact* `r*` (min over `EDdeg` critical points). The code ships a
  *local optimiser's failure to find* a closer point — a **one-sided empirical**
  claim that can be wrong if all 50 restarts miss a nearer real critical point
  (high `EDdeg` = many basins to miss). The single most load-bearing edge in this
  construction, and the exact quantity the ED-degree paper is meant to *replace*
  the surrogate with.
- **ED-2 (global boundary vs. sampled lines).** `sample_boundary_points` finds
  boundary points only along random affine lines within `[t_min,t_max]`; whole
  branches of the real variety can be missed. The chosen `p` need not be the
  *nearest* boundary point to `x₀`.
- **ED-3 (`L∞` normal step vs. true `L∞` nearest point).** Stepping along
  `sign(∇g)` gives an `L∞` displacement whose landing distance is *known*, but
  `sign(∇g)` is the `L∞` steepest direction only to first order; the true `L∞`
  distance to the curved variety can be smaller.
- **ED-4 (float32 ONNX vs. float64 oracle).** Boundary sampling and NBC run in
  float64 (`PolynomialOracle`); the exported model is float32 (line 599). At
  `deg=10` the powers amplify tiny coordinate errors — the paper's ED-degree /
  homotopy methods are partly motivated by exactly this numerical fragility.

## 5. Formalization target (Lean)

This thread is the **least ReLU-like** and the most classically mathematical.
The formalizable core is small and clean: *"if `dist(x₀,𝒱) > ε` then the `ε`-box
contains no boundary point, hence the class is constant on the box"* — a pure
metric-geometry lemma (Mathlib `Metric`/`IsClosed`), independent of how `dist` is
computed. `EDdeg` itself (polar classes, homotopy continuation) is **far** outside
current Mathlib and is *cited context*, not a target. The edge ED-1 becomes an
explicit hypothesis `dist(x₀,𝒱) > ε` whose *witness* in the code is the NBC's
non-existence result — the honest seam between "exact algebraic distance" and
"local search found nothing." Recommended: formalize the metric lemma; treat the
ED-degree machinery as the pointer to the companion paper.
