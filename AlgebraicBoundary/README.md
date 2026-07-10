# `AlgebraicBoundary` — T6

**Result:** for a polynomial net, `dist(x₀, 𝒱) > ε ⟹ robust` (class constant on
the box), where `𝒱` is the algebraic decision boundary.
**Papers:** Alexandr–Duan–Montúfar ([arXiv:2602.06105](https://arxiv.org/abs/2602.06105)); ED degree, Draisma et al. 2016 ([arXiv:1309.0049](https://arxiv.org/abs/1309.0049)).
**Prose:** [`../prose/ed-degree-polynomial-verification.md`](../prose/ed-degree-polynomial-verification.md).
**Grounds:** `polynomial.algebraic_boundary`.

Status tracked in [`../formalization.yaml`](../formalization.yaml); all **proved**.

| Declaration | File | What it claims |
|---|---|---|
| `robust_of_lt_dist_boundary` | `Basic.lean` | far-from-boundary ⟹ class constant on ball (metric + IVT; empty-boundary caveat in docstring, audit F9) |
| `robust_of_numerical_lower_bound` | `Basic.lean` | **carries edge ED-1** via premise `distHat ≤ infDist` |

We formalize the **metric core** only. The ED-degree machinery (polar classes,
homotopy continuation) that makes the exact distance *computable* is cited
context, far outside Mathlib — and is exactly what would discharge edge ED-1
(replacing the code's 50-restart local-search surrogate).
