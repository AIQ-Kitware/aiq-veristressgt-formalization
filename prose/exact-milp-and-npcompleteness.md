# Exact `L∞` robustness radius via MILP (the ground-truth oracle)

**Primary sources:**
- V. Tjeng, K. Xiao, R. Tedrake, *Evaluating Robustness of Neural Networks with
  Mixed Integer Programming*, ICLR 2019. **arXiv:1711.07356**.
- G. Katz, C. Barrett, D. Dill, K. Julian, M. Kochenderfer, *Reluplex: An
  Efficient SMT Solver for Verifying Deep Neural Networks*, CAV 2017.
  **arXiv:1702.01135** (NP-completeness of exact ReLU verification).

**Grounds:** `robust_constructions/mlp_relu/milp/exact_radius.py`. Unlike the
Lipschitz constructions — which certify a *sufficient* margin and accept a
conservative radius — this one computes the **exact** minimum-adversarial-radius
`r*` and then ships the box at `ε = 0.999·r*` (UNSAT, provably robust) or
`1.001·r*` (SAT). It is the *ground-truth oracle* the whole benchmark leans on
when there is no closed-form margin.

---

## 1. The exact-verification MILP

For a ReLU MLP with affine layers `sᵢ = Wᵢ zᵢ₋₁ + bᵢ`, `zᵢ = ReLU(sᵢ)`, the
robustness query "does an adversarial `x` exist in the `L∞` `ε`-box?" is exactly
encodable as a mixed-integer **linear** program because ReLU is piecewise linear.

**ReLU big-M encoding (Tjeng et al. Eq. 5–7).** For a preactivation neuron with
sound interval bounds `l ≤ s ≤ u` (from IBP), introduce a binary `a ∈ {0,1}` and
encode `z = ReLU(s) = max(0, s)` by
```
z ≥ 0,   z ≥ s,
z ≤ u · a,               # if a=0 forces z=0 (inactive)
z ≤ s − l · (1 − a).     # if a=1 forces z=s (active)
```
This is *exact* whenever `l ≤ s ≤ u` holds — the binary picks the active/inactive
branch and the big-M constants `u, −l` make the off-branch constraints vacuous.
`build_distance_milp` (exact_radius.py:189–305) implements precisely this, with
the two stable cases short-circuited: `u ≤ 0` ⟹ `z=0` (line 264), `l ≥ 0` ⟹ `z=s`
(line 271); only **unstable** neurons (`l<0<u`) spend a binary (line 277–287).

**Exact radius as an objective.** Minimising the `L∞` radius `t` subject to a
misclassification constraint `logit_k ≥ logit_y` gives, per target class `k`, the
closest adversarial point; `r* = min_{k≠y} t_k*` (`solve_exact_radius`,
lines 308–513). Then `ε = 0.999 r*` is provably UNSAT, `1.001 r*` provably SAT.

## 2. The two theorems that make this a ground truth

> **Theorem A (soundness+completeness of the MILP).** If every hidden neuron's
> `(l,u)` bounds are **valid** (contain the true preactivation range over the
> box) and Gurobi solves the MILP to `OPTIMAL`, then `t_k*` is the *exact*
> minimum `L∞` distance to a class-`k` adversarial example. Hence the shipped
> UNSAT/SAT label is correct.

Argument: the big-M constraints are an exact disjunctive encoding of `max(0,·)`
on `[l,u]`; the feasible set of the MILP is *exactly* the set of
`(x, network(x))` with `x` in the box; minimising `t` finds the true nearest
counterexample. Validity of `(l,u)` is supplied by IBP on `[x₀−Rmax, x₀+Rmax]`
(`ibp_preact_bounds`, line 162) — see
[`ibp-relaxation-barrier-linear-regions.md`](ibp-relaxation-barrier-linear-regions.md).

> **Theorem B (Katz et al.: hardness).** Deciding `L∞` robustness of a ReLU
> network is **NP-complete**. So Theorem A's "solved to OPTIMAL" is not free: in
> the worst case the MILP has `2^{#unstable}` branches. This is *why* the
> benchmark is a meaningful stress test — and why the construction records an
> `INCOMPLETE` status (line 467) when a per-class MILP times out with a lower
> bound below the incumbent `r*`.

## 3. Hypotheses to scrutinize (edge candidates `MILP-#`)

- **MILP-1 (`Rmax` box must contain `r*`).** IBP bounds are computed on
  `[x₀−Rmax, x₀+Rmax]`; the MILP constrains `t ≤ Rmax` (line 232). If the true
  `r*` exceeds `Rmax`, the solver returns `t*=Rmax` and the code *warns* but the
  radius is a **lower bound**, not exact (lines 400, 482). Shipping `ε=0.999 r*`
  off a clamped `r*` could mislabel. Load-bearing.
- **MILP-2 (`OPTIMAL` vs. `TIME_LIMIT`/`INCOMPLETE`).** The ground-truth label is
  only sound under Theorem A's `OPTIMAL`. The code explicitly propagates an
  `INCOMPLETE` verdict and warns the label is "NOT reliable" (line 716) when a
  timed-out class has `lower_bound < r*`. **This is a self-declared edge inside
  the construction** — the cleanest example in the whole benchmark of the code
  naming its own assumption gap.
- **MILP-3 (float MILP vs. real arithmetic).** Gurobi solves in floating point
  with a `MIPGap`/feasibility tolerance; the exported ONNX is `float32`. Two
  numeric regimes (float64 parse → Gurobi → float32 ONNX → verifier) must agree
  at the `0.001·r*` margin. This is exactly the "numeric tolerance" failure the
  VeriStressGT paper reports finding in verifiers — an edge that lands on
  *tolerance*, not logic.
- **MILP-4 (parser faithfulness).** `parse_mlp_gemm_relu` (line 45) supports only
  `Gemm`/`MatMul+Add`/`Relu`/`Flatten` chains; the certificate is about the
  parsed `layers`, which must equal the exported ONNX semantics.

## 4. Formalization target (Lean)

Theorem A is a statement about an **exact disjunctive encoding**: `z = max(0,s)`
iff the four big-M constraints hold given `l ≤ s ≤ u`. That biconditional is a
finite case-split — very formalizable, no solver needed (Lean proves the
*encoding is faithful*, not that Gurobi is correct). Theorem B (NP-completeness)
is *not* a target — cite Katz et al.; the relevant formal object is the
*soundness of the label given OPTIMAL*, i.e. edge MILP-2 as an explicit
hypothesis `status = OPTIMAL ∧ Rmax_not_binding`. This mirrors how DKPS carries
"extra (implicit) assumptions beyond the paper" as named hypotheses.
