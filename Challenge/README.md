# VeriStressGT formalization — challenge manifest

This repository formalizes the certificate theorems behind the UCLA **VeriStressGT**
evaluation card (the **end states**) and, in the course of proving them, produced one
reusable, Mathlib-quality package with **no existing Lean source** (verified in
[`../EXTERNAL-LEAN-SURVEY.md`](../EXTERNAL-LEAN-SURVEY.md)): the **softmax** map on
`EuclideanSpace`, its Fréchet derivative, its tight `½`-Lipschitz constant, and the
Loewner-order bounds on its Jacobian.

```
Challenge/
  MathlibCandidate/  — drop-ready upstream PRs, one folder per PR (leaf theorems only)
comparator/          — one JSON per candidate (challenge_module / solution_module / theorem_names)
```

The **VeriStressGT certificate theorems** themselves (the repo's end states) are
deliberately **not** comparator challenges: their statements are in the constructions' own
vocabulary (`FixedPatternAttn`, `advSet`, `BigMReach`, `netLipschitz`, …), and a comparator
can only certify a proof is axiom-clean — it cannot certify those definitions faithfully
model the paper. That faithfulness is a human reading task (tracked under "outside review"
in [`../formalization.yaml`](../formalization.yaml)). The comparator stays purely
Mathlib-candidate-focused.

Principles (matching the sibling [`aiq-dkps-formalization`](../../aiq-dkps-formalization) manifest):

- **Leaf theorems only.** Each challenge lists only the *leaf* (top-level) theorems — those
  not used to prove any other listed theorem. `#print axioms` on a leaf transitively
  certifies its entire proof tree, so supporting lemmas need not be listed.
- **Axiom gate.** Every listed theorem depends only on `propext, Classical.choice,
  Quot.sound` — no `sorryAx`, no custom axioms (verified by `AxiomAudit.lean` /
  `scripts/check.sh`).

---

## `MathlibCandidate/` — the upstream push

| # | Challenge | Leaf theorem(s) | Destination | Why it clears the bar |
|---|---|---|---|---|
| 01 | Softmax | `lipschitzWith_softmax`, `softmaxJac_posSemidef`, `two_smul_softmaxJac_le_one` | new `Analysis/SpecialFunctions/Softmax.lean` (+ `Analysis/Matrix/…` for the Loewner forms) | **`softmax` is absent from Mathlib** — no definition, derivative, Lipschitz constant, or Jacobian bound. `lipschitzWith_softmax` transitively certifies the softmax `HasFDerivAt` and the spectral bound `‖diag a − a aᵀ‖₂ ≤ ½` (tight, arXiv:2510.23012); the Loewner pair `0 ≤ J ∧ 2•J ≤ 1` is the maintainer-preferred spectral statement. |

**What each leaf transitively certifies** (so it need not be listed separately):

- `lipschitzWith_softmax` → `hasFDerivAt_softmax` (the softmax Fréchet derivative on
  `EuclideanSpace`, via `hasFDerivWithinAt_piLp` + the scalar quotient rule) →
  `softmaxJac_opNorm_le_half` → `softmax_jacobian_opNorm_le_half` (the spectral `½` bound via
  the self-adjoint operator-norm = sup-Rayleigh route + Popoviciu variance bound).
- `softmaxJac_posSemidef` / `two_smul_softmaxJac_le_one` → the two variance lemmas
  (`sj_var_nonneg`, `sj_var_le`) via `Matrix.posSemidef_iff_dotProduct_mulVec`.

**Packaging note (C\*-order vs ℝ).** The `½` *operator-norm* form stays the Rayleigh proof:
Mathlib's C\*-order↔norm bridge is complex-only (`Matrix n n ℝ` is not a `CStarAlgebra` —
verified in Lean), so the generic "`‖a‖ ≤ 1 ↔ a ≤ 1`" corollary does not apply over `ℝ`.
The PR should carry **both** the operator-norm form and the Loewner pair.

---

## Comparator

Each candidate has a `comparator/candidate-NN-*.json` giving the challenge module (the
`sorry`-stated Mathlib-only claim), the solution module (this project's proof), the leaf
theorem names, and the permitted axioms. Running the comparator needs the external
`landrun` / `comparator` / `lean4export` tools (see the sibling repo's
`docs/challenge/comparator-tools.md`); the `Challenge` library is intentionally **not** a
default `lake build` target.
