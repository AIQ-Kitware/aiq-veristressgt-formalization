# `ForMathlib` — Mathlib-staging candidates (VeriStressGT thread)

Paper-agnostic results the robustness-certificate libraries depend on, restated in
Mathlib idiom — the potential upstream contributions. One file per proposed
destination path, mirroring `aiq-dkps-formalization/ForMathlib`.

**Status:** all statements here are **proved** (zero `sorry`); central status in
[`../formalization.yaml`](../formalization.yaml). The `[status]` column records upstream
disposition: whether the result is a genuine Mathlib candidate or a short corollary of
existing API.

| File | Statement | Used by | Upstream status |
|---|---|---|---|
| `Analysis/OperatorNormLipschitz.lean` | `lipschitz_affine_of_opNorm` (`LipschitzWith ‖W‖₊ (W·+b)`) + `abs_apply_le_norm` (coordinate ≤ L²-norm) | LipschitzMargin (`netLipschitz`), SelfAttention | affine bound = **corollary**; the product-of-constants composition is Mathlib's `LipschitzWith.list_prod` (prior-art pass removed the redundant local `lipschitzWith_listComp`; `netLipschitz` calls the upstream lemma directly) |
| `Analysis/SoftmaxJacobianBound.lean` | `‖diag a − a aᵀ‖ ≤ 1/2` (**L²-operator norm**, Rayleigh) + Loewner forms `softmaxJac_posSemidef` (`0 ≤ J`) & `two_smul_softmaxJac_le_one` (`2•J ≤ 1`) | SelfAttention/FixedPattern, SoftmaxLipschitz | **strong Mathlib candidate** — Loewner pair is the PR-preferred primary statement; norm bound stays Rayleigh (the C\*-order↔norm bridge is ℂ-only — `Matrix n n ℝ` isn't a `CStarAlgebra`, verified) |
| `Analysis/SoftmaxLipschitz.lean` | `softmax` def + `hasFDerivAt_softmax` (softmax fderiv = `toEuclideanCLM` of its Jacobian) + `lipschitzWith_softmax` (**`LipschitzWith ½`, unconditional**) | SelfAttention/FixedPattern (F2-B) | **strong Mathlib candidate (proved)** — ½ tight (arXiv:2510.23012); packages with `softmax_jacobian_opNorm_le_half` |
| `Analysis/IntervalArithmeticSound.lean` | `ibp_affine_sound` / `ibp_relu_sound` (affine + ReLU interval steps contain the true image) | IntervalBounds, ExactMILP | **candidate** (NN-IBP form); primitives exist |

> **Removed:** `Topology/RobustBallOffClosed.lean` — the intended lemma already
> exists as `Metric.disjoint_closedBall_of_lt_infDist` (verified against the pinned
> Mathlib source). `AlgebraicBoundary` calls it directly. This deletion was a
> finding of the first self-review pass.

## Contribution workflow (same discipline as the DKPS repo)

1. Prove the statement here against the pinned Mathlib rev (`lake-manifest.json`). ✓ done.
2. Verify `#print axioms <decl>` is clean (`{propext, Classical.choice, Quot.sound}`) —
   run [`../scripts/check.sh`](../scripts/check.sh) / [`../AxiomAudit.lean`](../AxiomAudit.lean).
3. Only then consider it a Mathlib PR candidate; downgrade any that turn out to be
   one-liners over existing API to a local corollary and delete the staging file.

`softmax_jacobian_opNorm_le_half` together with its now-proved consumer
`lipschitzWith_softmax` (softmax is `½`-Lipschitz, tight) is the clear upstream candidate —
softmax appears nowhere in the pinned Mathlib.
