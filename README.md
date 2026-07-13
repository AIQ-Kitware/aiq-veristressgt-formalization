# AIQ VeriStressGT Formalization

Lean 4 formalization of the theorems underlying the UCLA **VeriStressGT** (neural-network
robustness-verification stress test) TA1 evaluation card. Structure mirrors the sibling
[`aiq-dkps-formalization`](../aiq-dkps-formalization): one top-level Lean library per
certificate family, a paper-agnostic `ForMathlib` staging library, a
`formalization.yaml`, and prose transcriptions of every source under [`prose/`](prose/).

> 🧭 **New here — especially AI agents — start with [`AGENTS.md`](AGENTS.md).** It
> codifies *why* this exists (formalizing MAGNET evaluation cards), the key structural
> fact (VeriStressGT is a *certificate factory* — many small theorems, not one), the
> published-theorem chain, the working conventions, and the known traps. This README is
> just the build + library map.

> **Status: proved & axiom-clean — `lake build` green, ZERO `sorry`.** Every substantive
> theorem is proved; an independent `#print axioms` sweep over all **63 audited declarations**
> ([`AxiomAudit.lean`](AxiomAudit.lean) / [`scripts/check.sh`](scripts/check.sh)) shows only
> `{propext, Classical.choice, Quot.sound}`.
> Both audit gaps (F2, F4b) are **fully closed** in Lean — for **both** attention constructions
> and including the softmax `LipschitzWith ½` bound (F2-B). Not all theorems are equal weight —
> see the three-tier breakdown in [`AUDIT.md`](AUDIT.md) §3. The flagship
> `ForMathlib.softmax_jacobian_opNorm_le_half` (`‖diag a − aaᵀ‖₂ ≤ ½`, tight) is proved via the
> self-adjoint operator-norm = sup-Rayleigh route. **Single source of truth for status:
> [`formalization.yaml`](formalization.yaml)** (`review:` section); this block summarizes it.
>
> Three review passes are folded in — [`AUDIT.md`](AUDIT.md) (F1–F11),
> [`GUIDANCE-F2-F4b.md`](GUIDANCE-F2-F4b.md), and [`AUDIT2.md`](AUDIT2.md) (G1–G9):
> - **F4b CLOSED** — the whole-network big-M encoding is wired to IBP box validity
>   ([`ExactMILP/Network.lean`](ExactMILP/Network.lean): `advSet`, `bigMReach_sound`/`_complete`,
>   `bigM_feasible_iff_netEval`; [`IntervalBounds`](IntervalBounds/Basic.lean) `netTrace_mem_netBoxes`).
> - **F2-B CLOSED (unconditional)** — [`SoftmaxLipschitz.lean`](ForMathlib/Analysis/SoftmaxLipschitz.lean)
>   proves the softmax Fréchet derivative on `EuclideanSpace` (`hasFDerivAt_softmax`) and concludes
>   `lipschitzWith_softmax : LipschitzWith ½ softmax` — the completed consumer of the Jacobian
>   bound and the ForMathlib upstream candidate (½ tight, arXiv:2510.23012; no Lean source existed
>   to reuse, [`EXTERNAL-LEAN-SURVEY.md`](EXTERNAL-LEAN-SURVEY.md)).
> - **F2 CLOSED for the linear construction** — `linearDominance_robust_derived` derives the
>   certificate from per-token deviations, no assumed Lipschitz constant
>   ([`LinearDominanceBlock.lean`](SelfAttention/LinearDominanceBlock.lean)).
> - **F2 fixed-pattern chain ASSEMBLED** (AUDIT2 G1) — [`FixedPatternBlock.lean`](SelfAttention/FixedPatternBlock.lean)
>   `Z_deviation`/`Z_deviation_n2` derive `‖ΔZᵢ‖ ≤ (n/2)·B_S·ε·(Vmax+δV) + δV`, consuming
>   `lipschitzWith_softmax` and Mathlib's Chebyshev pooling lemma. Its **leading coefficient `n/2`
>   is now a machine-checked derivation** — the real Lean anchor for edge `attn-Lattn-n4-pooling`.
>
> **Headline finding — a confirmed soundness bug ([`FINDING-attn-Lattn-n4.md`](FINDING-attn-Lattn-n4.md)).**
> Reading the primary sources settled the `n/4` question: the VeriStressGT **paper**
> (arXiv:2605.17153 §A.6 eq. 54) uses **`n/2`** (from the spectral `‖∇softmax‖_op ≤ ½`), matching
> our machine-checked `Z_deviation_n2`; the shipped **code** `compute_L_attn` uses **`n/4`** (the
> *entrywise* Jacobian max `¼` mis-substituted for the spectral norm). The code under-certifies
> `L_attn` by 2× vs its own paper — the **unsafe** direction (risk of false-UNSAT ground-truth
> labels). This is exactly the class of defect the edges program exists to catch, now backed by a
> machine-checked bound rather than prose.
>
> *(Flagship packaging note, AUDIT2 G8: the Mathlib-preferred **Loewner** statements
> `softmaxJac_posSemidef` (`0 ≤ J`) and `two_smul_softmaxJac_le_one` (`2•J ≤ 1`) are added; the
> `½` operator-norm form stays the Rayleigh proof because Mathlib's C\*-algebra order↔norm bridge is
> ℂ-only — `Matrix n n ℝ` is not a `CStarAlgebra`, verified.)*

## What VeriStressGT claims

Every generated instance is **UNSAT (provably robust) by construction**: each
construction instantiates a published robustness theorem so that
`margin(x₀) > (Lipschitz/sensitivity constant) · ε ⟹ no adversarial example in the L∞
ε-box`. The instance is exported as an `(ONNX, VNN-LIB)` pair, and the card
(`../../ta1/VeriStressGT/cards/evaluation.yaml`) asks the verifier **α-β-CROWN** to
re-derive the UNSAT verdict on **≥ 60%** of instances within a **60 s** timeout. So the
*ground-truth certificate* is a theorem; the *card claim* is an empirical verifier stress
test. See [`AGENTS.md`](AGENTS.md) §3 and [`prose/README.md`](prose/README.md) for the
full published-theorem chain.

## Libraries

| Library | Role | Key declarations |
|---|---|---|
| `ForMathlib` | Paper-agnostic staging: operator-norm Lipschitz, softmax-Jacobian bound, IBP steps | `lipschitz_affine_of_opNorm`, `softmax_jacobian_opNorm_le_half`, `ibp_affine_sound`, `ibp_relu_sound` |
| `LipschitzMargin` | T1/T1′ — scalar Lipschitz-margin certificate + spectral-norm composition | `robust_of_margin_gt`, `argmax_stable_of_margin_gt`, `dccnn_robust_of_true_L`, `dccnn_robust_of_upper_bound` |
| `SelfAttention` | T2 — attention `L_attn` sensitivity | `linearDominance_token_bound`, `linearDominance_robust`, `gap_implies_stability_margin`, `fixedPattern_robust` |
| `IntervalBounds` | T4 — interval bound propagation soundness | `Layer`, `netEval`, `netProp`, `ibp_network_sound`, `robust_of_ibp_lower_pos` |
| `ExactMILP` | T3 — big-M ReLU encoding faithfulness + label soundness | `bigM_relu_faithful`, `label_sound_of_optimal` |
| `AlgebraicBoundary` | T6 — distance-to-the-algebraic-boundary certificate | `robust_of_lt_dist_boundary`, `robust_of_numerical_lower_bound` |
| `Verifier` | T5 — CROWN/β-CROWN sound/complete *specification* the card stands on | `VerifierSpec`, `Sound`, `CompleteInLimit`, `sound_unsat_robust` |

There is **no single capstone** (unlike DKPS/DRSB): VeriStressGT is many independent
per-construction certificates. Each `<Library>/Basic.lean` docstring cites the prose file
+ printed theorem number every declaration corresponds to; each library's `README.md`
gives its construction crosswalk.

## Layout

```text
.
├── ForMathlib.lean / ForMathlib/     # DV-free reusable results (import: Mathlib only)
├── <Library>.lean / <Library>/       # one library per certificate family (import: Mathlib + ForMathlib)
├── prose/                            # faithful transcriptions of every source theorem
├── papers/                           # fetch script + manifest (PDFs git-ignored)
├── theorem-map.md                    # published-theorem ⟷ construction crosswalk
├── ucla-formalization-edges.md       # assumption→relaxation edges + power-iteration Appendix A
├── formalization.yaml                # project metadata (sources, targets, status, edges)
└── lakefile.toml / lake-manifest.json / lean-toolchain / setup_lean.sh
```

The planning products (`theorem-map.md`, `ucla-formalization-edges.md`, `prose/`) are the
pre-Lean layer: they identify the published theorems, transcribe their core argument
chains, and draw the edges to the empirical repo `../../ta1/VeriStressGT/`.

## Build

Toolchain `leanprover/lean4:v4.31.0-rc2`; Mathlib pinned in `lake-manifest.json` (same
rev as the DKPS repo — this repo's `.lake/packages` may be symlinked to it to reuse the
build).

```bash
bash setup_lean.sh      # elan + the pinned toolchain
lake exe cache get      # download prebuilt Mathlib oleans (or reuse the sibling build)
lake build              # builds green (zero `sorry`; see scripts/check.sh)
```

Check a single file fast (no build lock): `lake env lean LipschitzMargin/Basic.lean`.

## Next steps

Both audit gaps (F2 including the softmax bound, and F4b) are landed. The remaining work is
non-Lean adjudication and outside review.

1. **Adjudicate the `n/4` pooling (F2-C.3, edge `attn-Lattn-n4-pooling`):** find the halving
   argument in Kim et al. (arXiv:2006.04710) — if none exists, this is a candidate Family-A
   soundness bug in `compute_L_attn` (certified `L_attn` ~2× too small, unsafe direction).
   `pooling_leading_coeff` records the honest `n/2`; raise with UCLA.
2. **External review** of statement faithfulness to the PDFs — the concrete asks are in
   [`AUDIT.md`](AUDIT.md) §5 step 7.
3. **DKPS parity (AUDIT.md §6):** package `softmax_jacobian_opNorm_le_half` **and its now-proved
   consumer `lipschitzWith_softmax`** as a `Challenge/MathlibCandidate/` (the strongest upstream
   candidate in the repo).
4. **Optional (`float32-export`, R9):** adopt `girving/interval` if the float-soundness edge is
   prioritized ([`EXTERNAL-LEAN-SURVEY.md`](EXTERNAL-LEAN-SURVEY.md) §A).

Reproduce the verification story at any time with [`scripts/check.sh`](scripts/check.sh)
(build + no-sorry + axiom audit).
