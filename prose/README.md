# `prose/` — transcribed core mathematical arguments for the UCLA / VeriStressGT thread

This folder mirrors the `prose/` convention in
[`aiq-dkps-formalization`](../../aiq-dkps-formalization) (e.g.
`DkpsQuench/prose/`, `Acharyya2024/prose/`): before any Lean is written, the
**chain of core mathematical arguments** for each load-bearing published theorem
is transcribed to Markdown so that (a) the statement, its hypotheses, and its
proof skeleton are pinned in one place, and (b) a later Lean formalization has a
faithful, line-checkable target.

Unlike the DKPS repo — where each `prose/` sits next to a single paper's Lean
library — the UCLA thread has **no single paper theorem**. VeriStressGT's whole
premise is that every generated instance is UNSAT *by construction*, and each
construction discharges a **different, small, self-contained certificate theorem**
drawn from the robustness-verification literature. So this folder transcribes the
**published theorems the constructions instantiate**, not (only) the UCLA paper
itself. See [`../theorem-map.md`](../theorem-map.md) for the construction →
theorem crosswalk and [`../ucla-formalization-edges.md`](../ucla-formalization-edges.md)
for the assumption → relaxation edges.

## Files

| File | Core argument transcribed | Grounds which construction(s) |
|---|---|---|
| [`00-overview-and-provenance.md`](00-overview-and-provenance.md) | The two UCLA papers; how "provably robust instance" decomposes into a certificate theorem + a verifier stress test | all |
| [`lipschitz-margin-certificate.md`](lipschitz-margin-certificate.md) | Tsuzuku–Sato–Sugiyama Lipschitz-margin bound; product-of-spectral-norms composition | `cnn.deep_contractive_cnn`, and the margin half of the attention certs |
| [`self-attention-lipschitz.md`](self-attention-lipschitz.md) | Kim–Papamakarios–Mnih: dot-product self-attention is not globally Lipschitz; softmax-Jacobian spectral bound | `attention.fixed_pattern`, `attention.linear_dominance` |
| [`exact-milp-and-npcompleteness.md`](exact-milp-and-npcompleteness.md) | Katz et al. NP-completeness of ReLU verification; Tjeng–Xiao–Tedrake big-M MILP for the exact radius | `mlp_relu.milp.exact_radius` (ground-truth oracle) |
| [`ibp-relaxation-barrier-linear-regions.md`](ibp-relaxation-barrier-linear-regions.md) | Interval Bound Propagation soundness; the Salman et al. convex-relaxation barrier; Montúfar et al. linear-region counting | the **Difficulty Profile** (`unstable_frac`, `ibp_relative_gap`, `A_tau_*`, `margin_sample_min`) |
| [`crown-branch-and-bound.md`](crown-branch-and-bound.md) | CROWN linear relaxation; β-CROWN per-neuron split + branch-and-bound; soundness & incompleteness-under-timeout | the verifier under test (α-β-CROWN) and the card's ≥60%/60 s claim |
| [`ed-degree-polynomial-verification.md`](ed-degree-polynomial-verification.md) | Draisma et al. Euclidean-distance degree; distance-to-the-algebraic-boundary certification | `polynomial.algebraic_boundary` (the arXiv:2602.06105 thread) |

## Reading convention (same as DKPS)

Each file states the theorem as **hypotheses → conclusion**, then gives the
**argument chain** (the proof reduced to its load-bearing steps), then a
**"hypotheses to scrutinize"** list flagging exactly which assumptions the
VeriStressGT code either *discharges exactly*, *approximates numerically*, or
*silently drops*. Those flags are what become formalization edges.

Source PDFs are downloaded (not committed) into [`../papers/`](../papers/); run
[`../papers/fetch_papers.sh`](../papers/fetch_papers.sh). Every theorem below
carries its arXiv id inline.
