# Theorem map — UCLA / VeriStressGT constructions ↔ published theorems

Status: **proposal / first pass**, 2026-07-03. Companion to
[`docs/planning/ta1-formalization-edges.md`](../../docs/planning/ta1-formalization-edges.md)
§3.2 (this is its deep expansion) and to the transcriptions in
[`prose/`](prose/). Scope: `ta1/VeriStressGT/`.

## The most relevant published theorems

Ranked by how load-bearing they are for VeriStressGT's *ground-truth* labels.
Each links to its prose transcription and carries its arXiv id (PDFs fetched, not
committed — see [`papers/`](papers/)).

| # | Published theorem | arXiv | Role in VeriStressGT | Prose |
|---|---|---|---|---|
| T1 | **Lipschitz-margin certificate** (Tsuzuku–Sato–Sugiyama 2018): `margin > √2·L·ε ⟹ robust` | [1802.04034](https://arxiv.org/abs/1802.04034) | The certificate for `deep_contractive_cnn`; the margin half of both attention certs | [lipschitz-margin-certificate.md](prose/lipschitz-margin-certificate.md) |
| T1′ | **Product-of-spectral-norms Lipschitz composition** (Szegedy 2014; Cisse/Parseval 2017; Miyato 2018) | — / [1704.08847](https://arxiv.org/abs/1704.08847) | Supplies the `L = σ_proj·λ^D·‖w_out‖₁` used by T1 | ″ |
| T2 | **Lipschitz constant of self-attention** (Kim–Papamakarios–Mnih 2021): dot-product attention is *not* globally Lipschitz; softmax-Jacobian `‖diag a − aaᵀ‖≤½` | [2006.04710](https://arxiv.org/abs/2006.04710) | The `L_attn` sensitivity in `attention.fixed_pattern` / `linear_dominance` | [self-attention-lipschitz.md](prose/self-attention-lipschitz.md) |
| T3 | **Exact MILP robustness radius** (Tjeng–Xiao–Tedrake 2019) + **NP-completeness** (Katz et al. *Reluplex* 2017) | [1711.07356](https://arxiv.org/abs/1711.07356) / [1702.01135](https://arxiv.org/abs/1702.01135) | The ground-truth oracle for `mlp_relu.milp.exact_radius` (ships `ε=0.999·r*`) | [exact-milp-and-npcompleteness.md](prose/exact-milp-and-npcompleteness.md) |
| T4 | **IBP soundness** (Gowal 2018) + **convex-relaxation barrier** (Salman 2019) + **linear-region count** (Montúfar 2014) | [1810.12715](https://arxiv.org/abs/1810.12715) / [1902.08722](https://arxiv.org/abs/1902.08722) / [1402.1869](https://arxiv.org/abs/1402.1869) | Theory behind the **Difficulty Profile** coordinates (`unstable_frac`, `ibp_relative_gap`, `A_tau_*`) | [ibp-relaxation-barrier-linear-regions.md](prose/ibp-relaxation-barrier-linear-regions.md) |
| T5 | **CROWN** (Zhang 2018) + **β-CROWN** complete branch-and-bound (Wang 2021) | [1811.00866](https://arxiv.org/abs/1811.00866) / [2103.06624](https://arxiv.org/abs/2103.06624) | The **verifier under test** (α-β-CROWN); complete-in-limit, incomplete-under-60 s | [crown-branch-and-bound.md](prose/crown-branch-and-bound.md) |
| T6 | **Euclidean-distance degree** (Draisma et al. 2016) → **polynomial-net verification** (Alexandr–Duan–Montúfar) | [1309.0049](https://arxiv.org/abs/1309.0049) / [2602.06105](https://arxiv.org/abs/2602.06105) | Distance-to-algebraic-boundary certificate for `polynomial.algebraic_boundary` | [ed-degree-polynomial-verification.md](prose/ed-degree-polynomial-verification.md) |
| — | **UCLA paper itself** (Troxell et al., *Stress-Testing NN Verifiers…*) | [2605.17153](https://arxiv.org/abs/2605.17153) | Frames "provably robust instance + Difficulty Profile"; not itself a theorem to relax | [00-overview-and-provenance.md](prose/00-overview-and-provenance.md) |

## Construction → theorem crosswalk

Every construction in `src/VeriStressGT/robust_constructions/` and which theorem
supplies its ground-truth UNSAT label.

| Construction (`CONSTRUCTION_NAME`) | File | Ground-truth theorem | Certificate constant | Formalizability |
|---|---|---|---|---|
| `cnn.deep_contractive_cnn` | `cnn/deep_contractive_cnn.py` | **T1 + T1′** | `L = σ_proj·λ^D·‖w_out‖₁`, exact-ish (power-iter) | **High** — 2-line margin lemma + Mathlib `LipschitzWith.comp` |
| `cnn.cnn_paired_bias` | `cnn/cnn_paired_bias.py` | T1 (+ exploits CROWN's per-neuron independence) | Lipschitz-margin variant | High |
| `attention.linear_dominance` | `attention/linear_dominance.py` | **T2** (gated-linear, softmax-free) | bilinear `B_i = Δw(‖V_i‖+ΔV)+w_{ii}ΔV`, **exact** | **High** ★ easiest attention target |
| `attention.fixed_pattern` | `attention/fixed_pattern.py` | **T2** (softmax) + gap condition | `2·L_h·√n·L_attn·ε` | Med-High (needs softmax-Jacobian lemma) |
| `mlp_relu.milp.exact_radius` | `mlp_relu/milp/exact_radius.py` | **T3** | exact `r*` from MILP (`OPTIMAL`) | High for *encoding faithfulness*; `EDdeg`-free |
| `mlp_relu.meap` / `corners` / `embedded_projection` | `mlp_relu/*.py` | T1-flavoured margin / projection certs | per-construction | Med-High |
| `polynomial.algebraic_boundary` | `polynomial/algebraic_boundary.py` | **T6** | `dist(x₀,𝒱)` (shipped as numerical NBC surrogate) | metric lemma High; `EDdeg` machinery out of scope |
| — Difficulty Profile — | `difficulty_profile/components.py` | **T4** (measurement, not certificate) | `unstable_frac`, `ibp_relative_gap`, `A_tau_effective_log`, … | Low (measurements); IBP-soundness is High |
| — card claim — | `cards/evaluation.yaml` | **T5** qualifiers dropped | `correct_fraction ≥ 0.6` @ 60 s | Low (no theorem entails 0.6) |

## The one-paragraph synthesis

VeriStressGT is **not** one theorem with a finite-sample shadow (that is JHU). It
is a **certificate factory**: each construction instantiates a *different*
published robustness theorem (T1/T2/T3/T6) on hand-designed weights so the UNSAT
label holds *by construction*, then asks α-β-CROWN (T5) to re-derive it under a
budget, and reports where on the relaxation barrier (T4) each instance sits. So
the formalizable content is **many small certificate lemmas** whose hypotheses
are cleanly nameable; the *card* claim (≥60% @ 60 s) is an empirical
verifier-stress measurement with no underlying theorem. The formalization edges
(next doc) therefore split into two kinds: **(a)** certificate hypotheses the
*construction* numerically approximates (power-iteration `L`, clamped MILP `Rmax`,
multi-start NBC), and **(b)** verifier qualifiers the *card* drops (soundness
assumed, completeness time-bounded).
