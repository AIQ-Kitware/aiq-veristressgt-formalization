# Dominant-key linear attention — paper Appendix A.7 (Lemma 8, Props 9–10)

Source: VeriStressGT paper (arXiv:2605.17153), Appendix A.7. This file transcribes the
*argument structure* of the linear-dominance certificate as used by the Lean development in
[`SelfAttention/DominantKey.lean`](../SelfAttention/DominantKey.lean); the equation-number
crosswalk follows the audit's PDF extraction (AUDIT4.md §4/N2). **Lemma 8 and Props 9–10 are
now all formalized** — A.7 is machine-checked end to end.

## Setup

A linear-attention head assigns token `i` an output `Zᵢ = ∑ⱼ aᵢⱼ · Vⱼ`, where the weights
`aᵢⱼ = wᵢⱼ / ∑ₖ wᵢₖ` are normalized from *positive* unnormalized scores `wᵢⱼ > 0`, and
`Vⱼ` are the value vectors. For each query `i` there is a **dominant key** `j*ᵢ`.

**Dominance condition (eq. 7).** Key `j*ᵢ` dominates by a factor `ρᵢ ≥ 0` when

    ρᵢ · ∑_{j ≠ j*ᵢ} wᵢⱼ  ≤  wᵢ,j*ᵢ .

## Lemma 8 (App. A.7) — FORMALIZED

The attention output is close to the dominant key's value, with the gap controlled by the
dominance ratio and the spread of the competing values:

    ‖ Zᵢ − V_{j*ᵢ} ‖₂  ≤  (1 / (1 + ρᵢ)) · max_{j ≠ j*ᵢ} ‖ Vⱼ − V_{j*ᵢ} ‖₂ .

**Proof (eq. 59–61).**
- (eq. 60–61, the convex-combination core) Since `∑ⱼ aᵢⱼ = 1`, the deviation is
  `Zᵢ − V_{j*} = ∑ⱼ aᵢⱼ (Vⱼ − V_{j*})`, whose `j = j*` term vanishes, so
  `‖Zᵢ − V_{j*}‖ ≤ ∑_{j≠j*} aᵢⱼ · M = (1 − aᵢ,j*) · M`, where `M` bounds the competitor
  spread. — Lean: `attn_dominant_key_bound` (for any probability vector).
- (eq. 59, the ρ-bridge) The dominance condition gives `1 − aᵢ,j* ≤ 1 / (1 + ρᵢ)`: writing
  `S = ∑_{j≠j*} wⱼ` and `T = w_{j*} + S`, `1 − a_{j*} = S/T`, and `S/T ≤ 1/(1+ρ) ⟺ ρ·S ≤
  w_{j*}` (the hypothesis). — Lean: `dominant_weight_bound`.
- Composing gives Lemma 8. — Lean: `attn_dominant_key_bound_rho`.

## Proposition 9 (App. A.7) — three-term insertion bound — FORMALIZED (`attn_output_perturbation`)

Over the `L∞` ε-box, with per-row dominance at both `X` and `X₀` (same `j*ᵢ`, uniform `ρ`),
nominal value spread `‖V₀ⱼ − V₀,j*‖ ≤ ΔV` and value drift `‖V_X j − V₀ j‖ ≤ ε·L_V`, the
per-row output moves by (eq. 63)

    ‖ Zᵢ(X) − Zᵢ(X₀) ‖  ≤  (2/(1+ρ))·ΔV  +  (1 + 2/(1+ρ))·ε·L_V .

Proof shape (eq. 64–67): triangle through `V_X(j*)` and `V₀(j*)`, apply Lemma 8 at `X` (with
spread `≤ ΔV + 2εL_V`) and at `X₀` (spread `ΔV`), and the middle term by the value drift.

## Proposition 10 (App. A.7) — the certificate — FORMALIZED (`linAttn_dominant_robust`)

With `Δ_lin := (2/(1+ρ))·ΔV + (1 + 2/(1+ρ))·ε·L_V` and a linear head `W_head`, a nominal
margin exceeding `2·‖W_head‖·√n·Δ_lin` for every competitor certifies robustness on the box
(eq. 68–71) — the same `√n` token pooling + head/margin structure already formalized for the
gated construction in [`SelfAttention/LinearDominanceBlock.lean`](../SelfAttention/LinearDominanceBlock.lean)
(`zflat_deviation`, `margin_deviation`, `robust_of_deviation_lt_margin`), which Props 9–10
would reuse verbatim with `Δ_lin` in place of `√n·Bmax`.
