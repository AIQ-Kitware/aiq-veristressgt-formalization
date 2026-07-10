# `SelfAttention` — T2

**Certificate:** `margin(X₀) > 2·L_h·√n·L_attn·ε ⟹ robust`, where `L_attn` is the
attention block's local Lipschitz constant.
**Paper:** Kim–Papamakarios–Mnih 2021 ([arXiv:2006.04710](https://arxiv.org/abs/2006.04710)) — dot-product attention is *not* globally Lipschitz; the bound is regional.
**Prose:** [`../prose/self-attention-lipschitz.md`](../prose/self-attention-lipschitz.md).

Status tracked in [`../formalization.yaml`](../formalization.yaml); all **proved**.

| Declaration | File | What it claims |
|---|---|---|
| `linearDominance_token_bound` | `LinearDominance.lean` | bilinear product-rule bound `‖wV − w₀V₀‖ ≤ …` (softmax-free) |
| `linearDominance_robust` | `LinearDominance.lean` | margin cert for `attention.linear_dominance`, **total-deviation form** (audit F3: `B_max` already absorbs `ε`) |
| `token_deviation` | `LinearDominanceBlock.lean` | per-token `‖ΔZᵢ‖ ≤ B_max` from the code's `dw`/`dV` (consumes `linearDominance_token_bound`) |
| `zflat_deviation` | `LinearDominanceBlock.lean` | `√n` token pooling: `‖Δzflat‖ ≤ √n·B_max` |
| `margin_deviation` | `LinearDominanceBlock.lean` | head step: `|Δmargin| ≤ 2·‖W_head‖·√n·B_max` (bias cancels) |
| `linearDominance_robust_derived` | `LinearDominanceBlock.lean` | **cert DERIVED** — no assumed Lipschitz constant (audit F2, linear) |
| `gap_iff_stability_margin` | `FixedPattern.lean` | coherence gap `⟺` `δ_min > ε·C_max` (audit F10: full equivalence) |
| `gap_implies_stability_margin` | `FixedPattern.lean` | the forward (used) direction |
| `fixedPattern_robust` | `FixedPattern.lean` | softmax margin cert (Lipschitz constant *assumed*) |
| `inner_deviation_bound` / `score_deviation_unit` | `FixedPatternBlock.lean` | fixed-pattern **score sensitivity** `B_S` (bilinear, softmax-free; C.1) |
| `FixedPatternAttn.attn_dist_le` | `FixedPatternBlock.lean` | softmax-row contraction `‖Δaᵢ‖ ≤ ½‖ΔSᵢ‖` (consumes `lipschitzWith_softmax`; C.2) |
| `FixedPatternAttn.Z_deviation` / `Z_deviation_n2` | `FixedPatternBlock.lean` | **assembled** output bound `‖ΔZᵢ‖ ≤ (n/2)·B_S·ε·(Vmax+δV)+δV` — leading coeff **n/2** (C.3, AUDIT2 G1) |
| `pooling_leading_coeff` | `FixedPatternBlock.lean` | supporting identity `√n·½·√n = n/2` |

`linear_dominance` is the clean case (edge SA-5): the construction forces off-diagonal
gates to **exactly zero**, so the pattern is fixed by algebraic identity — no softmax,
no gap inequality. Its certificate is now **fully derived**
(`linearDominance_robust_derived`): per-token gate/value deviations (`dw`/`dV`) → `√n`
pooling → head → margin, with no assumed Lipschitz constant (audit F2, linear construction).

The softmax `fixed_pattern` construction is now **fully assembled** (AUDIT2 G1), mirroring the
linear case: score sensitivity `B_S` (`score_deviation_unit`, C.1) → softmax-row contraction
`‖Δaᵢ‖ ≤ ½‖ΔSᵢ‖` (`attn_dist_le`, consuming `ForMathlib.lipschitzWith_softmax`, C.2) → product-rule
output bound `Z_deviation`/`Z_deviation_n2` (C.3). The `√n` pooling uses Mathlib's
`sq_sum_le_card_mul_sum_sq`; the value path is coefficient-free because `‖aᵢ‖₁ = 1`
(`attn_l1`). `Z_deviation_n2` exhibits the **leading coefficient `n/2`** as a machine-checked
derivation — the Lean anchor for edge `attn-Lattn-n4-pooling` (the honest `n/2` the code's `n/4`
under-estimates 2×). `fixedPattern_robust` remains the older assumed-Lipschitz margin wrapper.

**F2-B:** the softmax contraction rests on `ForMathlib.lipschitzWith_softmax`
(`LipschitzWith ½ softmax`, unconditional — via `ForMathlib.hasFDerivAt_softmax` +
`softmax_jacobian_opNorm_le_half`). Remaining fixed-pattern items are **non-Lean**: the UCLA
adjudication of the `n/4` finding (now backed by `Z_deviation_n2`) and outside review.
