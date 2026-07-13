# `LipschitzMargin` — T1 + T1′

**Certificate:** `margin(x₀) > L·(perturbation) ⟹ robust`, with
`L = ∏‖Wᵢ‖₂` (spectral-norm composition).
**Papers:** Tsuzuku–Sato–Sugiyama 2018 ([arXiv:1802.04034](https://arxiv.org/abs/1802.04034)); Parseval/spectral-norm composition.
**Prose:** [`../prose/lipschitz-margin-certificate.md`](../prose/lipschitz-margin-certificate.md).
**Grounds:** `cnn.deep_contractive_cnn` and the margin half of both attention certs.

Status tracked in [`../formalization.yaml`](../formalization.yaml); all **proved**.

| Declaration | File | What it claims |
|---|---|---|
| `robust_of_margin_gt` | `Basic.lean` | scalar margin `> K·ε` ⟹ `g>0` on the `ε`-ball |
| `argmax_stable_of_margin_gt` | `Basic.lean` | multi-competitor form |
| `robust_of_deviation_lt_margin` | `Basic.lean` | total-deviation form (bound `D` absorbs `ε`) — for certs like linear-dominance |
| `dccnn_robust_of_true_L` / `_upper_bound` | `DeepContractiveCNN.lean` | scalar margin cert with `hg` *assumed* (Tier-2); `_upper_bound` carries edge `dccnn-L-power-iter` via premise `L ≤ L̂` |

**T1′ (composition bound) — now formalized (audit F1):**

| Declaration | File | What it claims |
|---|---|---|
| `AffLayer` / `AffLayer.map` / `.map_lipschitz` | `DeepContractiveCNN.lean` | one affine + `1`-Lipschitz-activation layer is `‖W‖₊`-Lipschitz |
| `netMap` / `netLipschitz` | `DeepContractiveCNN.lean` | the network is `LipschitzWith (∏ᵢ ‖Wᵢ‖₊)` — via Mathlib's `LipschitzWith.list_prod` |
| `netProd_eq` | `DeepContractiveCNN.lean` | `∏ᵢ ‖Wᵢ‖₊ = σ_proj · λ^D · w_out` under the DCCNN normalization |
| `dccnn_margin_lipschitz` | `DeepContractiveCNN.lean` | margin read-out `φ∘net` is `‖φ‖₊·∏‖Wᵢ‖₊`-Lipschitz |
| `dccnn_robust_via_net` / `_upper` | `DeepContractiveCNN.lean` | robustness with `L` **discharged** by the product; `_upper` attaches the edge `L ≤ L̂` to the genuine `‖φ‖₊·∏‖Wᵢ‖₊` |

So the certified constant `L = σ_proj·λ^D·‖w_out‖` (`compute_true_lipschitz_bound`,
`deep_contractive_cnn.py:235`) now appears in Lean as the actual product of layer
operator norms, and the `dccnn-L-power-iter` edge (power iteration under-estimates each
`‖Wᵢ‖`, so `L̂ < L`) anchors to that product — see
[`../ucla-formalization-edges.md`](../ucla-formalization-edges.md) Appendix A. Constant
width (audit F8): layers are self-maps of one space; heterogeneous shapes embed by
zero-padding (norm-preserving).
