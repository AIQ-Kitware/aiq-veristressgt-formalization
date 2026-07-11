# Lipschitz sensitivity of self-attention

**Primary source:** H. Kim, G. Papamakarios, A. Mnih,
*The Lipschitz Constant of Self-Attention*, ICML 2021. **arXiv:2006.04710**.

**Grounds:** `robust_constructions/attention/fixed_pattern.py` (softmax
attention) and `attention/linear_dominance.py` (linear/gated attention). Both
build the *value / head* margin exactly as in
[`lipschitz-margin-certificate.md`](lipschitz-margin-certificate.md); the new
content here is the **`L_attn` sensitivity constant** of the attention block.

---

## 1. The two facts from Kim et al.

Let `X ∈ ℝ^{n×d}` be `n` tokens. Standard **dot-product self-attention** is

> `Attn(X) = softmax(α · X Xᵀ) · (X W_V)`  (self-attention: queries=keys=values=X).

> **Fact 1 (negative).** Dot-product self-attention is **not globally
> Lipschitz** on `ℝ^{n×d}`: as `‖X‖ → ∞` the Jacobian norm is unbounded. The
> obstruction is that the score `X Xᵀ` is *quadratic* in the input, so the
> softmax argument — and hence the Jacobian — grows without bound.

> **Fact 2 (positive / the usable bound).** On any **bounded** input region, or
> for the L2-attention variant, the map is Lipschitz, and the block's Jacobian
> decomposes through the **softmax Jacobian**
> `J_softmax(s) = diag(a) − a aᵀ`, where `a = softmax(s)`. Its spectral norm
> satisfies `‖diag(a) − a aᵀ‖₂ ≤ 1/2` (a probability-vector fact: the largest
> eigenvalue of `diag(a)−aaᵀ` is ≤ ¼·… bounded by ½), which is the seed of every
> attention Lipschitz constant.

VeriStressGT lives in Fact 2's regime *deliberately*: it works on a **bounded
`L∞` `ε`-box** around a fixed `X₀`, so a finite local `L_attn` exists, and it
picks `X₀` near-orthogonal so the softmax is far from the flat/degenerate regime
where the bound is loosest.

## 2. The `L_attn` bound — paper (`n/2`) vs code (`n/4`)

For scaled attention `softmax(α X Xᵀ)(X W_V)` on the `ε`-box around `X₀`, with
`V₀ = X₀ W_V`, the **paper** (arXiv:2605.17153 Appendix A.6, eq. 52–54) states

```
B̄_S(ε) = α·(2√d + ε·d)                          # bound on the score perturbation ‖ΔS‖
L_attn  = (n/2)·B̄_S·‖V₀‖_{2,∞}                   # softmax-Jacobian × value magnitude term
        + √d·σ(W_V)                              # value-path sensitivity
        + (n/2)·B̄_S·ε·√d·σ(W_V)                  # cross second-order term
```

derived from `‖∇softmax(z)‖_op ≤ ½` (spectral) via the per-row drift
`‖ã_i − a_i⁰‖₁ ≤ (n/2)·ε·B̄_S` (eq. 52). **The shipped code `compute_L_attn`
(fixed_pattern.py:56–71) instead uses `n/4` on the first and third terms** — a
confirmed code-vs-paper discrepancy (2× too small, unsafe direction). See
[`../FINDING-attn-Lattn-n4.md`](../FINDING-attn-Lattn-n4.md); the honest `n/2` is
machine-checked as `FixedPatternAttn.Z_deviation_n2`.

**Argument chain (product / chain rule).** Attention output row `Z_i =
Σ_j a_{ij} v_j`. Perturbing `X → X+Δ` (‖Δ‖∞ ≤ ε) moves two things:
1. **the weights `a`**, through the score `S = αXXᵀ`. `ΔS` is bounded by
   `B̄_S = α(2√d + εd)` (linear `2√d` term + quadratic `εd` self-term). The
   **spectral** softmax-Jacobian bound `‖diag(a)−aaᵀ‖_op ≤ ½` gives
   `‖Δa_i‖₂ ≤ ½·‖ΔS_i‖₂ ≤ ½·√n·B̄_S·ε`, then `‖Δa_i‖₁ ≤ √n·‖Δa_i‖₂ = (n/2)·B̄_S·ε`
   (ℓ¹←ℓ² Cauchy–Schwarz). The coefficient is **`n/2`**, not `n/4`; substituting
   the *entrywise* Jacobian bound `maxₐ a(1−a) = ¼` for the spectral `½` is the
   only route to `n/4`, and it is wrong here (the ℓ² row-aggregation needs the
   spectral norm).
2. **the values `v = XW_V`**, with sensitivity `√d·σ(W_V)` (`L∞→L₂` gives `√d`,
   `σ(W_V)` is the projection's spectral norm); coefficient-free in `n` because
   `‖a_i⁰‖₁ = 1`.
The product rule on `a·v` gives the three terms: `Δa · v₀` (term 1), `a·Δv`
(term 2), and `Δa·Δv` (the cross term). Then the head `W_head` (spectrally
normalised so `L_h = ‖W_head‖₂ = 1`) multiplies through, giving the full logit
sensitivity `L_h · √n · L_attn` (the `√n` folds the `n` token rows into the flat
logit vector, matching the paper's eq. 55 `‖Attn(X)−Attn(X₀)‖_F ≤ √n·L_attn·ε`).

**The certificate.** With that constant, the margin condition (`check_certificate`,
line 111) is the *same* Lipschitz-margin corollary as the CNN:

> `m_X0 = logit_y − max_{k≠y} logit_k  >  2 · L_h · √n · L_attn · ε   ⟹  robust`.

The construction sets the head bias so `m_X0 = margin_slack · (RHS)` with
`margin_slack ≳ 1` (line 239), i.e. it sits *just above* the certified threshold —
deliberately near the robustness boundary to stress the verifier's tightness.

## 3. The gap condition (attention-specific, no CNN analogue)

`fixed_pattern.py` additionally imposes a **gap / pattern-stability condition**
(lines 82–92): with token coherence `μ = max_{i≠j}|⟨x_i,x_j⟩|`,

> `1 − μ  >  4ε√d + 2ε²d`.

This guarantees the **argmax attention pattern does not change** inside the box —
the softmax stays "locked" onto the same token, so the fixed-pattern linearisation
is valid. It is a *near-orthogonality* requirement: `_build_near_orthogonal_tokens`
(line 147) minimises `μ` over 2000 random draws. This has no counterpart in the
CNN cert; it is the attention-specific hypothesis and a prime **edge**: the
condition is checked at `X₀` for the *nominal* pattern, and the certificate's
validity rests on the pattern never flipping in the box.

## 4. Hypotheses to scrutinize (edge candidates `SA-#`)

- **SA-1 (bounded-region Lipschitz, not global).** Kim et al. Fact 1 says there
  is **no** global constant; the certificate is only valid *inside the `ε`-box*.
  Every use of `L_attn` implicitly relies on `X` staying in the box — which the
  VNN-LIB spec does enforce, so this is sound, but the constant is *region-specific*
  and recomputed per instance.
- **SA-2 (softmax-Jacobian `½`/`n/4` constant) — RESOLVED, confirmed bug.** The
  aggregation of `‖diag(a)−aaᵀ‖_op ≤ ½` over the `n` rows gives coefficient **`n/2`**
  — this is the paper's own eq. 52/54 (arXiv:2605.17153 §A.6) and is now machine-checked
  (`FixedPatternAttn.Z_deviation_n2`). The shipped `compute_L_attn` uses **`n/4`**
  (the *entrywise* Jacobian max `maxₐ a(1−a)=¼` mis-substituted for the spectral norm),
  i.e. **2× too small — the unsafe direction**, so a shipped instance with `margin_slack<2`
  can be a false-UNSAT ground-truth label. Edge `attn-Lattn-n4-pooling`; details in
  [`../FINDING-attn-Lattn-n4.md`](../FINDING-attn-Lattn-n4.md).
- **SA-3 (gap condition ⟹ fixed pattern).** The certificate assumes the softmax
  argmax pattern is constant on the box. `gap_ok` is a *sufficient* condition for
  that; the code checks `gap_ok_actual` (line 92) numerically at `X₀`. Edge: the
  pattern-invariance claim is the real hypothesis; the coherence inequality is a
  conservative proxy for it.
- **SA-4 (spectral norms of `W_V`, `W_head`).** `σ(W_V)`, `L_h` are computed by
  `numpy.linalg.norm(·, 2)` (exact SVD here, unlike the CNN's power iteration) —
  so *this* thread has an exact constant, a nice contrast with edge **LM-1**.
- **SA-5 (`linear_dominance` gate exactness).** `linear_dominance.py` replaces
  softmax with a **ReLU-gated linear** score whose off-diagonal entries are
  *exactly zero by construction* (asserted to `< 1e-12`, lines 176–185): the
  attention pattern is diagonal, so the "pattern stays fixed" hypothesis becomes
  an *algebraic identity* rather than an inequality. The certificate is then a
  clean product-rule bound `B_i = Δw·(‖V_i‖+ΔV) + w_{ii}·ΔV` (line 195). This is
  the *most* formalizable attention instance — no softmax transcendental, no gap
  inequality, just a bilinear perturbation bound. Recommended first Lean target
  of the attention family.

## 5. Formalization target (Lean)

Hard part: `softmax` and its Jacobian bound in Mathlib. The `linear_dominance`
variant (SA-5) sidesteps softmax entirely and reduces to a bilinear
`‖ (w(x)·V(x)) − (w₀·V₀) ‖` product-rule bound — provable with
`Analysis.Normed` product/`mul` lemmas. Do that first; treat `fixed_pattern`'s
softmax bound (SA-2) as the reusable `ForMathlib` lemma
`‖diag a − a aᵀ‖₂ ≤ 1/2 for a a probability vector`, which is independently
Mathlib-worthy.
