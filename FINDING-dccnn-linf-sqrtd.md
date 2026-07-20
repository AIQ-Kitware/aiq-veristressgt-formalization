# Finding (RE-SCOPED): the DCCNN `cert_bound` is norm-incoherent but not exposed as shipped

> **STATUS — 2026-07-17, corrected.** The original exposure claim of this document (an
> earlier draft asserted every shipped DCCNN instance was ~3.6× under-certified) was
> **wrong** and is retracted. AUDIT4 (item J1) caught the error and it is now **machine-checked**
> in [`LipschitzMargin/DccnnReadout.lean`](LipschitzMargin/DccnnReadout.lean). The shipped
> read-out row is *uniform* `1/flat_dim`, so its ℓ₂ operator norm is `‖w‖₂ = 1/√flat_dim`, not
> the ℓ₁ value `‖w‖₁ = 1` the draft used; under the standard all-ℓ₂ Lipschitz-margin
> certificate the shipped margin clears the honest threshold by **≈ 8.8×**. **No shipped
> instance is exposed; do not report this as a soundness bug.** What survives is a
> norm-bookkeeping / robustness-of-process note (§5). The Lean theorems
> `dccnn_robust_linf_box` and `dist_le_sqrt_dim_mul_linf` were always correct — the mistake
> was only in the interpretation, and the same certificate theorem, instantiated with the
> *right* operator norm, settles both the over-claim and its refutation.

**Status:** norm-bookkeeping observation (NOT a soundness finding) · **Severity:** low ·
**Edge:** `dccnn-linf-sqrtd-metric` (`kind: norm-bookkeeping`, `status: NOT-EXPOSED-AS-SHIPPED`) ·
**Lean anchors:** `LipschitzMargin.dccnn_robust_linf_box`, `LipschitzMargin.dccnn_readout_robust`,
`LipschitzMargin.uniform_readout_l2`, `LipschitzMargin.uniform_readout_code_bound_dominates`.

---

## 1. The three artifacts (unchanged — the quotes are accurate)

**The underlying theorem** — the Lipschitz-margin certificate (Tsuzuku–Sato–Sugiyama,
NeurIPS 2018) is an **ℓ₂** statement: if a scalar margin `g` is `L`-Lipschitz *in the
Euclidean norm* and `g(x₀) > L·ε`, then `g(x) > 0` for every `x` with `‖x − x₀‖₂ ≤ ε`.

**The code** — `robust_constructions/cnn/deep_contractive_cnn.py`. The conv/proj Lipschitz
constants are **spectral** (`_spectral_norm_power_iter` = largest singular value, ℓ₂→ℓ₂), and
the certified perturbation folds in `2ε` with the read-out's ℓ₁ norm:
```python
sigma_proj = _spectral_norm_power_iter(model.input_proj.weight)   # ℓ₂→ℓ₂
w_out_l1   = model.fc.weight[model.label].abs().sum().item()      # = 1.0   (uniform row!)
cert_bound = sigma_proj * (model.contraction_rate ** model.depth) * 2 * eps * w_out_l1
```
The VNN-LIB query is a per-coordinate **L∞** box (`_write_vnnlib`, lines 390–397), so an
adversary may set all `d` coordinates to `±ε` simultaneously.

**The Lean proof** — `dccnn_robust_linf_box` states the honest threshold over the L∞ box with
the `√d` explicit; `dist_le_sqrt_dim_mul_linf` is the ℓ∞→ℓ₂ conversion; `dccnn_readout_robust`
uses the read-out's **own operator norm** `‖w‖` as the Lipschitz constant.

## 2. The metric conversion (correct, but not by itself a gap)

The spectral constant supports the Euclidean bound `|f(x) − f(x₀)| ≤ L·‖x − x₀‖₂`, and over
the L∞ box `‖x − x₀‖₂ ≤ √d·ε`. So the honest L∞-box threshold **does** carry a `√d` factor —
that part of the original analysis is right, and `dccnn_robust_linf_box` machine-checks it.

The error was to fix the Lipschitz constant as `L = σ·λ^D·‖w_out‖₁` (the code's bookkeeping)
and conclude the `√d` is a net gap "under either reading." It is not: the margin functional
is `g(x) = ⟨w_out, h(x)⟩ + B` (competitor rows and biases are zeroed — `setup_output_layer`),
whose tight ℓ₂ Lipschitz constant is `‖w_out‖₂·σ·λ^D` by Cauchy–Schwarz (`readout_opNorm`:
`‖innerSL w‖ = ‖w‖₂`). An instance is exposed only if **no** valid certificate reads it as
robust — and the all-ℓ₂ reading is valid *and* far tighter than the ℓ₁ one used.

## 3. Why the shipped instances are safe (≈ 8.8× margin)

The shipped read-out row is **uniform**: `fc.weight[label] = 1/flat_dim`, with
`flat_dim = channels·H·W`. Hence (machine-checked, `uniform_readout_l2`/`_l1`):
```
‖w_out‖₂ = 1/√flat_dim          ‖w_out‖₁ = 1        (they differ by √flat_dim)
```
At the shipped defaults `in_channels=1, H=W=8, channels=16`: `d = 64` (`√d = 8`),
`flat_dim = 1024` (`√flat_dim = 32`). The honest all-ℓ₂ threshold and the shipped margin are
```
honest = ‖w_out‖₂·σλ^D·√d·ε = (1/32)·σλ^D·8·ε = 0.25·σλ^D·ε
B      = 1.1·cert_bound       = 1.1·(σλ^D·2ε·1) = 2.2·σλ^D·ε
```
so `B` clears the honest requirement by **8.8×**. The construction's labels are *proven*
robust by the repo's own certificate theorem (`dccnn_readout_robust` at `‖w‖ = ‖w_out‖₂`).
(The slack analysis — `slack = max(1e-3, 0.1·cert_bound)`, `B = 1.1·cert_bound` for every
shipped config — was correct; only the read-out norm was wrong.)

## 4. The general safety condition (machine-checked)

The code's `cert_bound = σλ^D·2ε·‖w‖₁` dominates the honest `σλ^D·√d·ε·‖w‖₂` exactly when
```
√d · ‖w‖₂  ≤  2 · ‖w‖₁ .
```
For the uniform row (`‖w‖₂ = 1/√flat_dim`, `‖w‖₁ = 1`) this is `√d ≤ 2·√flat_dim`, i.e.
`d ≤ 4·flat_dim`, i.e. **`in_channels ≤ 4·channels`** — true for every shipped and every
reachable CLI configuration (`in_channels = 1`, `channels ≥ 16`). This is
`uniform_readout_code_bound_dominates` (`d ≤ 4m ⟹ (1/√m)·L₀·√d·ε ≤ L₀·2ε`), axiom-clean.

**So the shipped formula is safe — but by accident, not by design.** It is not a coherent
single-norm certificate (a spectral ℓ₂ chain × an ℓ₁ read-out × a `2` that is an L∞-diameter
convention), and it is sound here only because the uniform read-out's `‖w‖₁/‖w‖₂ = √flat_dim`
happens to dwarf `√d/2`.

## 5. What survives (a latent robustness-of-process note)

For a **non-uniform** read-out with `‖w‖₁ ≈ ‖w‖₂` (e.g. a one-hot / class-dependent row), the
safety condition `√d·‖w‖₂ ≤ 2·‖w‖₁` fails as soon as `d > 4`, and the missing `√d` would bite
silently. So the surviving, honest content is a *process* observation, safe to mention
alongside the `n/4` conversation **clearly labeled "no shipped instance is exposed"**: if UCLA
ever varies the read-out, the `cert_bound` formula should be re-derived as a single coherent
norm (certify against `‖w‖₂·σλ^D·√d·ε`, or use ℓ∞→ℓ∞ operator norms end-to-end). The
machine-checked `dccnn_readout_robust` is the drop-in coherent certificate.

## 6. Relation to the still-open DCCNN concern

Everything above (both the original over-claim and this correction) is computed against the
code's *own* per-layer constants `σ_proj, λ`, which come from power iteration on the
**reshaped kernel matrix** — exact for the 1×1 projection but *not* the true convolution
operator norm for the 3×3 layers. That gap is the separate, still-open edge
`dccnn-L-power-iter` (see `ucla-formalization-edges.md` Appendix A), unaffected by this
correction and the strongest remaining DCCNN item. The `√d` metric point is settled: **not a
soundness finding as shipped.**

## Lesson

Three prior audits reviewed this finding for internal consistency and for the code/paper
quotes (all accurate) but nobody recomputed `‖w_out‖₂` for the *shipped* read-out. The rule,
matching the repo's own `ε`-double-count precedent (AUDIT F3): **exposure claims must be
evaluated against the tightest valid certificate, not against the code's own bookkeeping** —
and formalized (here, `DccnnReadout.lean`) before being externalized.
