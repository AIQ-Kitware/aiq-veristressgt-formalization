# Finding — DCCNN certificate omits the ℓ∞→ℓ² `√d` factor (unsafe for `d > 4`)

**Status:** CONFIRMED code-level discrepancy (2026-07-16). Machine-checked anchor:
`LipschitzMargin.dccnn_robust_linf_box` ([`LipschitzMargin/DccnnLInfBox.lean`](LipschitzMargin/DccnnLInfBox.lean)).
Second finding of the VeriStressGT formalization, structurally identical to the
`attn-Lattn-n4` finding ([`FINDING-attn-Lattn-n4.md`](FINDING-attn-Lattn-n4.md)): a missing
dimensional factor in the **unsafe** (false-UNSAT) direction.

## The claim

`cnn.deep_contractive_cnn` certifies robustness on an **L∞** ε-box using a **spectral
(ℓ²)** Lipschitz constant, without the `√d` factor that converts the ℓ∞ box radius to the
ℓ² radius the constant is valid for. The certified perturbation is therefore too small by a
factor `√d / 2` (with `d` = input dimension); for `d > 4` the shipped margin can fail to
dominate the true worst-case output deviation, so a genuine adversarial example can exist
inside a box the construction labels **UNSAT (robust)**.

## The code

`deep_contractive_cnn.py`:

```python
# L = σ_proj · λ^D · ‖w_out‖₁   — a chain of SPECTRAL (ℓ²→ℓ²) norms:
def _spectral_norm_power_iter(W, n_iter=20):   # largest singular value = ‖W‖₂
    ...
def compute_true_lipschitz_bound(model):       # line 235
    return sigma_proj * (lambda ** D) * w_out_l1

# certified perturbation (line 227):
cert_bound = sigma_proj * (model.contraction_rate ** model.depth) * 2 * eps * w_out_l1
#            └────────────────── L ──────────────────┘   × 2ε   (NO √d)
B = cert_bound + slack                          # margin set to clear cert_bound
```

The query is an **L∞** box — each input coordinate varies independently
(`_write_vnnlib`, lines 390–397):

```python
lo, hi = x0 - eps, x0 + eps                     # per-coordinate ±ε
# (assert (>= X_i lo[i])) (assert (<= X_i hi[i]))   for every i in range(d)
```

So the adversary may set *all* `d` coordinates to `±ε` simultaneously.

## The mathematics

Power iteration returns the largest singular value, i.e. the **ℓ²→ℓ²** operator norm; the
product `L = σ_proj·λ^D·‖w_out‖` is submultiplicative in ℓ² (`netLipschitz` /
`LipschitzWith.list_prod`). The Lipschitz inequality it supports is

```
|f(x) − f(x₀)| ≤ L · ‖x − x₀‖₂ .
```

Over the L∞ box `‖x − x₀‖_∞ ≤ ε`, the worst case is a corner, where

```
‖x − x₀‖₂ = √d · ε          (all d coordinates at ±ε).
```

Hence the honest robustness threshold is

```
f_y(x₀) > L · √d · ε        (dccnn_robust_linf_box).
```

The code uses `L · 2ε`. The `2` is an ℓ∞ **diameter** convention (`00-overview`), *not* the
ℓ∞→ℓ² **radius** conversion `√d`. Comparing:

```
honest:  L · √d · ε          code:  L · 2 · ε
```

For `d > 4`, `√d > 2`, so `cert_bound = L·2ε < L·√d·ε`: the code under-certifies the
perturbation, sets the margin `B` too small, and the true worst-case deviation `L·√d·ε` can
exceed `B` → a real adversarial corner inside a box labelled UNSAT. **Unsafe direction.**
(Note the `‖w_out‖₁` vs `‖w_out‖₂` choice for the read-out is a *separate*, smaller
bookkeeping question, edge LM-4; the `√d` gap above is present under either reading, since
`‖v−v'‖_∞ ≤ ‖v−v'‖₂` still routes the conv-stack ℓ² deviation into the last layer.)

## Is the slack a rescue? (the exposed regime)

`slack = max(margin_floor = 1e-3, 0.1 · cert_bound)` (lines 229–231), `B = cert_bound + slack`.
Soundness needs `B ≥ L·√d·ε`, i.e. `slack ≥ L·ε·(√d − 2)`.

- **When `0.1·cert_bound` dominates:** `0.1·(L·2ε) ≥ L·ε·(√d − 2)` ⟺ `0.2 ≥ √d − 2` ⟺
  `d ≤ 4`. So for **`d ≥ 5` the 10% slack cannot absorb the gap** — and for image-scale
  `d` (hundreds–thousands, `√d ≈ 20–50`) the deficit dwarfs the slack by orders of
  magnitude. This is the opposite of the power-iteration edge (`dccnn-L-power-iter`), whose
  ~`δ`-scale deficit *is* bounded by the 10% slack.
- **When the `1e-3` floor dominates** (very deep nets, `L = σ·λ^D·… → 0`): both the needed
  correction `L·ε·(√d−2)` and `cert_bound` vanish, so the fixed floor is a huge relative
  cushion — deep instances are accidentally safe. **The at-risk regime is shallow/moderate
  `D` with non-vanishing `L` and realistic input dimension `d`.**

## The Lean anchor

[`LipschitzMargin/DccnnLInfBox.lean`](LipschitzMargin/DccnnLInfBox.lean):

- `dist_le_sqrt_dim_mul_linf : (∀ i, |xᵢ − x₀ᵢ| ≤ ε) → dist x x₀ ≤ √d·ε` — the ℓ∞→ℓ²
  conversion, machine-checked (Cauchy–Schwarz over the `d` coordinates).
- `dccnn_robust_linf_box : (L·√d·ε < g x₀) → ∀ x in the L∞ ε-box, 0 < g x` — the honest
  certificate; the `√d` is a *derived* quantity, exactly as `Z_deviation_n2`'s `n/2` is the
  derived anchor for the `attn-Lattn-n4-pooling` finding.
- `Layer.toAffLayer_eval` — the IBP concrete-layer model and the T1′ spectral model compute
  the same map, so the ℓ∞-box (IBP) and ℓ²-spectral (T1′) accounts meet on one network.

## How to close it (make the certificate sound)

Any one of: (a) certify against `L·√d·ε` (or `L·√d·2ε` keeping the diameter convention) —
add the `√d`; (b) use ℓ∞→ℓ∞ operator norms (max abs row sum) throughout instead of spectral,
so the constant matches the L∞ box directly (no `√d` needed, but a different, generally
larger `L`); or (c) shrink `eps` by `√d` when interpreting it as an ℓ² budget — but the
VNN-LIB box is genuinely L∞, so this changes the ground-truth query. Options (a)/(b) remove
the unsafe direction.

## Action

Report to UCLA alongside the `attn-Lattn-n4` and `dccnn-L-power-iter` items. Suggested
confirmation: pick a shipped shallow DCCNN instance with `d ≥ 5`, run PGD / a complete
verifier at the box corner `x₀ + ε·sign(∇f)`; if it finds `f_k(x) ≥ f_y(x)` the "UNSAT"
label is falsified. Tracked as edge `dccnn-linf-sqrtd-metric` (Family A, high).
