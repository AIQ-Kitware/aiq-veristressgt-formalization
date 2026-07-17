# Finding: the DCCNN certificate applies a spectral (ℓ₂) Lipschitz constant to the L∞ box without the `√d` conversion

**Status:** CONFIRMED code-level discrepancy · **Severity:** high (unsafe direction) ·
**Edge:** `dccnn-linf-sqrtd-metric` · **Lean anchor:**
`VeriStressGT.LipschitzMargin.dccnn_robust_linf_box`
(`LipschitzMargin/DccnnLInfBox.lean`) · **Date:** 2026-07-16

The `cnn.deep_contractive_cnn` construction certifies robustness over the VNN-LIB **L∞**
ε-box, but its certified perturbation multiplies a **spectral (ℓ₂→ℓ₂) Lipschitz constant** by
`2ε` with **no `√d` factor**. The honest ℓ∞→ℓ₂ radius of the box is `√d·ε`, so the honest
threshold is `L·√d·ε`. For the shipped input dimension `d = 64` this is `L·8ε` — a factor
**4× larger** than the code's `L·2ε`, in the direction that can ship a **false-UNSAT**
ground-truth instance. This is a distinct issue from the attention `n/4` finding
([`FINDING-attn-Lattn-n4.md`](FINDING-attn-Lattn-n4.md)) — a different construction and a
different mechanism (a metric-conversion factor, not a mis-substituted Jacobian bound) — but
the same *kind* of defect: a missing dimensional factor in the unsafe direction.

---

## 1. The three artifacts

**The underlying theorem** — the Lipschitz-margin certificate (Tsuzuku–Sato–Sugiyama,
NeurIPS 2018) is an **ℓ₂** statement: if a scalar margin `g` is `L`-Lipschitz *in the
Euclidean norm* and `g(x₀) > L·ε`, then `g(x) > 0` for every `x` with `‖x − x₀‖₂ ≤ ε`. The
perturbation radius `ε` is measured in the **same norm** `L` is a Lipschitz constant for —
here ℓ₂. (Transcription: [`prose/lipschitz-margin-certificate.md`](prose/lipschitz-margin-certificate.md) §1.)

**The code** — `robust_constructions/cnn/deep_contractive_cnn.py`. The network Lipschitz
constant is a chain of **spectral** norms (power iteration = largest singular value =
ℓ₂→ℓ₂ operator norm), and the certified perturbation folds in `2ε`:
```python
def _spectral_norm_power_iter(W, n_iter=20):        # largest singular value = ‖W‖₂
    ...
# each contractive conv is rescaled to spectral norm = contraction_rate (λ):
def _normalize_to_spectral_norm(conv, target): ...  # ℓ₂→ℓ₂
# certified perturbation (setup_output_layer, line 227):
sigma_proj = _spectral_norm_power_iter(model.input_proj.weight)     # ℓ₂→ℓ₂
w_out_l1   = model.fc.weight[model.label].abs().sum().item()        # = 1.0
cert_bound = sigma_proj * (model.contraction_rate ** model.depth) * 2 * eps * w_out_l1
#            └──────────────────────── L (spectral) ───────────────┘  × 2ε   (NO √d)
```
The VNN-LIB query is an **L∞** box — every input coordinate ranges *independently* over
`[x₀ᵢ − ε, x₀ᵢ + ε]` (`_write_vnnlib`, lines 390–397):
```python
lo, hi = x0 - eps, x0 + eps
# (assert (>= X_i lo[i])) (assert (<= X_i hi[i]))   for every i in range(d)
```
So an adversary may set **all `d` coordinates** to `±ε` simultaneously.

**The Lean proof** — `dccnn_robust_linf_box` (`LipschitzMargin/DccnnLInfBox.lean`) states the
honest threshold over the L∞ box, with the `√d` explicit:
```
(L·√d·ε < g x₀)  →  ∀ x with ‖x − x₀‖_∞ ≤ ε,  0 < g x
```
Its glue `dist_le_sqrt_dim_mul_linf` is the machine-checked ℓ∞→ℓ₂ conversion
`(∀ i, |xᵢ − x₀ᵢ| ≤ ε) → ‖x − x₀‖₂ ≤ √d·ε`. `Layer.toAffLayer_eval` additionally proves the
IBP concrete-layer model and this spectral-chain model compute the *same* network, so the
two accounts meet on one object.

## 2. The derivation (why `√d` is required)

The spectral constant `L = σ_proj · λ^D · ‖w_out‖` supports the Euclidean Lipschitz bound
```
|f(x) − f(x₀)|  ≤  L · ‖x − x₀‖₂ .
```
Over the L∞ box `‖x − x₀‖_∞ ≤ ε`, the worst case is a corner, where
```
‖x − x₀‖₂  =  √d · ε          (all d coordinates at ±ε).
```
Hence the honest threshold is `f(x₀) > L·√d·ε`. The code uses `L·2ε`. The `2` is an ℓ∞
**diameter** convention ([`prose/00-overview-and-provenance.md`](prose/00-overview-and-provenance.md)),
i.e. a *safe* 2× over-count of the ℓ∞ radius — but it is not the ℓ∞→ℓ₂ **radius** conversion
`√d`. Comparing:
```
honest:  L · √d · ε          code:  L · 2 · ε
```
`√d` dominates the conservative `2` as soon as `d > 4`.

(The read-out norm is a separate, smaller bookkeeping question — the code pairs `‖w_out‖₁`
with the spectral chain, edge LM-4 — but the `√d` gap is present under either reading, since
the conv-stack ℓ₂ deviation routes into the last layer via `‖·‖_∞ ≤ ‖·‖₂`. The `√d` is the
clean, machine-checked core, independent of the `√2`/`‖w_out‖₁` details.)

## 3. Why it matters (direction of the error)

The construction *sets* the margin `B = f_y(x₀)` (via the head bias, `setup_output_layer`)
to `cert_bound + slack`, forcing `f_y(x₀) > cert_bound = L·2ε`. Since the true worst-case
deviation over the box is `L·√d·ε > L·2ε` (for `d > 4`), the certificate's own inequality
does **not** rule out `f_y(x) ≤ f_k(x)` at a corner: the constructed margin is too small.
A smaller certified perturbation means the construction accepts as UNSAT (robust) an instance
whose ground-truth label its own theorem does not establish — a **false-UNSAT** in the
making, corrupting exactly the ground truth the stress test measures.

**Scope (sufficient, not necessary).** `L = σ_proj·λ^D·‖w_out‖` is a *global* Lipschitz
bound; the *true local* margin drop over the box can be smaller, so an under-certified
instance is **unproven-as-robust by the construction's theorem**, not provably non-robust.
An empirical check (PGD, or a complete verifier at the corner `x₀ + ε·sign(∇f)`) is what
distinguishes "unproven" from "actually false." Either outcome is worth reporting; the
"provably robust by construction" guarantee does not hold for the instances as shipped.

## 4. The shipped instances are in the exposed regime (verified)

Every shipped DCCNN instance in [`configs/mini_sweep.yaml`](../../ta1/VeriStressGT/src/VeriStressGT/configs/mini_sweep.yaml)
(`dc_cnn_01…07`) and `configs/sweep_all.yaml` (`dc_cnn1…`) overrides only `depth`,
`channels`, `contraction_rate` (0.90), and `margin` (0.001); none overrides the input shape,
so all use the CLI defaults `in_channels=1, height=8, width=8` — **input dimension `d = 64`,
`√d = 8`.** The honest threshold is therefore `L·8ε`, versus the code's `L·2ε`: **a 4× gap.**

The cushion is `slack = max(margin_floor = 1e-3, 0.1·cert_bound)`, `B = cert_bound + slack`
(lines 229–230). Soundness needs `B ≥ L·√d·ε = 4·cert_bound`, i.e. `slack ≥ 3·cert_bound`.

- **The 10% slack term dominates the floor for every shipped config.** `cert_bound =
  σ_proj·λ^D·2ε` with `ε = 0.02`, `λ = 0.9`; even the deepest shipped net (`D = 10`,
  `λ^D ≈ 0.35`) with `σ_proj ≈ O(1)` gives `cert_bound ≈ 0.02`, so `0.1·cert_bound ≈ 2e-3 >
  1e-3`. Hence `slack = 0.1·cert_bound` and `B = 1.1·cert_bound`.
- **So every shipped instance falls short by ≈ 3.6×**: `B = 1.1·cert_bound` covers only
  `1.1/4 ≈ 28 %` of the honest worst-case deviation `4·cert_bound`. The 10% slack was never
  going to absorb a `√d/2 = 4×` deficit — this is much larger than the `2×` attention gap,
  and (unlike the `dccnn-L-power-iter` power-iteration deficit, which the 10% slack *does*
  bound) it is not cushioned.
- Only a hypothetical instance with `cert_bound ≤ 2.5e-4` (so the `1e-3` floor dominates and
  `1e-3 ≥ 3·cert_bound`) would be safe on this account; no shipped config is that small.

**Therefore every shipped DCCNN instance fails its own certificate condition under the
correct ℓ∞→ℓ₂ metric:** its UNSAT ground-truth label is unproven by the construction's
theorem as shipped.

## 5. How to close it

Any one of: **(a)** certify against `L·√d·ε` (or `L·√d·2ε` keeping the diameter convention) —
add the `√d`; **(b)** use ℓ∞→ℓ∞ operator norms (max absolute row sum) throughout instead of
spectral norms, so the constant matches the L∞ box directly (no `√d`, but a different,
generally larger `L`); or **(c)** interpret `eps` as an ℓ₂ budget and shrink it by `√d` —
but the VNN-LIB box is genuinely L∞, so this changes the ground-truth query. Options (a)/(b)
remove the unsafe direction.

## 6. What we verified ourselves vs. what to ask UCLA

**Verified from the code + a machine-checked proof (no UCLA input needed):**
- The conv/proj Lipschitz constants are spectral (ℓ₂→ℓ₂) — power iteration returns the
  largest singular value (`_spectral_norm_power_iter`).
- The VNN-LIB query is a per-coordinate L∞ box over all `d = 64` shipped input dimensions.
- The honest robustness threshold for an ℓ₂-Lipschitz margin over that box is `L·√d·ε`
  (machine-checked `dccnn_robust_linf_box` / `dist_le_sqrt_dim_mul_linf`, axiom-clean); the
  shipped `cert_bound = L·2ε` omits the `√d`, and the 10%/1e-3 cushion is ~3.6× short on
  every shipped config.

**The question for UCLA:** the certificate multiplies a spectral (ℓ₂) constant by `2ε` over
an L∞ box. Applying the ℓ₂ Lipschitz-margin theorem to that box requires the ℓ∞→ℓ₂ factor
`√d` (= 8 for the shipped `8×8` inputs). Is the omission intentional (e.g. is the chain meant
to be ℓ∞→ℓ∞, in which case the spectral norms are the wrong operator norms)? If not,
`cert_bound` under-certifies the perturbation by `√d/2 = 4×`, and every shipped DCCNN
instance's "provably robust by construction" label is unproven as shipped. Raise alongside
the attention `n/4` item (edge `attn-Lattn-n4-pooling`) and the power-iteration item (edge
`dccnn-L-power-iter`).
