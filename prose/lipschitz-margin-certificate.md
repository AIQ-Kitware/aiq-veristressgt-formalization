# Lipschitz-margin robustness certificate

**Primary source:** Y. Tsuzuku, I. Sato, M. Sugiyama,
*Lipschitz-Margin Training: Scalable Certification of Perturbation Invariance
for Deep Neural Networks*, NeurIPS 2018. **arXiv:1802.04034**.
**Supporting:** the product-of-spectral-norms Lipschitz composition bound
(Szegedy et al. 2014 §4.3; Cisse et al., *Parseval Networks*, ICML 2017;
Miyato et al., *Spectral Normalization*, ICLR 2018).

**Grounds:** `robust_constructions/cnn/deep_contractive_cnn.py` (the whole
certificate) and the *margin half* of both attention certificates
(`fixed_pattern.py`, `linear_dominance.py`), which reuse the identical
`margin > L·2ε` logic with a different `L`.

---

## 1. The theorem (margin ⟹ robustness)

Let `f : ℝᵈ → ℝᶜ` output one logit per class, let `y` be the class of `x₀`, and
define the **prediction margin**

> `M(x₀) = f_y(x₀) − max_{k≠y} f_k(x₀)`.

Let `f` be **globally `L`-Lipschitz** from the input `Lₚ` norm to the output `L₂`
norm: `‖f(x) − f(x')‖₂ ≤ L·‖x − x'‖_p` for all `x, x'`.

> **Theorem (Tsuzuku et al. 2018, Prop. 1 / Eq. 4).**
> If `M(x₀) > √2 · L · ε`, then `argmax_k f_k(x) = y` for **every** `x` with
> `‖x − x₀‖_p ≤ ε`. I.e. `x₀` is certifiably robust at radius `ε`.

The `√2` is the worst-case geometry of a *two-logit* gap: perturbing the output
can move `f_y` down and one competitor `f_k` up, and the pair `(f_y − f_k)` has
`L₂`-sensitivity `√2 · L` because it reads two coordinates of the output. When
one works directly with the **scalar margin function** `g(x) = f_y(x) − f_k(x)`
and its own Lipschitz constant `L_g`, the clean form is:

> **Corollary (scalar-margin form, used by the code).**
> If `g` is `L_g`-Lipschitz in `‖·‖_p` and `g(x₀) > L_g · ε`, then `g(x) > 0`
> on the whole `ε`-ball, so `k` never overtakes `y`.

### Argument chain
1. For any `x` in the ball, `|g(x) − g(x₀)| ≤ L_g‖x − x₀‖_p ≤ L_g ε`
   (definition of Lipschitz).
2. Hence `g(x) ≥ g(x₀) − L_g ε > 0` by the hypothesis `g(x₀) > L_g ε`.
3. `g(x) > 0` means `f_y(x) > f_k(x)`; taking the min over competitors `k`
   keeps `y` the argmax. ∎

That is the *entire* mathematical content. Everything hard is in **producing a
valid `L` (or `L_g`)**, which is the composition bound below.

## 2. The composition bound (where `L` comes from)

For a feed-forward composition `f = ℓ_m ∘ φ ∘ ℓ_{m−1} ∘ φ ∘ … ∘ ℓ_1` with affine
layers `ℓ_i(z) = W_i z + b_i` and 1-Lipschitz activations `φ` (ReLU is
1-Lipschitz), the Lipschitz constant is **submultiplicative**:

> `L ≤ ∏_i ‖W_i‖₂`  (operator/spectral norms),

because `Lip(g∘h) ≤ Lip(g)·Lip(h)` and `Lip(ℓ_i) = ‖W_i‖₂`, `Lip(φ)=1`.

**In `deep_contractive_cnn.py`.** The network is
`fc ∘ (ReLU∘Conv)^D ∘ ReLU∘Proj`. Each contractive conv is *rescaled* so its
spectral norm is exactly `λ = contraction_rate ∈ (0,1)`
(`enforce_contraction`, `_normalize_to_spectral_norm`, lines 165–168, 76–81).
The read-out `fc` reads class `y` with an `‖·‖₁ = 1` row. So the code's global
bound (`compute_true_lipschitz_bound`, line 235–239) is

> `L = σ_proj · λ^D · ‖w_out‖₁`,

and the certified perturbation bound is `cert_bound = L · 2ε` (line 227; the
`2ε` is the box diameter, see `00-overview`). The margin `B = f_y(x₀)` is then
*set* (line 231) to `cert_bound + slack`, forcing `M(x₀) > cert_bound` — the
corollary's hypothesis — by construction. Contraction (`λ < 1`) makes `λ^D` shrink
with depth `D`, so a deep stack has a *tiny* certified bound and a huge margin
slack: trivially robust to a Lipschitz-aware verifier (CROWN), but the many ReLU
layers create an exponential search for a CDCL/branch verifier — the intended
"easy for CROWN, hard for complete solvers" stress.

## 3. Hypotheses to scrutinize (edge candidates)

Numbered so `ucla-formalization-edges.md` can cite them (`LM-#`).

- **LM-1 (exact spectral norm → power iteration).** The composition bound needs
  the *true* `‖W_i‖₂`. The code uses **20 iterations of power iteration**
  (`_spectral_norm_power_iter`, line 64, `n_iter=20`) — a stochastic *lower-ish*
  estimate that can under- or over-shoot. If it **underestimates** `σ_proj`, the
  certified `L` is too small and `B` might not actually dominate the true bound.
  This is the single most load-bearing numerical gap.
- **LM-2 (`Lip(φ)=1` for the reshape/flatten path).** The bound assumes every
  non-affine map is 1-Lipschitz. Flatten/reshape are isometries (fine), but the
  `FlatWrapper` and ONNX export must preserve this; the certificate is stated on
  the PyTorch model, verified on the exported ONNX.
- **LM-3 (global vs. local Lipschitz).** `∏‖W_i‖₂` is a *global* constant; the
  true local Lipschitz constant on the `ε`-box can be far smaller, but never
  larger — so the certificate is **sound** (conservative). The gap only makes
  instances *easier* than advertised, never falsely UNSAT. Good direction of
  error; still an edge for "how tight is the ground truth."
- **LM-4 (`L₂` output metric vs. the code's scalar `w_out`).** Tsuzuku's `√2`
  assumes the full output vector; the code collapses to a single certified class
  with `‖w_out‖₁` and works with `2ε` diameter. The bookkeeping (`√2` vs. `2`,
  `L₂` vs. `L∞→L₁` duality) must match the VNN-LIB `L∞` box exactly — an easy
  place for an off-by-a-constant that either loosens (safe) or, if wrong,
  invalidates the ground truth.
  **RESOLVED (2026-07-16) — SECOND FINDING.** The spectral (ℓ²) constant `L` is
  applied to the `L∞` ε-box with `2ε` and **no `√d`**: the honest ℓ∞→ℓ² radius is
  `√d·ε`, so the honest threshold is `L·√d·ε`, not `L·2ε`. For input dim `d > 4`
  the code under-certifies (unsafe / false-UNSAT). Machine-checked anchor
  `LipschitzMargin.dccnn_robust_linf_box`; see `FINDING-dccnn-linf-sqrtd.md`,
  edge `dccnn-linf-sqrtd-metric`.
- **LM-5 (empirical check is not a proof).** `verify_certificate_empirically`
  (line 307) samples **20 000** random `δ` and checks all-correct. This is a
  *sanity test of the construction*, not a certificate; a passing empirical check
  with a broken analytic bound would still ship a mislabeled instance. The
  analytic inequality is the ground truth; the sampling is a guard.

## 4. Formalization target (Lean)

The scalar-margin corollary is a *two-line* Lean lemma over a
`LipschitzWith L_g g` hypothesis and a real inequality — directly in Mathlib's
`Topology.MetricSpace.Lipschitz` + `order` territory, no measure theory. The
reusable piece is the **composition bound** `LipschitzWith (∏ Lᵢ) (comp …)`,
which Mathlib already has as `LipschitzWith.comp`; the spectral-norm identity
`Lip(x ↦ Wx) = ‖W‖₂` is the one lemma worth staging in a `ForMathlib`-style file.
The edges LM-1/LM-4 are then explicit `sorry`-free side-conditions relating the
*constructed* weights to the hypotheses — the honest seam between "proved for the
ideal `L`" and "shipped with a power-iteration `L̂`."
