# IBP soundness, the convex-relaxation barrier, and linear-region counting

**Primary sources:**
- S. Gowal et al., *On the Effectiveness of Interval Bound Propagation for
  Training Verifiably Robust Models*, 2018. **arXiv:1810.12715** (IBP).
- H. Salman, G. Yang, H. Zhang, C.-J. Hsieh, P. Zhang, *A Convex Relaxation
  Barrier to Tight Robustness Verification of Neural Networks*, NeurIPS 2019.
  **arXiv:1902.08722**.
- G. Montúfar, R. Pascanu, K. Cho, Y. Bengio, *On the Number of Linear Regions
  of Deep Neural Networks*, NeurIPS 2014. **arXiv:1402.1869** (Montúfar's own
  foundational result — directly relevant since UCLA = his group).

**Grounds:** the **Difficulty Profile**, `difficulty_profile/components.py`.
These theorems are not certificates of any single instance's robustness; they are
the theory behind the *hardness coordinates* VeriStressGT reports:
`unstable_frac`, `ibp_relative_gap`, `A_tau_effective_log`, `margin_sample_min`,
`effective_grad_dim_mean`.

---

## 1. Interval Bound Propagation — soundness (why `unstable_frac`/`ibp_*` mean something)

IBP propagates an axis-aligned box `[l,u]` through the network:
- affine `Wz+b`: `l' = W⁺l + W⁻u + b`, `u' = W⁺u + W⁻l + b` (split by sign of `W`);
- ReLU: `[max(0,l), max(0,u)]`.

> **Theorem (IBP soundness).** The propagated `[l,u]` **contains** the true range
> of every neuron over the input box. Hence if the output margin lower bound
> `ibp_margin_lb > 0`, the instance is certifiably robust (a *sufficient*
> certificate), and IBP's per-neuron `[l,u]` validly feeds the exact MILP
> (Theorem A in [`exact-milp-and-npcompleteness.md`](exact-milp-and-npcompleteness.md)).

Argument: interval arithmetic is a sound abstract interpretation — each rule is a
valid over-approximation, and composition of sound over-approximations is sound.

**Difficulty coordinates that read off IBP** (`estimate_ibp_components`,
components.py:1034):
- `unstable_frac` = fraction of ReLUs with `l<0<u` on the box (line 1071). These
  are exactly the neurons that *cost a binary* in the MILP and a *relaxation
  triangle* in CROWN — the direct driver of verification hardness.
- `ibp_relative_gap` = `(sample_min_margin − ibp_margin_lb)/|sample_min_margin|`
  (line 1092): how loose IBP is vs. an empirical min-margin. Large gap ⟹ IBP
  alone cannot certify ⟹ the verifier must branch.

## 2. The convex-relaxation barrier (why loose bounds are *fundamental*, not fixable)

> **Theorem (Salman et al. 2019).** For ReLU networks there is a family of
> single-neuron convex relaxations (the "triangle" relaxation is the tightest
> layer-wise one); *no* method within this family — including LP with the optimal
> per-neuron relaxation — can close the gap to the true robust radius in general.
> There is an inherent **barrier**: a strictly positive gap between the best
> layer-wise convex bound and the exact answer, unless one branches on neurons.

This is the theoretical reason VeriStressGT's constructions can be *simultaneously*
provably robust and *hard for incomplete verifiers*: `deep_contractive_cnn` is
trivially certifiable by a **global-Lipschitz** argument (which CROWN captures)
but drives `unstable_frac` high so that a **complete** solver must branch through
the barrier. The Difficulty Profile is, in effect, an empirical map of *where on
the barrier* each instance sits.

## 3. Linear-region counting (the `A_tau` coordinates)

> **Theorem (Montúfar et al. 2014).** A ReLU network with `L` layers of width `w`
> over input dimension `d` can partition input space into as many as
> `Ω((w/d)^{d(L−1)} · w^d)` linear regions — **exponential in depth**. Each region
> is one activation pattern; the function is affine on it.

Exact robustness must, in the worst case, reason about how many *distinct
activation patterns* live in the `ε`-box — the more patterns, the more branches.
`estimate_local_region_count` (components.py:876) estimates this **`A_τ`**
quantity from **gradient fingerprints**: it samples the box, quantises normalised
margin-gradients (each activation region has a constant gradient), and reports the
Shannon **`A_tau_effective_log`** = log of the effective number of distinct
patterns seen (line 934, 983). This is a *sampled lower bound* on the region count
Montúfar's theorem upper-bounds — the empirical shadow of the linear-region
theory, authored by the same group.

## 4. Hypotheses to scrutinize (edge candidates `DP-#`)

- **DP-1 (IBP soundness vs. tightness).** IBP `[l,u]` is *sound* (contains truth)
  but arbitrarily *loose*; `unstable_frac` counts neurons IBP *cannot* stabilise,
  which over-counts true instability (a neuron IBP flags unstable may be stable
  under a tighter bound). The difficulty coordinate is a conservative proxy — an
  edge between "IBP-unstable" and "actually-splits-in-optimal-verification."
- **DP-2 (`A_tau` sampled lower bound vs. true region count).** Montúfar's count
  is a worst-case *upper* bound; the fingerprint estimator is a *lower* bound from
  finite samples + quantisation (`quantize_decimals=1`, random projection to
  `projection_dim=10`). The gap between them is unquantified — the coordinate is a
  heuristic, explicitly named `..._log_lower` (line 990).
- **DP-3 (`margin_sample_min` is not a certified margin).** The "mixed stress
  sampler" (uniform + faces + corners + gradient + PGD, line 221) gives an
  *empirical* min margin — an **upper** bound on the true worst-case margin. It is
  a difficulty diagnostic, not the certificate; the certificate is the analytic
  construction margin. Do not confuse `margin_sample_min` with the ground truth.
- **DP-4 (barrier ⟹ the card's ≥60% is architecture-attributable).** The relaxation
  barrier predicts that instances with high `unstable_frac` / large `ibp_relative_gap`
  are the ones an *incomplete-under-timeout* verifier fails — so the card's pass
  rate is not a single number but a function of where the swept instances sit on
  the barrier. The formalization edge for the *card* is: "≥60%" has no theorem;
  the Difficulty Profile is the (theory-grounded) explanation of the residual.

## 5. Formalization target (Lean)

**IBP soundness** is the clean, high-value target: `interval arithmetic ⟹ range
containment`, provable by induction over layers with monotonicity lemmas —
squarely in Mathlib `Order`/`Analysis`. It is *also* the shared dependency of the
MILP oracle (validity of `(l,u)`), so proving it once discharges a hypothesis in
two places. The relaxation barrier (Salman) and linear-region count (Montúfar) are
**cited context**, not targets: they explain the *difficulty coordinates*, which
are measurements, not theorems — record them as "no crisp per-instance theorem,"
exactly the JHU-doc verdict for Low-formalizability claims.
