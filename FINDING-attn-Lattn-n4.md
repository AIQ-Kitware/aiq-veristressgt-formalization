# Finding: `compute_L_attn` uses `n/4` where the paper (and a machine-checked proof) require `n/2`

**Status:** CONFIRMED code-vs-paper discrepancy · **Severity:** high (unsafe direction) ·
**Edge:** `attn-Lattn-n4-pooling` · **Lean anchor:**
`VeriStressGT.SelfAttention.FixedPatternAttn.Z_deviation_n2`
(`SelfAttention/FixedPatternBlock.lean`) · **Date:** 2026-07-10

This resolves, from the primary sources, the adjudication that AUDIT2.md (G2) had deferred
to UCLA. **The shipped code contradicts its own paper**; the paper (and our Lean proof) are
right, the code under-estimates the certified sensitivity constant by a factor of 2 on two
of its three terms, in the direction that can ship a **false-UNSAT ground-truth instance**.

---

## 1. The three artifacts

**The paper** — Troxell, Alexandr, Hunt, Lei, Montúfar, *Stress-Testing Neural Network
Verifiers with Provably Robust Instances* (arXiv:2605.17153), Appendix A.6, verbatim:

- Softmax Jacobian bound: `‖∇softmax(z)‖_op ≤ 1/2` (spectral operator norm).
- Per-row attention-weight drift (eq. 52): `‖ã_i − a_i⁰‖₁ ≤ (n/2)·ε·B̄_S(ε)`.
- Attention sensitivity constant (eq. 54):
  ```
  L_attn(ε) = (n/2)·B̄_S(ε)·‖V₀‖_{2,∞}  +  √d_tok·‖W_V‖_op  +  (n/2)·ε·B̄_S(ε)·√d_tok·‖W_V‖_op
  ```
- Block perturbation (eq. 55): `‖Attn(X) − Attn(X₀)‖_F ≤ √n·L_attn(ε)·ε`.

**The code** — `robust_constructions/attention/fixed_pattern.py`, `compute_L_attn`, verbatim:
```python
B_S    = alpha * (2.0 * math.sqrt(d) + epsilon * d)
L_attn = (
    (n / 4.0) * B_S * V0_inf                              # ← n/4, paper eq.54 has n/2
    + math.sqrt(d) * sigma
    + (n / 4.0) * B_S * epsilon * math.sqrt(d) * sigma    # ← n/4, paper eq.54 has n/2
)
```
`B_S`, the middle term `√d·σ(W_V)`, and the outer `√n` (in `rhs_margin = 2·L_h·√n·L_attn·ε`)
all match the paper. **Only the two `n`-terms differ: code `n/4`, paper `n/2`.**

**The Lean proof** — `FixedPatternAttn.Z_deviation_n2` derives, from the score-row deviation
`ρ = √n·B_S·ε`, the value deviation `δV`, and the nominal value bound `Vmax`:
```
‖ΔZᵢ‖ ≤ (n/2)·B_S·ε·(Vmax + δV) + δV
```
axiom-clean, consuming `ForMathlib.lipschitzWith_softmax` (the *spectral* `‖J‖_op ≤ ½`, itself
proved from `softmax_jacobian_opNorm_le_half`). Its leading coefficient **is `n/2`.**

## 2. The derivation (why `n/2` is correct)

Per token `i`, output row `Zᵢ = Σⱼ aᵢⱼ · Vⱼ` with `aᵢ = softmax(Sᵢ)`, `Sᵢ ∈ ℝⁿ` the score row.

1. **Score row**: each entry moves by `≤ B_S·ε`, so `‖ΔSᵢ‖₂ ≤ √n · B_S·ε` (ℓ² over `n` entries).
2. **Softmax contraction** (the crux): softmax is `½`-Lipschitz in ℓ² because its Jacobian
   `J = diag(a) − a aᵀ` has **spectral** norm `‖J‖_op ≤ ½`. Hence
   `‖Δaᵢ‖₂ ≤ ½·‖ΔSᵢ‖₂ ≤ ½·√n·B_S·ε`.
3. **ℓ¹ pooling**: `‖Δaᵢ‖₁ ≤ √n·‖Δaᵢ‖₂ ≤ (n/2)·B_S·ε` (Cauchy–Schwarz,
   `sq_sum_le_card_mul_sum_sq`). *This is exactly the paper's eq. 52.*
4. **Value mixing**: `‖Σⱼ Δaᵢⱼ Vⱼ‖ ≤ ‖Δaᵢ‖₁ · maxⱼ‖Vⱼ‖ ≤ (n/2)·B_S·ε · Vmax`.

Leading coefficient `n/2`. The value-path term is coefficient-free in `n` because
`‖aᵢ⁰‖₁ = 1` (probability vector) — matching the paper's lone `√d·‖W_V‖`.

## 3. Where `n/4` comes from — the spectral-vs-entrywise trap

The softmax Jacobian `J = diag(a) − a aᵀ` has two different "size ½/¼" facts:
- **spectral** operator norm `‖J‖_op ≤ 1/2` (the largest eigenvalue; **this** is what the ℓ²
  step 2 needs), and
- **entrywise** maximum `maxᵢⱼ|Jᵢⱼ| = maxₐ a(1−a) = 1/4` (attained on the diagonal at `a=½`).

Substituting the **entrywise** `1/4` where the ℓ² aggregation requires the **spectral** `1/2`
halves the coefficient: `n·¼ = n/4` instead of `n·½·(the √n·√n) … = n/2`. This is the precise
mechanism the audit flagged ("`¼ = maxₐ a(1−a)` is the entrywise bound — the spectral-vs-
entrywise trap"), and it is the only way to land on the code's `n/4`.

## 4. Why it matters (direction of the error)

`L_attn` enters the certificate as `rhs_margin = 2·L_h·√n·L_attn·ε`, and the construction
accepts an instance as *provably robust* when `m_X0 > rhs_margin`. A **smaller** `L_attn`
gives a **smaller** threshold, so the code certifies as UNSAT (robust) instances whose true
margin only clears the 2×-too-small bar. Because VeriStressGT's entire value proposition is
that its instances carry a **known-correct ground-truth robustness label**, such an instance
is a **false-UNSAT**: a *sound* verifier that (correctly) declines to certify it would be
wrongly scored as failing. This corrupts exactly the ground truth the stress test measures —
the class of defect this formalization-edges program exists to catch.

The cushion is `margin_slack` (the construction sets `m_X0 = margin_slack · rhs_margin`,
`margin_slack ≳ 1`, `fixed_pattern.py:239`): the construction's *own theorem* certifies an
instance only if `m_X0 > 2·L_h·√n·L_paper·ε`, and since the `n`-terms dominate `L_attn` at the
shipped parameters `L_paper ≈ 2·L_code`, this needs roughly `margin_slack ≳ 2`.

**The shipped sweeps are in the exposed regime (verified, AUDIT3 H1).** Every fixed-pattern
instance in `configs/mini_sweep.yaml` (`fp_01…fp_08`) and `configs/sweep_all.yaml` uses
**`margin_slack: 1.05`**; the CLI default (`fixed_pattern.py:202`) is `1.0001`. All are `< 2`.
So under the paper-correct `n/2` constant, `m_X0 = 1.05·(2·L_h·√n·L_code·ε) < 2·L_h·√n·L_paper·ε`
whenever the `n`-terms exceed ~5 % of `L_attn` — which they dominate (e.g. `fp_01`:
`n=16, α=5, d=4, ε=5e-4` gives first term `(n/4)·B_S·V0_inf ≈ 80·V0_inf` vs value term `2σ`).
**Therefore every shipped fixed-pattern instance fails the paper's own certificate condition:
its UNSAT ground-truth label is *unproven by the construction's theorem*** (not necessarily
*false* — the bound is sufficient, not necessary — but the benchmark's "provably robust by
construction" guarantee does not hold for the instances as shipped). An optional empirical
check (PGD / long-budget complete verifier on one instance) would tell whether any label is
actually false rather than merely unproven; either outcome is worth reporting.

## 5. What we verified ourselves vs. what to ask UCLA

**Verified from primary sources (no UCLA input needed):**
- Paper eq. 52/54 use `n/2`, derived from the spectral `‖∇softmax‖_op ≤ 1/2` (arXiv:2605.17153 §A.6).
- Kim et al. (arXiv:2006.04710, the cited attention-Lipschitz source) provide **no** `n/4` and
  **no** "symmetric-structure halving"; their bound is a different, tighter `O(√N log N)`
  (2-norm) / `O(log N)` (∞-norm, Lambert-W) result — so nothing in the literature justifies `n/4`.
- The shipped `compute_L_attn` uses `n/4` (code quoted above).
- The honest coefficient is `n/2`, machine-checked (`Z_deviation_n2`, axiom-clean).

**The single question for UCLA (now precise and minimal):**
> `compute_L_attn` uses `n/4` on the `‖V₀‖` and cross terms, but your Appendix-A.6 eq. 54 uses
> `n/2` (from `‖∇softmax‖_op ≤ 1/2`). Is the `n/4` intentional? If so, what justifies it — it is
> the *entrywise* Jacobian bound `maxₐ a(1−a)=¼`, not the *spectral* norm the ℓ² row-aggregation
> (your eq. 52) requires. If not, `compute_L_attn` under-certifies `L_attn` by 2× — and since
> every shipped fixed-pattern instance uses `margin_slack ≈ 1.05 < 2` (mini_sweep / sweep_all),
> none satisfies your own certificate condition (Prop. 7) under the corrected constant, so their
> "provably robust by construction" labels are unproven as shipped.

Raise alongside the Appendix-A power-iteration item (edge `dccnn-L-power-iter`).
