# UCLA / VeriStressGT — formalization edges (assumption → relaxation)

Status: **proposal / first pass**, 2026-07-03. This is the VeriStressGT analogue
of the JHU proof-of-concept in
[`docs/planning/ta1-formalization-edges.md`](../../docs/planning/ta1-formalization-edges.md)
§2. It draws the explicit edges the program is after:

> **edge** = (a specific theorem hypothesis — the *idealized* assumption)
> ⟶ (the specific empirical code that relaxes / approximates / drops it),
> annotated with *what kind* of relaxation and *how load-bearing* it is.

For JHU the left-hand side is a **Lean object** (a proved theorem's hypothesis).
For VeriStressGT the Lean does not exist yet, so the left-hand side is a
**published-theorem hypothesis** transcribed in [`prose/`](prose/); the Lean
column is a *forward pointer* to where that hypothesis will live once the
certificate lemmas are stated (see each prose file's "Formalization target").
The right-hand side is real, shippable code in `ta1/VeriStressGT/`.

## The two families of edge (this is the VeriStressGT-specific shape)

Because a VeriStressGT instance = **ground-truth certificate** ⊕ **verifier
stress test** (see [prose/00](prose/00-overview-and-provenance.md)), the edges
split cleanly:

- **Family A — construction edges.** The *certificate theorem's* hypotheses that
  the **construction code** discharges only *numerically*. If one of these is
  actually violated, the shipped instance is **mislabeled** (a false UNSAT). These
  are the edges that threaten ground truth. Highest value.
- **Family B — card edges.** The *verifier's* proof qualifiers that the **card**
  drops. These do not threaten ground truth; they set what the ≥60% number can and
  cannot mean.

---

## Family A — construction edges (threaten the ground-truth label)

Ordered by severity. `prose` tags (LM-#, SA-#, MILP-#, ED-#) point to the exact
"hypotheses to scrutinize" entry.

| id | Idealized assumption (theorem) | Prose | Empirical relaxation | Code site | Kind | Severity |
|---|---|---|---|---|---|---|
| `dccnn-L-power-iter` | Composition bound needs the **true** conv operator norm `‖convᵢ‖₂` (T1′) | LM-1 | **Two** unsafe under-estimates: (i) 20-step power iteration `σ̂` is a *lower* bound on the reshaped-matrix norm (**Appendix A**, bounded by 10% slack); (ii) the reshaped-kernel norm itself ≠ the true conv operator norm — for 3×3 kernels the true norm can be up to `√9 = 3×` larger (**Appendix A′**), unbounded and data-dependent. 1×1 input_proj is exact. | `deep_contractive_cnn.py:64,67` (`_spectral_norm_power_iter` reshape); used `:225,237` | numeric-estimate + metric | **high** (strongest remaining DCCNN concern) |
| `dccnn-linf-sqrtd-metric` | Honest L∞-box threshold uses the read-out's **ℓ² operator norm** `‖w‖₂` *and* the `√d` conversion: `‖w‖₂·σλ^D·√d·ε` (T1′) | LM-4 | **NOT-EXPOSED-AS-SHIPPED (AUDIT4 J1).** `cert_bound = σλ^D·2ε·‖w‖₁` is norm-incoherent but safe: the shipped **uniform** read-out has `‖w‖₂=1/√flat_dim`, so the all-ℓ² certificate clears the margin ≈`8.8×`. Safe iff `√d·‖w‖₂ ≤ 2‖w‖₁` (`in_channels ≤ 4·channels`, all shipped). Latent risk only for a **non-uniform** read-out (`d>4`). Machine-checked: `dccnn_readout_robust`, `uniform_readout_code_bound_dominates`. | `deep_contractive_cnn.py:227` (`cert_bound`); box `:390-397` | norm-bookkeeping | low (not exposed) |
| `milp-rmax-clamp` | Exact `r*` = min over **all** target classes, unbounded (T3) | MILP-1 | Search clamped to `t ≤ Rmax`; if `r* > Rmax`, returns a **lower bound**, still ships `ε=0.999·r*` | `exact_radius.py:232`; warn `:400,482` | regime-clamp | **high** |
| `milp-incomplete-label` | Label sound only if MILP solved to **`OPTIMAL`** (T3, Thm A) | MILP-2 | `TIME_LIMIT` ⇒ `INCOMPLETE`; code itself warns label "NOT reliable" | `exact_radius.py:454-469,714` | budget-drop (self-declared) | **high** |
| `poly-nbc-surrogate` | Exact radius = **distance to the algebraic variety** (T6) | ED-1 | **50-restart L-BFGS-B** "did not find a closer boundary point" — one-sided local non-existence | `algebraic_boundary.py:405` (`nearest_boundary_check`); type `:610` | exact→local-search | **high** |
| `attn-fixed-pattern-gap` | Softmax argmax pattern is **constant on the box** (T2) | SA-3 | Coherence inequality `1−μ > 4ε√d+2ε²d` checked at `X₀` only, as a *proxy* for pattern-invariance | `fixed_pattern.py:82-92,221` | proxy-condition | med |
| `float32-export` | Certificate proved in exact/`float64` arithmetic | LM-2, MILP-3, ED-4 | Model exported **float32**; verifier reads float32; `deg=10` powers amplify | `*_export`/`onnx_export.py`; `algebraic_boundary.py:599` | precision-mismatch | med (this is the paper's *headline* finding: tolerance bugs) |
| `poly-line-sampling` | Boundary = the **whole** real variety `𝒱` (T6) | ED-2, ED-3 | Boundary points only along **random lines**; `L∞` normal step is first-order | `algebraic_boundary.py:344,393` | sampling-gap | med |
| `empirical-not-proof` | The certificate **is** the analytic inequality | LM-5, DP-3 | `verify_certificate_empirically` (20 000 samples) is a *guard*, not a proof | `deep_contractive_cnn.py:307` | sanity≠certificate | low (safe) |
| `attn-Lattn-constant` | Softmax-Jacobian `n/4`·`½` aggregation is a valid bound (T2) | SA-2 | Analytic `compute_L_attn`; `σ(W_V),L_h` are **exact SVD** (contrast `dccnn-L-power-iter`) | `fixed_pattern.py:56-71` | (tight) | low |

**Headline (Family A): `dccnn-L-power-iter` + `poly-nbc-surrogate`.** These are
the two places where the *ground truth itself* rests on a numerical estimate that
could be wrong in the unsafe direction — an under-estimated Lipschitz constant, or
a missed nearer boundary point. They are the VeriStressGT counterpart of JHU's
"E1: the proved theorem is about a different estimator than the one shipped." The
difference: VeriStressGT is unusually **honest** about them — `milp-incomplete-label`
and `poly-nbc-surrogate` are *self-declared in the code's own strings*.

## Family B — card edges (bound what ≥60% can mean)

| id | Idealized (verifier spec) | Prose | Card relaxation | Code site | Kind |
|---|---|---|---|---|---|
| `card-verifier-soundness` | `verifier(x)=UNSAT ⟹ robust(x)` (T5 soundness) | CR-1 | **Assumed**, never checked — and is exactly what the paper finds violated by tolerance bugs | `cards/evaluation.yaml:49-60` | assumed-soundness |
| `card-timeout-incomplete` | β-CROWN **complete** given unbounded time (T5) | CR-2 | 60 s timeout ⇒ incomplete; hard (high-`unstable_frac`) instances time out by design | `cards/evaluation.yaml:69` | completeness→budget |
| `card-threshold-0.6` | (no theorem) | DP-4 | `correct_fraction ≥ 0.6` is an engineering threshold, not entailed by any theorem | `cards/evaluation.yaml:44-60` | empirical-threshold |
| `card-cert-mismatch` | Construction cert (global-Lipschitz) ≠ verifier cert (local linear) | CR-3 | "verifier fails" ≠ "not robust"; different proofs of the same fact | — | proof-mismatch |

## Proposed encoding (mirrors JHU §2.5 schema)

When the Lean certificate lemmas land, add an `edges:` block to a VeriStressGT
`formalization.yaml` (sibling of the DKPS one). Strawman for the headline edge:

```yaml
# formalizations/veristressgt/formalization.yaml  (future)
edges:
  - id: dccnn-L-power-iter
    card: ta1/VeriStressGT/cards/evaluation.yaml
    construction: cnn.deep_contractive_cnn
    assumption:
      theorem: "Tsuzuku 2018 (arXiv:1802.04034) + product-of-spectral-norms"
      prose: prose/lipschitz-margin-certificate.md   # LM-1
      lean: VeriStressGT.CNN.lipschitz_margin_cert    # FUTURE — not yet stated
      informal: "Certificate needs the true spectral norm ‖W_i‖₂ of each layer."
    relaxation:
      code: ta1/VeriStressGT/src/VeriStressGT/robust_constructions/cnn/deep_contractive_cnn.py
      line: 64
      informal: "σ̂ from 20-step power iteration; may under-estimate ‖W‖₂."
    kind: numeric-estimate       # numeric-estimate | regime-clamp | budget-drop |
                                  # exact→local-search | proxy-condition |
                                  # precision-mismatch | assumed-soundness
    severity: high               # high = could ship a mislabeled (false-UNSAT) instance
    note: >
      Direction of error matters: an OVER-estimate is safe (conservative cert);
      an UNDER-estimate can invalidate ground truth. A cheap fix is to certify
      with σ̂·(1+tol) or an exact SVD for the small proj layer.
```

A card-side back-pointer (`formalization_edges: [dccnn-L-power-iter, …]`) lets the
MAGNET runner show, next to a card's VERIFIED/FALSIFIED verdict, *which
construction assumptions the ground-truth label is standing on* — the same shared
vocabulary the JHU edges introduce.

## Recommended next steps (VeriStressGT-specific)

1. **Formalize the easy wins first (independent, parallelizable).** Per
   [theorem-map](theorem-map.md): (a) the scalar Lipschitz-margin corollary
   (`prose/lipschitz-margin-certificate.md` §4) — a 2-line Lean lemma; (b) the
   `linear_dominance` bilinear cert (SA-5) — softmax-free; (c) **IBP soundness**
   (`prose/ibp…` §5) — high value, it also discharges the MILP oracle's `(l,u)`
   validity. These three cover three constructions and the difficulty profile.
2. **Land the Family A edges as the first `edges:` block** once (1) gives real
   Lean anchors — starting with `dccnn-L-power-iter` and `poly-nbc-surrogate`
   (the two that threaten ground truth) plus the two self-declared ones.
3. **Record the Family B edges as the card's honest ceiling.** They are not bugs;
   they define what "≥60% @ 60 s" measures — verifier engineering on the
   relaxation barrier, not a mathematical guarantee.
4. **Feed the edges back to UCLA.** `poly-nbc-surrogate` (vs. the ED-degree exact
   method of arXiv:2602.06105) is a live subject-matter question — the polynomial
   paper is *literally* the exact method that would close it. And
   `dccnn-L-power-iter` has a firm answer now (Appendix A) worth raising: the
   error is in the *unsafe* direction, bounded by the 10% slack.

---

## Appendix A — the power-iteration Lipschitz error is *unsafe-but-bounded*

The `dccnn-L-power-iter` edge asked: does the power-iteration spectral-norm
estimate bias the certificate *safe* (conservative) or *unsafe* (could ship a
false UNSAT)? Firm answer: **unsafe direction, but bounded by the construction's
10% slack.** Derivation.

**A.1 Power iteration always *under*-estimates `‖W‖₂`.**
`_spectral_norm_power_iter` (deep_contractive_cnn.py:64–73) returns
`σ̂ = |uᵀ W v|` with `u, v` unit vectors. By Cauchy–Schwarz,
`|uᵀ W v| ≤ ‖u‖·‖W v‖ ≤ ‖u‖·‖W‖₂·‖v‖ = ‖W‖₂ = σ_max`. So for **any** finite
iteration count, `σ̂ ≤ σ_max`; equality only in the limit. Writing
`σ̂ = (1−δ)·σ_max`, the relative deficit `δ ≥ 0` shrinks geometrically as
`δ = Θ((σ₂/σ₁)^{2k})` for `k=20` iterations — tiny **unless the top two singular
values are nearly degenerate** (`σ₂/σ₁ → 1`), where convergence stalls.

**A.2 The deficit propagates in the *unsafe* direction, and compounds with depth.**
Two uses, both biased the same way:
- `enforce_contraction` rescales `W ← W·(target/σ̂)`. The resulting **true** norm
  is `σ_max·(target/σ̂) = target/(1−δ) ≥ target = λ`. So each contractive layer is
  *slightly more expansive than λ*.
- `compute_true_lipschitz_bound` reports `L_cert = σ̂_proj · λ^D · ‖w_out‖₁`,
  substituting (i) an under-estimated `σ̂_proj` and (ii) `λ^D` for the true conv
  norms `≥ λ`. Both substitutions shrink the constant. Hence
  ```
  L_true ≥ (σ_proj)·∏(true conv norms)·‖w_out‖₁
         ≥ L_cert / [ (1−δ_proj)·(1−δ_conv)^D ].
  ```
  The `(1−δ)^D` shows the deficit **compounds with depth** `D`.

**A.3 Is the shipped instance still truly robust?**
`setup_output_layer` sets margin `B = cert_bound + slack`, with
`cert_bound = L_cert·2ε` and `slack = max(margin_floor=1e-3, 0.1·cert_bound)`
(lines 227–231). True robustness needs `B > L_true·2ε`. Substituting A.2,
robustness is guaranteed as long as
```
slack  >  cert_bound · ( 1/[(1−δ_proj)(1−δ_conv)^D] − 1 )  ≈  cert_bound·(δ_proj + D·δ_conv).
```
- When `0.1·cert_bound` dominates the slack, this holds iff the **aggregate
  relative deficit** `δ_proj + D·δ_conv < 0.1` (10%). Twenty power iterations on a
  Kaiming-random conv clear this by orders of magnitude — *unless* the spectrum is
  near-degenerate.
- For **deep** nets `cert_bound = σ̂·λ^D·… → 0`, so `slack` hits the `1e-3` floor,
  which is a *huge* relative cushion over a vanishing `cert_bound` — deep instances
  are very safe. **The at-risk regime is shallow `D` with a near-degenerate top
  singular pair**, exactly where `δ_conv` is largest.

**A.4 How to close it (make the 10% empirical buffer a proof).**
Any one of: (a) certify with an **upper** bound `σ̂·(1+tol)` instead of `σ̂`;
(b) use an **exact SVD** for the input-proj and conv layers — they are small
(`≤16×16×3×3`), so exact `numpy.linalg.norm(·,2)` is cheap (this is already what
the *attention* constructions do, edge `attn-Lattn-constant`/SA-4 — an internal
inconsistency worth flagging); or (c) **re-measure** the post-normalization conv
norms and use `∏(measured)` instead of `λ^D`. Any of these removes the unsafe
direction entirely.

**A.5 Takeaway for the formalization.** In Lean this is exactly the seam between
the ideal hypothesis `L = ∏‖Wᵢ‖₂` and the shipped `L̂` — encode it as an explicit
side-condition `L̂ ≥ ∏‖Wᵢ‖₂` (an **upper**-bound hypothesis). The proof of the
margin corollary then goes through unchanged; the honest cost is that the shipped
`L̂` does **not** currently satisfy that hypothesis (it satisfies the reverse),
which is the edge, quantified.

## Appendix A′ — a *second*, distinct under-estimate: reshaped-kernel norm ≠ true conv operator norm

A.1–A.5 assumed the target of the power iteration — the spectral norm of the
**reshaped kernel** `W2d = W.reshape(K, C·kH·kW)` (`deep_contractive_cnn.py:67`) —
*is* the layer's operator norm. For a **convolution as a linear map on the H×W×C
image, it is not.** This is a separate gap from A.1–A.5 (which is about power-
iteration *convergence* to the reshaped-matrix norm), raised by AUDIT4 (J1's caveat).

**A′.1 The 1×1 input projection is exact.** `input_proj` is a `1×1` conv
(`:127`): a single spatial position, so the conv is the pointwise map
`I_{HW} ⊗ M` with `M` the `K×C` weight. Its operator norm equals `σ_max(M) =
‖reshape‖₂` exactly, so `σ_proj` is the true norm (modulo A.1's convergence).

**A′.2 The `kH×kW` contractive convs are not.** Write `M_{ij} = W[·,·,i,j]` for the
per-position `K×C` channel matrices. Decomposing the conv as a sum of shifted
pointwise maps (shifts are unitary under circular padding),

    σ_conv  ≤  ∑_{i,j} σ_max(M_{ij})          (triangle; a valid *upper* bound),

while the reshaped-matrix norm is the horizontal stack `[M_{00} | … | M_{k−1,k−1}]`,

    max_{i,j} σ_max(M_{ij})  ≤  σ_reshape = σ_max([M_{00}|…])  ≤  √(∑_{i,j} σ_max(M_{ij})²)

(the upper bound from `[M|…][M|…]ᵀ = ∑ M_{ij}M_{ij}ᵀ` and subadditivity of `λ_max`
on PSD matrices). **Neither of `σ_conv`, `σ_reshape` bounds the other in general.**

**A′.3 The gap is unsafe and up to `√(kH·kW)`.** Worst case: all spatial positions
share the *same* channel matrix `M` (`σ_max = s`). Then at the DC frequency the
conv symbol is `∑_{i,j} M_{ij} = (kH·kW)·M`, so **`σ_conv = kH·kW·s`**, whereas
`σ_reshape = σ_max([M|…|M]) = √(kH·kW)·s`. Hence

    σ_conv / σ_reshape  =  √(kH·kW)  =  3   for the shipped 3×3 kernels,

in the **unsafe** direction: the code normalizes each conv so `σ_reshape = λ = 0.9`,
but the true operator norm can be as large as `3·λ = 2.7`, and this compounds as
`3^D` over depth. For Kaiming-*random* init the per-position matrices are nearly
independent, so the DC alignment is weak and `σ_conv ≈ σ_reshape` in practice — but
this is **data-dependent, not guaranteed**, and the shipped `L̂` is not proven to
be the required *upper* bound on `∏‖convᵢ‖₂`.

**A′.4 How to settle / close it.** Compute the *true* conv operator norms exactly by
the DFT method (Sedghi–Gupta–Long, ICLR 2019, *The Singular Values of Convolutional
Layers*): `σ_conv = max_ω σ_max(Ŵ(ω))` over the 2-D DFT `Ŵ(ω) = ∑_{i,j} M_{ij}
e^{-2πi⟨ω,(i,j)⟩}` of the kernel, and certify against `∏ σ_conv` (or its upper
bound `∏ ∑_{ij} σ_max(M_{ij})`) instead of `∏ σ_reshape`. On the shipped weights
this is a few-line NumPy check per conv (`≤16×16×3×3`); the environment for this
formalization pass has no NumPy, so the numeric magnitude on the *actual* kernels is
left as the recommended empirical check to attach to the UCLA conversation.

**A′.5 Formalization seam.** This is the same `L ≤ L̂` upper-bound hypothesis as A.5,
but now the deficit has *two* independent sources — power-iteration convergence
(A.1) and reshaped-vs-true (A′.2/A′.3) — both biased unsafe. The Lean side already
carries the honest hypothesis: `LipschitzMargin.dccnn_robust_of_upper_bound` takes
`hupper : L ≤ L̂` explicitly, and the shipped `L̂ = σ_reshape` product is not proven
to satisfy it. This edge (not the refuted `dccnn-linf-sqrtd-metric`) is the strongest
remaining DCCNN concern.
