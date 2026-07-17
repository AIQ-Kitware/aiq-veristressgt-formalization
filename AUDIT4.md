# Fourth outside audit — full-depth formalization review at the "two findings" milestone

**Date:** 2026-07-17 · **Auditor:** independent review pass (Claude, at Kitware's request).
**Scope of this audit:** (a) absolute formalization correctness and depth of the Lean
production tree at HEAD `9e7df54`; (b) fidelity to the source PDFs and the UCLA code;
(c) parity against the reference formalizations `../protected/aiq-dkps-formalization` and
`../protected/aiq-drsb-formalization` (read fresh this pass, alongside
`../REFERENCE-COMPARISON.md`); (d) **the requested decision on presenting the second
finding (`FINDING-dccnn-linf-sqrtd.md`) to UCLA**.
**Method:** re-ran `bash scripts/check.sh` from this tree (fresh output captured; PASS);
read **every line of all 28 production Lean files** and re-derived each substantive proof
by hand; mechanically diffed `AxiomAudit.lean` coverage against every `theorem` in the
sources; re-extracted pp. 18–20 of arXiv:2605.17153 (Prop. 6, eq. 44–55, Lemma 8, Props
9–10) from the PDF with pypdf; re-read `fixed_pattern.py`, `linear_dominance.py`,
`deep_contractive_cnn.py`, and `configs/mini_sweep.yaml` in the parent tree.
Item numbering continues the F→G→H sequence: this audit's items are **J1–J8**.

---

## 1. Verdict

1. **Mechanical state: PASS, independently re-verified.** `scripts/check.sh` exit 0 at
   HEAD: build clean, no `sorry`/`admit` in the seven production libraries, and all **82**
   audited declarations depend only on `{propext, Classical.choice, Quot.sound}`
   (`Verifier.sound_unsat_robust` on none). Coverage diff: exactly four trivial wrappers
   are outside the audit list (`softmax_apply`, `softmax_denom_pos`, `reluMap_apply`,
   `abs_apply_le_norm`) — nothing substantive escapes the audit (J6a).
2. **The mathematics of the production tree is correct.** I re-derived, line by line: the
   Rayleigh route to `softmax_jacobian_opNorm_le_half` (incl. the Popoviciu midpoint
   argument), `hasFDerivAt_softmax` and the mean-value reduction, both tightness
   witnesses, the three-stage fixed-pattern chain (C.1→C.3) and both concrete-instance
   discharges, the `BigMReach` soundness/completeness inductions and the capstone `iff`,
   the IBP inductions, the IVT boundary argument, and the T1′ `list_prod` instantiation.
   **No mathematical defect was found.** Statements are non-vacuous, the norms are the
   claimed ones (the `Matrix.Norms.L2Operator` scope is opened wherever `‖·‖` must be
   spectral), and every deliberate assumption boundary is a named hypothesis.
3. **Finding 1 (`attn-Lattn-n4`) stands.** Independently re-confirmed this pass from all
   three artifacts: the shipped `compute_L_attn` uses `n/4.0` on the first and third
   terms (re-read at `fixed_pattern.py:64-70`); the paper's eq. 54 uses `n/2` on both
   (re-extracted from the PDF, p. 18–19); the Lean `Z_deviation_n2` derives `n/2`
   axiom-clean. The exposure argument (shipped `margin_slack = 1.05 < 2`, CLI default
   `1.0001`) is sound *because it is evaluated against the paper's own Prop. 7 criterion*
   and carefully phrased ("unproven, not necessarily false"). No change requested.
4. **Finding 2 (`dccnn-linf-sqrtd`) must NOT be sent as drafted — its exposure claim
   (§4 of the finding) is refuted by this audit (J1, the principal finding below).** The
   Lean theorems anchoring it (`dccnn_robust_linf_box`, `dist_le_sqrt_dim_mul_linf`) are
   true and stay; what fails is the *interpretation layer*: the finding computes the
   "honest threshold" with the ℓ₁ read-out norm and concludes every shipped instance is
   ~3.6× short, but the shipped read-out row is **uniform** `1/flat_dim`, whose ℓ₂ norm
   is `1/√flat_dim` — and under the standard all-ℓ₂ Lipschitz-margin certificate (the
   very theorem this repo formalizes) the shipped margin clears the honest threshold by
   ≈ **8.8×**. The residual observation (the shipped formula is norm-incoherent as
   written, and would be unsafe for a *non-uniform* read-out) is real but is a
   **bookkeeping/robustness-of-process note, not a soundness finding**. Details and the
   required revisions in §3.
5. **Depth is at or beyond reference parity, with two claim-precision gaps.** B1–B5 of
   the reference-comparison roadmap are genuinely landed and were verified against the
   artifacts. Two status lines overstate: B6's "Lemma 8 … paper-complete" (the Lean
   theorem is the convex-combination *core* of Lemma 8's proof, not Lemma 8 as stated —
   J2), and B4's "model unification" (the bridge is single-layer only — J3).
6. **Mathlib-quality assessment:** the softmax package (definition, Fréchet derivative,
   tight `½`-Lipschitz, Loewner Jacobian pair) is genuinely PR-shaped, lean-native,
   idiomatic, and absent upstream (survey re-checked). The Challenge/comparator layer
   matches the DKPS pattern at proportionate scale (1 candidate vs. DKPS's 3+10 — the
   right size for this repo's scope). Concrete PR steps in §5 (N7).

## 2. What was verified this pass (evidence table)

| Item | Method | Result |
|---|---|---|
| `check.sh` | fresh run at HEAD `9e7df54` | PASS; 82 declarations, axioms clean |
| Audit coverage | name-diff of `#print axioms` list vs every source `theorem` | complete except 4 trivial wrappers (J6a) |
| Softmax Rayleigh proof | re-derived: variance identity, Popoviciu via max/min midpoint, sup-Rayleigh | correct; `½` tight |
| `hasFDerivAt_softmax` | re-derived quotient rule + covector-vs-Jacobian-row match | correct |
| Tightness witnesses (B3) | re-derived eigenvector `(1,−1)` at `a=(½,½)`; `le_of_lipschitz` route | correct |
| Fixed-pattern chain | re-derived C.1 (bilinear), C.2 (½-contraction), C.3 (product rule, `‖a‖₁=1` value path), `√n` poolings | correct; matches paper eq. 50–55 term-by-term |
| Concrete instances (B1) | re-checked `hρ`/`hδV`/`hw`/`hV` discharges vs `fixed_pattern.py` / `linear_dominance.py` quantities | faithful; `dw` conservative in the safe direction, documented |
| Prop. 6 (B2) | PDF p. 18 vs `dotProductAttn_pattern_stable` | faithful specialization (`M = αI`, unit tokens, uniform `2·B_S·ε` ≥ the paper's per-pair `C_ij·ε`) |
| Lemma 8 / Props 9–10 (B6) | PDF pp. 19–20 vs `attn_dominant_key_bound` | **core inequality only** — see J2 |
| `BigMReach` | re-derived both inductions + capstone `iff`; stable-neuron footnote checked vs `exact_radius.py` | correct |
| IBP / trace | re-derived `ibp_term_lb/ub` sign splits, both inductions | correct |
| T1′ | re-checked `list_prod` instantiation and `foldr` orientation note | correct |
| Finding 1 | code re-read (`n/4.0` present), PDF eq. 52/54 re-extracted (`n/2`), Lean anchor re-read | **stands** |
| Finding 2 | independent re-derivation with the shipped read-out; `setup_output_layer`, `_write_vnnlib`, CLI defaults, `mini_sweep.yaml` re-read | **exposure claim refuted** (J1) |
| Resource-tally hook | `git config core.hooksPath` | installed (`.llm_resource_tally/tool/hooks`) |

## 3. J1 · PRINCIPAL FINDING — the DCCNN `√d` finding's exposure claim is wrong; do not send as drafted

**The decision requested:** do **not** present `FINDING-dccnn-linf-sqrtd.md` to UCLA in
its current form. Its §4 ("every shipped DCCNN instance fails its own certificate
condition … ≈3.6× short") is incorrect. Revise per below before any external use.

**The error.** The finding treats `L = σ_proj·λ^D·‖w_out‖₁` as *the* Lipschitz constant
of the margin and derives the honest L∞-box threshold `L·√d·ε`. But the margin functional
is `g(x) = ⟨w_out, h(x)⟩ + B` (competitor rows and biases are zeroed —
`setup_output_layer` re-read this pass), and the shipped read-out row is **uniform**:
`fc.weight[label] = 1/flat_dim` with `flat_dim = channels·H·W`. By Cauchy–Schwarz the
tight pairing is the all-ℓ₂ chain

    |Δg| ≤ ‖w_out‖₂ · σ_proj · λ^D · ‖Δx‖₂ ≤ ‖w_out‖₂ · σ_proj · λ^D · √d · ε ,

and for the uniform row `‖w_out‖₂ = 1/√flat_dim` while `‖w_out‖₁ = 1`. At the shipped
defaults (`in_channels=1, H=W=8` ⟹ `d = 64`, `channels = 16` ⟹ `flat_dim = 1024`):

    honest threshold  = (1/32)·σλ^D·8·ε = 0.25·σλ^D·ε
    shipped margin  B = 1.1·cert_bound = 2.2·σλ^D·ε        (slack analysis of §4 was right)

so the shipped margin clears the honest requirement by **8.8×** — the construction's
labels are *proven* robust by the repo's own certificate theorem (`dccnn_robust_linf_box`
instantiated with the true operator norm `‖φ‖ = ‖w_out‖₂`), not "unproven as shipped."
The finding's §2 parenthetical ("the `√d` gap is present under either reading") is the
precise wrong step: the ℓ₁ reading `|⟨w,Δh⟩| ≤ ‖w‖₁·‖Δh‖_∞ ≤ ‖w‖₁·‖Δh‖₂` is valid but
loose; the ℓ₂ reading is valid *simultaneously* and 32× tighter here, and an instance is
exposed only if **no** valid reading certifies it.

**The general safety condition** (worth machine-checking, step N1): the code's
`cert_bound = σλ^D·2ε·‖w‖₁` dominates the honest all-ℓ₂ threshold iff

    √d · ‖w‖₂ ≤ 2 · ‖w‖₁ .

For the uniform row this is `√d ≤ 2·√flat_dim`, i.e. `in_channels ≤ 4·channels` — true
for every shipped and every reachable CLI configuration (`in_channels = 1`). For a
*generic* (e.g. one-hot) read-out with `‖w‖₁ ≈ ‖w‖₂` it fails as soon as `d > 4` — which
is the true, surviving content of the finding.

**What survives, and how to re-scope it:**
- The Lean theorems are untouched and remain valuable: `dccnn_robust_linf_box` is the
  honest certificate; `dist_le_sqrt_dim_mul_linf` is the correct conversion. Nothing in
  the production tree asserted the exposure claim — the over-claim lives in the finding
  doc, the `DccnnLInfBox.lean` *header comment*, `STATUS.md`, `README.md` findings §2,
  and the `formalization.yaml`/`ucla-formalization-edges.md` edge records.
- Re-scope the edge `dccnn-linf-sqrtd-metric` from "CONFIRMED code bug, high, unsafe" to
  a **norm-bookkeeping observation** (severity LOW/MEDIUM): the shipped formula is not a
  coherent single-norm certificate (spectral chain × ℓ₁ read-out × a `2` that is a
  diameter convention, over an L∞ box), and is safe for the shipped uniform read-out
  only by the accident `‖w‖₁/‖w‖₂ = √flat_dim ≫ √d/2`. If UCLA ever varies the read-out
  (class-dependent rows, non-uniform weights), the missing `√d` bites silently. That is
  a fair *process* note to include alongside the n/4 conversation — clearly labeled as
  "no shipped instance is exposed."
- **Caveat that keeps the analysis honest:** all of the above (both the finding's
  version and this correction) is computed against the code's *own* per-layer constants
  `σ_proj, λ`. Those come from power iteration on the **reshaped kernel matrix**
  (`_spectral_norm_power_iter` reshapes `(K,C,kH,kW) → (K, C·kH·kW)`), which is exact
  for the 1×1 projection but is *not* the conv-operator norm for the 3×3 layers — that
  is the separate, still-open `dccnn-L-power-iter` edge (edges Appendix A), unaffected
  by this correction and still the strongest remaining DCCNN concern.

**Why this got past three audits:** the finding was reviewed for internal consistency
and for the code/paper quotes (all accurate), but nobody recomputed `‖w_out‖₂` for the
*shipped* read-out — the exposure analysis inherited the ℓ₁ constant from
`compute_true_lipschitz_bound`'s docstring. The lesson matches the repo's own precedent
(AUDIT F3, the ε double-count): **exposure claims must be evaluated against the
tightest valid certificate, not against the code's own bookkeeping** — formalize the
comparison (N1) before externalizing a finding.

## 4. Secondary findings (correctness of claims, not of proofs)

- **J2 · MEDIUM (claim precision, B6).** `attn_dominant_key_bound` proves
  `‖∑ aⱼVⱼ − V_{j*}‖ ≤ (1 − a_{j*})·M` for a probability vector — the eq. 60–61 core of
  Lemma 8's *proof*. Paper Lemma 8 (p. 19, re-extracted) is stated with the **dominance
  condition** `w*_i ≥ ρᵢ·∑_{j≠j*} w_ij` on *unnormalized* weights and concludes with
  `1/(1+ρᵢ)`; the bridging step eq. 59 (`a_{j*} ≥ ρ/(1+ρ)`) and the downstream Props 9
  (three-term insertion bound) and 10 (the actual certificate) are not formalized, and
  `prose/` contains **no transcription of A.7** (the repo's own faithfulness rule
  requires one). The status line "linear-dominance paper-complete" overstates; either
  finish A.7 (step N2 — recommended, it is a half-day) or re-word to "Lemma 8 core".
- **J3 · LOW (claim precision, B4).** The model bridge is the *single-layer*
  `Layer.toAffLayer_eval`; the list-level statement (the two network models compute the
  same *network*) is absent, and is subtler than it looks because `netMap` is
  head-outermost while `netEval` is head-first — see step N4 for the exact orientation-
  correct statement. "Unify network models" in `STATUS.md` should say "single-layer
  bridge" until N4 lands.
- **J4 · LOW (hand-drawn identification).** The identification of the Lean budget `fpK`
  with the paper's eq. 54 `L_attn(ε)·ε` (and hence with `compute_L_attn`'s three terms)
  is done by expansion *in the finding doc*, not in Lean. It is a 5-line `ring` lemma
  (N3) and would make the n/4 finding's "term-by-term match" machine-checked end-to-end.
- **J5 · LOW (record drift).** `STATUS.md` says "commit checked `f442d23`" but reports
  "82 audited declarations" — at `f442d23` the count was 81 (B6's declaration landed in
  `8e1cd5f`; commit `53834aa` even says "correct audit count to 81"). The count was
  bumped without re-dating the verification record. **Superseded by this audit:** the
  fresh `check.sh` run at `9e7df54` verifies 82. Update `STATUS.md`'s "Latest
  verification" to this audit's run (N6).
- **J6 · LOW (hygiene nits).** (a) Add the four uncovered trivial declarations to
  `AxiomAudit.lean` for 100% coverage. (b) Stale comment counts in `AxiomAudit.lean`
  section headers ("ForMathlib (4)" lists 6, etc.). (c) Stale `FLAG(build)` comment in
  `SoftmaxJacobianBound.lean` (`softmaxJac_isHermitian` — the flag's contingency never
  fired). (d) `fpK` docstring says "`m` = number of tokens"; the `√m` in `fpK` is the
  ℓ¹→ℓ² pooling over the *keys* of one row (both equal `n` here, but the docstring
  should say keys). (e) Duplicated `√·`-pooling proofs: `zflat_deviation` appears twice
  (GatedAttn / FixedPatternAttn) and `euclid_dist_le_sqrt_card_mul` ≅
  `dist_le_sqrt_dim_mul_linf` — the latter duplication is documented as deliberate
  (library independence), the former could share a `ForMathlib` lemma; optional.

## 5. Next formalization steps — specified for a mathematician

Each step is written to be single-interpretation: exact statements, files, and the
Mathlib lemmas expected to carry the proof. Order = recommended priority.

### N1 — Machine-check the corrected DCCNN account (closes J1's Lean side; ~half day)

New file `LipschitzMargin/DccnnReadout.lean` (import `Mathlib`,
`LipschitzMargin.DccnnLInfBox`):

1. **Read-out operator norm.** For `w : EuclideanSpace ℝ (Fin m)`, the margin read-out
   is `innerSL ℝ w : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ`. State
   ```
   theorem readout_opNorm (w : EuclideanSpace ℝ (Fin m)) : ‖innerSL ℝ w‖ = ‖w‖
   ```
   Proof: Mathlib `innerSL_apply_norm` (real inner-product space). If the name has
   drifted, `norm_innerSL_le` + the witness `w/‖w‖` gives `le_antisymm`.
2. **Uniform read-out norms.** For `wU : EuclideanSpace ℝ (Fin m)` defined by
   `wU = toLp 2 (fun _ => (1 : ℝ)/m)` (assume `[NeZero m]`):
   ```
   theorem uniform_readout_l2  : ‖wU‖ = 1 / Real.sqrt m
   theorem uniform_readout_l1  : ∑ i, |ofLp wU i| = 1
   ```
   Proofs: `EuclideanSpace.norm_eq` + `Real.sqrt_eq_iff` arithmetic; `Finset.sum_const`.
3. **The safety comparison (the corrected LM-4 statement).** For `d m : ℕ`, `ε ≥ 0`,
   `L₀ ≥ 0` (the chain constant `σ_proj·λ^D`):
   ```
   theorem uniform_readout_code_bound_dominates
       (h : d ≤ 4 * m) :
       (1 / Real.sqrt m) * L₀ * (Real.sqrt d * ε) ≤ L₀ * (2 * ε)
   ```
   Proof: reduce to `Real.sqrt d ≤ 2 * Real.sqrt m` via
   `Real.sqrt_le_sqrt (by exact_mod_cast h)` and `Real.sqrt_mul_self`/`sqrt_le_sqrt`
   plumbing (`√(4m) = 2√m`).
4. **The end-state corrected certificate.** Instantiate `dccnn_robust_linf_box` with
   `g = fun x => innerSL ℝ w (netMap Ls x) + B` and `L = ‖w‖₊ * (Ls.map (‖·.W‖₊)).prod`
   (from `dccnn_margin_lipschitz` — note `LipschitzWith` is translation-invariant, so
   `+ B` needs only `LipschitzWith.add_const` or a two-line wrapper). Conclusion:
   ```
   theorem dccnn_uniform_readout_robust … :
       ((‖wU‖₊ * (Ls.map (fun L => ‖L.W‖₊)).prod : ℝ≥0) : ℝ) * (Real.sqrt d * ε)
           < innerSL ℝ wU (netMap Ls x₀) + B →
       ∀ x, (∀ i, |ofLp x i - ofLp x₀ i| ≤ ε) → 0 < innerSL ℝ wU (netMap Ls x) + B
   ```
5. **Doc pass (same commit):** rewrite `FINDING-dccnn-linf-sqrtd.md` per §3 (keep §1–§2
   quotes, replace §3–§6 with the corrected account and the general safety condition);
   downgrade the edge in `formalization.yaml` + `ucla-formalization-edges.md` to
   `kind: norm-bookkeeping`, `status: NOT-EXPOSED-AS-SHIPPED`; fix the
   `DccnnLInfBox.lean` header, `README.md` findings §2, `STATUS.md` finding 2, and the
   memory/AGENTS status lines. Add the audit banner cross-reference.

### N2 — Complete paper A.7: Lemma 8 as stated, Props 9 and 10 (closes J2; ~1 day)

Extend `SelfAttention/DominantKey.lean` (or a sibling `DominantKeyCert.lean`); first
add the missing transcription `prose/dominant-key-linear-attention.md` (A.7 verbatim
structure: dominance condition (7), Lemma 8, eq. 59–61, Prop 9 eq. 63–67, Prop 10
eq. 68–71).

1. **Normalized linear-attention weights.** For unnormalized weights `w : Fin n → ℝ`
   with `hw : ∀ j, 0 < w j`:
   ```
   noncomputable def linAttnWeight (w : Fin n → ℝ) (j : Fin n) : ℝ := w j / ∑ k, w k
   theorem linAttnWeight_nonneg / linAttnWeight_sum_one   -- discharge via positivity, div_self
   ```
2. **Eq. 59 — dominance ⟹ weight lower bound.** With `S := ∑ j ∈ univ.erase jstar, w j`:
   ```
   theorem dominant_weight_bound (hw : ∀ j, 0 < w j) (ρ : ℝ) (hρ : 0 ≤ ρ)
       (hdom : ρ * (∑ j ∈ Finset.univ.erase jstar, w j) ≤ w jstar) :
       1 - linAttnWeight w jstar ≤ 1 / (1 + ρ)
   ```
   Proof sketch (all elementary): `∑ k, w k = w jstar + S`
   (`Finset.sum_erase_add`/`add_sum_erase`), `1 − a_{j*} = S/(w_{j*}+S)`, then
   `S/(w*+S) ≤ 1/(1+ρ) ⟺ (1+ρ)·S ≤ w* + S ⟺ ρ·S ≤ w*` via `div_le_div_iff`
   (denominators positive from `hw`). Requires `n ≥ 1`; if `n = 1` the erase-sum is `0`
   and the statement is trivial.
3. **Lemma 8 verbatim.** Compose 2 with the existing `attn_dominant_key_bound`
   (instantiated at `a = linAttnWeight w`, using `hM : 0 ≤ M` obtainable from `hM` at
   any competitor, or add `[NeZero n]`-guarded `M`-nonnegativity as a hypothesis when
   `n = 1` makes the competitor set empty):
   ```
   theorem attn_dominant_key_bound_rho … :
       ‖(∑ j, linAttnWeight w j • V j) - V jstar‖ ≤ (1 / (1 + ρ)) * M
   ```
   (One-line: `(attn_dominant_key_bound …).trans (mul_le_mul_of_nonneg_right
   (dominant_weight_bound …) hM0)`.)
4. **Prop 9 — output perturbation.** Hypotheses (all data/derivable seams, mirroring
   the paper's quantities): per-row dominance at both `X` and `X₀` with the *same*
   `jstar i` and uniform `ρ`; nominal spread `hDV : ∀ i, ∀ j ≠ jstar i,
   ‖V₀ j − V₀ (jstar i)‖ ≤ DV`; value drift `hLV : ∀ j, ‖V X j − V₀ j‖ ≤ εLV`.
   Conclusion, per row `i` (paper eq. 63):
   ```
   ‖Z X i - Z X₀ i‖ ≤ (2 / (1 + ρ)) * DV + (1 + 2 / (1 + ρ)) * εLV
   ```
   Proof shape = paper eq. 64–67: triangle through `V X (jstar i)` and `V₀ (jstar i)`,
   Lemma 8 at `X` (with spread bounded by `DV + 2·εLV` via add/subtract nominal values)
   and at `X₀` (spread `DV`), middle term `hLV`. All steps are `norm_add₃_le`/
   `norm_sub` triangle plumbing plus the two Lemma-8 applications.
5. **Prop 10 — the certificate.** Define `Δlin := (2/(1+ρ))·DV + (1+2/(1+ρ))·εLV` and
   reuse the existing pooling/margin machinery verbatim (`zflat_deviation`,
   `margin_deviation` pattern from `LinearDominanceBlock`, `robust_of_deviation_lt_margin`):
   `hmargin : ∀ k ≠ y, 2·‖Whead‖·(√n·Δlin) < margin … X₀ ⟹ robust on the box`.
6. Add all new theorems to `AxiomAudit.lean`, update `formalization.yaml`,
   `theorem-map.md`, and the B6 status line ("Lemma 8 + Props 9–10, paper-complete").

### N3 — The `fpK` = eq. 54 expansion lemma (closes J4; ~1 hour)

In `SelfAttention/FixedPatternConcrete.lean`:
```
theorem fpK_eq_Lattn_mul_eps (n : ℕ) (BS ε σV sqrtd Vmax : ℝ) :
    fpK n (Real.sqrt n * BS * ε) (σV * sqrtd * ε) Vmax
      = ((n : ℝ)/2) * BS * ε * Vmax
        + σV * sqrtd * ε
        + ((n : ℝ)/2) * BS * ε * (σV * sqrtd * ε) := by
  unfold fpK; have h := Real.mul_self_sqrt (n := n) …; ring_nf; linear_combination …
```
(Exact three-term match to paper eq. 54 × ε with `σV·sqrtd = √d·‖W_V‖`; the only
non-`ring` step is `√n·√n = n`.) Cite it from `FINDING-attn-Lattn-n4.md` §1 so the
term-by-term match is machine-checked, and add to `AxiomAudit.lean`.

### N4 — List-level model bridge (closes J3; ~half day)

In `LipschitzMargin/DccnnLInfBox.lean`. **Orientation trap (spell it exactly):**
`netEval (L :: rest) x = netEval rest (L.eval x)` applies the head *first*, while
`netMap (L :: Ls) = L.map ∘ netMap Ls` applies the head *last*. The correct statement
therefore reverses the list:
```
theorem netMap_reverse_toAffLayer_eval {n : ℕ} (net : List (IntervalBounds.Layer n))
    (x : Fin n → ℝ) :
    ofLp (netMap ((net.map Layer.toAffLayer).reverse) (toLp 2 x)) = netEval net x
```
Proof: induction on `net`; the cons case is
`netMap (l.reverse ++ [head])` — prove the auxiliary
`netMap (Ls ++ [L]) = netMap Ls ∘ L.map` first (induction, `List.foldr_append`), then
apply the single-layer `Layer.toAffLayer_eval` and the IH. Corollary worth stating:
the T1′ product constant certifies `netEval` networks directly —
`LipschitzWith (∏ ‖(toAffLayer Lᵢ).W‖₊) (fun x => toLp 2 (netEval net x))`-shaped, via
`netLipschitz` on the reversed mapped list (`List.prod_reverse` handles the constant).
Update the B4 status line once landed.

### N5 — Heterogeneous-width layers (long-standing F8; optional, ~1–2 days)

Only if real MLP shapes are wanted without zero-padding. Exact plan:
```
inductive Layer : ℕ → ℕ → Type
  | affine {n m : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Layer n m
  | relu   {n : ℕ} : Layer n n
inductive Net : ℕ → ℕ → Type
  | nil  {n : ℕ} : Net n n
  | cons {n m k : ℕ} : Layer n m → Net m k → Net n k
```
Port `eval`/`propLower`/`propUpper`/`netEval`/`netProp`/`sound`/`ibp_network_sound` by
the same inductions (`ibp_affine_sound` is already stated for rectangular `W`); port
`BigMReach` and its two inductions identically (they never use squareness). Keep the
constant-width versions as the default consumers or deprecate them; expect no new
mathematics, only plumbing.

### N6 — Record + hygiene commit (~1 hour)

(a) `STATUS.md`: new "Latest verification" block — date 2026-07-17, commit `9e7df54`,
`check.sh` PASS, 82 declarations (fixes J5); finding 2 re-scoped per N1.5.
(b) `AxiomAudit.lean`: add `softmax_apply`, `softmax_denom_pos`, `reluMap_apply`,
`abs_apply_le_norm`; fix the section-header counts (J6a/b).
(c) Delete the stale `FLAG(build)` comment; fix the `fpK` docstring "tokens"→"keys"
(J6c/d).

### N7 — Mathlib PR execution for the softmax package (when ready to start upstreaming)

The package is ready in substance; the steps are mechanical:
1. Target files upstream: `Mathlib/Analysis/SpecialFunctions/Softmax/Basic.lean`
   (definition, `softmax_nonneg/sum_one/apply`, `hasFDerivAt_softmax`,
   `lipschitzWith_softmax`) and `…/Softmax/JacobianBound.lean` (`softmaxJac`, the
   variance lemmas un-`private`d, `softmax_jacobian_opNorm_le_half`,
   `softmaxJac_posSemidef`, `two_smul_softmaxJac_le_one`, both tightness witnesses).
2. Strip the `VeriStressGT.ForMathlib` namespace; generalize `Fin n` to an arbitrary
   `[Fintype ι] [Nonempty ι]` index where it costs nothing (the Jacobian/variance
   lemmas generalize verbatim; `hasFDerivAt_softmax` needs `EuclideanSpace ℝ ι` only).
3. Open the PR with the Loewner pair + norm bound + tightness as one unit (maintainers
   ask for sharpness first — B3 already supplies it); keep `lipschitzWith_softmax` +
   derivative as the follow-up PR. Cross-link `Challenge/MathlibCandidate/Softmax/`
   conformance stubs as the tracking artifact, per the DKPS pattern.

### N8 — Non-Lean adjunct (unchanged from AUDIT3 H1, still open)

One empirical corner/PGD check on a shipped fixed-pattern instance to learn whether any
n/4-affected label is actually *false* rather than unproven — worth attaching to the
ongoing UCLA conversation. (For DCCNN, per J1, no such check is needed: the labels are
proven robust by the corrected account, modulo the separate power-iteration edge.)

## 6. Standing of the overall product (bottom line)

The production tree is mathematically sound, mechanically verified end-to-end, and its
statement fidelity to the PDFs and the shipped code is high — including the honest
labeling of every deliberate assumption boundary. Reference parity (DKPS/DRSB
discipline R1–R3) is met: no published theorem is assumed anywhere, concrete instances
discharge the derivable seams, tightness is machine-checked, and the process artifacts
(check gate, dated status, per-declaration yaml, Challenge layer) are all present at
proportionate scale. The repo's two externally-facing findings now split: **finding 1
(n/4) is confirmed at full strength and is correctly with UCLA; finding 2 (√d) is
refuted as an exposure claim by this audit and must be re-scoped to a norm-bookkeeping
note before any external presentation** — the corrected mathematics is itself a good
advertisement for the method, since both the original over-claim and its refutation are
settled by the same machine-checked certificate theorem instantiated with the right
operator norm. Highest-value next Lean work: N1 (correct the record in Lean and docs),
N2 (finish A.7), N3/N4 (close the two hand-drawn identifications).
