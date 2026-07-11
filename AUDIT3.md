# Third outside audit — completeness check at the "awaiting UCLA" milestone

**Date:** 2026-07-11 · **Auditor:** independent review pass (Claude, at Kitware's request).
**Claim under audit:** *the formalization is complete; the only open item is UCLA's response
to the `n/4` (code) vs `n/2` (paper + machine-checked bound) finding.* Git now exists
(`AIQ-Kitware/aiq-veristressgt-formalization`).
**Method:** re-ran `scripts/check.sh` from scratch; read every line added since AUDIT2
(commit `60c1029`) and re-checked the carried-over files; **independently verified the
paper citations against the actual PDF** (arXiv:2605.17153, pp. 18–19); re-checked the
UCLA code and, additionally, the shipped sweep configs; verified audit coverage by diffing
`AxiomAudit.lean` against every `theorem` in the sources.

---

## 1. Verdict

**The completeness claim is substantiated.** Everything AUDIT2 asked for is done and
correct, and the one thing that had to be beyond reproach — the `n/4` finding — now rests
on the strongest possible footing:

1. **I verified the paper quotes against the PDF myself.** Appendix A.6 eq. 51 (`B̄_S`),
   eq. 52 (`‖ãᵢ−aᵢ⁰‖₁ ≤ (n/2)εB̄_S`, "using the softmax Jacobian bound
   `‖∇softmax(z)‖_op ≤ ½`"), eq. 54 (`L_attn` with **`n/2`** on both `n`-terms), eq. 55
   (`√n` Frobenius pooling), and Proposition 7 (margin condition `µ > 2L_h√n L_attn ε`)
   read exactly as `FINDING-attn-Lattn-n4.md` quotes them. The shipped `compute_L_attn`
   (`fixed_pattern.py:64-70`, re-read) uses `n/4.0` on the first and third terms. **The
   code-vs-paper discrepancy is real and independently confirmed.**
2. **The Lean anchor is now the assembled bound, not numerology.**
   `FixedPatternAttn.Z_deviation` / `Z_deviation_n2` derive
   `‖ΔZᵢ‖ ≤ (n/2)·B_S·ε·(Vmax+δV) + δV` — I checked it **matches the paper's eq. 53/54
   term-by-term** (leading term, coefficient-free value path via `‖aᵢ‖₁ = 1`, cross term),
   consuming `lipschitzWith_softmax` for the ½ and Mathlib's `sq_sum_le_card_mul_sum_sq`
   for the `√n·√n`. AUDIT2's G1/G2 are genuinely closed: `fixedPattern_robust_derived`
   mirrors the paper's Proposition 7 proof shape with **no assumed Lipschitz constant**,
   and the edge's evidence is machine-checked.
3. **Mechanical state: PASS.** `scripts/check.sh` green in the new repo — build clean, no
   sorry, all 62 audited declarations depend only on
   `{propext, Classical.choice, Quot.sound}` (the `Verifier` spec on none). Coverage diff:
   only two trivial helpers (`softmax_apply` — a `rfl`, `softmax_denom_pos`) are outside
   the audit list; every substantive theorem is in it.
4. **The Loewner forms (G8) are correct and honestly scoped:** `softmaxJac_posSemidef` and
   `two_smul_softmaxJac_le_one` go straight through `posSemidef_iff_dotProduct_mulVec` to
   the existing variance lemmas, and the file records — *verified in Lean, not assumed* —
   that the C\*-order→norm shortcut is unavailable over `ℝ` (`Matrix n n ℝ` is not a
   `CStarAlgebra` in Mathlib), so the Rayleigh proof rightly remains the norm engine.
5. **The AUDIT2 G-list is closed:** stale headers rewritten (G3), `netTrace_mem_netBoxes`
   docstring fixed (G4), `pooling_leading_coeff` re-tiered to `spec-rewrite` and demoted
   to "supporting identity" (G5), `softmaxJac`/`sjJ` deduplicated with the Jacobian public
   in one place (G6), `netMap` fold orientation documented (G7), stable-neuron encoding
   footnote added to `Network.lean` (G9). Prose and the `edges:` block now carry the
   resolved finding (`kind: code-vs-paper-bug`, `status: CONFIRMED`).

**One new fact this audit adds — the exposure is concrete, not hypothetical (H1):** the
finding doc's §4 says an instance is exposed iff `margin_slack < 2`. I checked the shipped
configs: **every fixed-pattern instance in `mini_sweep.yaml` and `mini_sweep_tiny.yaml`
uses `margin_slack: 1.05`** (and the CLI default is `1.0001`). Under the paper-correct
`n/2` constant, `1.05·L_code < L_paper` whenever the `n`-terms contribute more than ~5% of
`L_attn` — which they dominate at the shipped parameters (e.g. `fp_01`: `n=16, α=5, d=4`
gives first-term ≈ `80·V0_inf` vs value-term `2σ`). So **all shipped fixed-pattern
instances fail the paper's own certificate condition**: their UNSAT ground-truth labels
are *unproven by the construction's theorem* (not necessarily false — the bound is
sufficient, not necessary — but the benchmark's "provably robust by construction" claim
does not hold for them as shipped). This sharpens the UCLA question and belongs in
`FINDING-attn-Lattn-n4.md` §4 (step H1 below).

**Remaining items are packaging, not mathematics** (§3): the unpushed commit, the stale
divergent copy still sitting in `aiq-eval-runner/formalizations/veristressgt`, the absent
`Challenge/` comparator layer, and four cosmetic nits.

## 2. What was verified this pass (detail)

| Item | Method | Result |
|---|---|---|
| Paper eq. 51/52/54/55, Prop. 6/7 | extracted from `papers/2605.17153…pdf` pp. 18–19 (pypdf) | match the finding doc verbatim; `n/2` confirmed; ½ is the **spectral** norm |
| `compute_L_attn` uses `n/4.0` | re-read `fixed_pattern.py:56-71` | confirmed (two terms) |
| Kim et al. claim ("no n/4, no halving") | consistent with their `O(√N log N)`/Lambert-W bounds; not exhaustively re-derived | plausible, unchallenged |
| `Z_deviation` proof | re-derived by hand: two-term product-rule split, `‖·‖₁`-weighted mixing, `l1_le_sqrt_mul_dist` (Cauchy–Schwarz), `attn_l1` (prob. vector) | correct; equals paper eq. 53 row bound |
| `Z_deviation_n2`, `pooling` coefficient | `√n·(½·√n·B_S·ε) = (n/2)B_S·ε` rewrite | correct |
| `attn_dist_le`, `attn_l1`, `zflat_deviation`, `margin_deviation`, `fixedPattern_robust_derived` | line-by-line | correct; mirrors the proven linear-dominance pattern and Prop. 7 |
| `softmaxJac_posSemidef`, `two_smul_softmaxJac_le_one` | line-by-line (incl. the `star_trivial`/`Matrix.le_iff` plumbing) | correct |
| Full pipeline | `bash scripts/check.sh` | PASS (62 audited, axioms clean) |
| Audit coverage | name-diff of `#print axioms` list vs all source `theorem`s | complete except 2 trivial helpers |
| Shipped `margin_slack` | grep sweep configs + CLI default | `1.05` / `1.0001` — inside the exposure band (H1) |
| Git | `git log`, remote, status | repo + GitHub remote exist; tree clean; **1 commit unpushed** |

## 3. Findings (all packaging/hygiene; none mathematical)

- **H1 · MEDIUM-HIGH (strengthens the finding — add before sending to UCLA):** the
  shipped sweeps sit at `margin_slack = 1.05 < 2`, so per the finding's own criterion the
  shipped fixed-pattern instances' ground-truth labels are unproven under the corrected
  constant (see §1). Add this concrete config evidence to `FINDING-attn-Lattn-n4.md` §4
  and to the edge's `informal:` note; it converts "may be exposed if…" into "the shipped
  sweeps are in the exposed regime." Optionally sanity-check one instance empirically
  (PGD attack or a long-budget complete verifier run) to learn whether any label is
  actually *false*, not merely unproven — either outcome is useful to report.
- **H2 · MEDIUM (two sources of truth):** `aiq-eval-runner/formalizations/veristressgt`
  still exists, untracked, and now **diverges** from this repo (missing the `60c1029`
  changes — it still tells the pre-resolution story with the old `n/4` framing). Anyone
  reading the parent tree gets stale conclusions. Delete it and leave a pointer (or wire
  this repo in as a submodule, matching the `aiq-dkps-formalization` sibling pattern);
  update the parent docs that reference `formalizations/veristressgt` paths.
- **H3 · MEDIUM (provenance):** the resolution commit `60c1029` is **ahead of origin by
  1** — the published GitHub state does not yet contain the finding, the assembled
  certificate, or the Loewner forms. Push before any UCLA communication that cites them.
- **H4 · LOW (API):** `fpK` is a `private def` appearing in the **statements** of the
  public `margin_deviation` / `fixedPattern_robust_derived` — downstream files cannot
  spell the bound they'd need to instantiate. Make it public (it is the Lean form of the
  paper's `L_attn·ε` budget) or inline it.
- **H5 · LOW (duplication regression):** `abs_apply_le_norm` is now `private` in *two*
  files (`LinearDominanceBlock`, `FixedPatternBlock`). Hoist one copy (ForMathlib is the
  natural home; Loogle-check first per survey §7.3).
- **H6 · LOW (cosmetics):** `Z_deviation_n2` docstring parenthetical says
  "(`√n·½·√n = n`)" — should be `n/2`; README/AGENTS say "61 public theorems" while
  `AxiomAudit.lean` prints 62 — pick one canonical count (suggest "62 audited
  declarations") and state it once.
- **H7 · LOW (last DKPS-parity gap):** the `Challenge/` comparator layer (AUDIT2 step 5)
  remains absent. The upstream candidate is now even better shaped (Loewner pair +
  `softmax` + `hasFDerivAt_softmax` + `lipschitzWith_softmax`); package it as one
  conformance/leaderboard/comparator-config unit when the Mathlib push starts.
- **H8 · LOW (optional tightening):** the derived certificates' seams are the row-level
  `hρ` (score-row deviation) and `hδV` — honest and exactly the paper's eq. 51/`∆V`
  quantities, but two ~10-line glue lemmas (`‖Xᵢ−X₀ᵢ‖₂ ≤ √d·ε` from the L∞ box;
  per-entry → row-ℓ² `≤ √n·max`) would connect `score_deviation_unit` all the way to
  `fixedPattern_robust_derived`, leaving the *weights themselves* as the only seam. Not
  required for the UCLA conversation; nice for the "self-contained" story.

## 4. Discrete steps to fully self-contained (short list)

1. **H3** — `git push` (now).
2. **H1** — add the `margin_slack: 1.05` config evidence to the finding + edge; then send
   the UCLA question (it is already correctly phrased and minimal in the finding §5).
3. **H2** — remove/replace the stale parent-tree copy; fix parent doc paths.
4. **H4–H6** — one small cleanup commit (public `fpK`, hoist `abs_apply_le_norm`, two
   docstring/count fixes).
5. **H7** — Challenge/comparator packaging when the Mathlib PR effort begins; **H8** — at
   leisure.

## 5. Standing of the overall product

With this pass, every certificate family is either **derived end-to-end from
construction-level quantities** (CNN via `netLipschitz`; both attention constructions via
the deviation chains; MILP via `BigMReach` + IBP; polynomial via the metric core) or
carries its gap as a **named, typed hypothesis** (power-iteration upper bound, OPTIMAL,
Rmax, NBC lower bound, verifier soundness). The repo has produced two externally
valuable artifacts: a **Mathlib-shaped softmax package** (definition, Fréchet derivative,
tight ½-Lipschitz, Loewner-order Jacobian bounds — none previously in any Lean source)
and a **confirmed, machine-check-backed code-vs-paper soundness finding** against the
benchmark it formalizes, with the shipped configs demonstrably in the exposed regime.
That is exactly the "separate evidential product of correctness" the effort set out to
build. Pending: UCLA's response, and the packaging steps above.
