# Second outside audit — VeriStressGT Lean formalization at convergence

**Date:** 2026-07-09 · **Auditor:** independent review pass (Claude, at Kitware's request).
**Prior art:** [`AUDIT.md`](AUDIT.md) (2026-07-07, findings F1–F11),
[`GUIDANCE-F2-F4b.md`](GUIDANCE-F2-F4b.md) (2026-07-08). This pass re-read **every** Lean
file line-by-line (nothing carried over on trust from the first audit), re-ran the
mechanical verification independently, analyzed each proof for vacuity/hypothesis-strength/
faithfulness, reviewed [`EXTERNAL-LEAN-SURVEY.md`](EXTERNAL-LEAN-SURVEY.md) (and appended
§7–§8 to it), and held the repo to the publishable bar set by `aiq-dkps-formalization`.

---

## 1. Verdict

**The mathematics is real, correct, and mechanically verified.** I re-ran
`scripts/check.sh` end-to-end: `lake build` green, no `sorry`/`admit`, and all **52 public
theorems** report axioms exactly `{propext, Classical.choice, Quot.sound}` (one, the
`Verifier` spec, axiom-free). I re-derived every proof by hand while reading — including
the softmax Fréchet derivative, the C\*-grade Jacobian bound, the whole-network big-M
induction, and the derived linear-dominance chain — and found **no incorrect statement and
no vacuous proof masquerading as content**. Since the last audit, four genuinely
substantive additions landed and are verified: `hasFDerivAt_softmax` +
`lipschitzWith_softmax` (F2-B, unconditional), `netLipschitz` (T1′, F1),
`linearDominance_robust_derived` (F2 linear case), and the `BigMReach`
soundness/completeness pair with `bigM_feasible_iff_netEval` (F4b/Theorem A).

**One mathematical gap and one integrity risk keep this short of "self-contained and
meaningful":**

1. **The fixed-pattern (softmax) certificate is still unassembled** (Finding G1). All the
   ingredients are proved — score deviation, `LipschitzWith ½ softmax`, the pooling
   identity — but no theorem connects them into a derived bound on the attention output,
   and `fixedPattern_robust` still takes its Lipschitz constant on assumption.
2. **The repo's headline claim about the `n/4` finding currently outruns its Lean
   evidence** (Finding G2). `pooling_leading_coeff` is the arithmetic identity
   `√n·½·√n = n/2` — it does *not* prove the assembled bound has coefficient `n/2`. Until
   G1 lands, the `attn-Lattn-n4-pooling` edge (a potential *soundness bug report against
   UCLA's code*) rests on prose, and raising it externally in that state would be exactly
   the kind of under-evidenced claim this program exists to eliminate.

Everything else found is documentation-consistency debt (G3–G5) and small hygiene items
(G6–G9). Section 5 gives the discrete steps; G1 is the only one requiring real proof work.

---

## 2. Mechanical verification (independently re-run, 2026-07-09)

| Check | Method | Result |
|---|---|---|
| Full pipeline | `bash scripts/check.sh` (the repo's own F11 artifact) | **PASS** — build clean, no sorry/admit, axioms clean |
| Axiom sweep | 52 `#print axioms` in `AxiomAudit.lean` | all `{propext, Classical.choice, Quot.sound}`; `sound_unsat_robust` axiom-free |
| Coverage of the sweep | cross-checked `AxiomAudit.lean` against every `theorem` in the sources | complete — every public theorem is audited (the "(6)" comment on the Network section miscounts its 8 entries; cosmetic) |
| Library roots | all four new files imported from their roots; `lakefile` targets unchanged and sufficient | ✓ |

The F11 artifact works as designed: this audit's step 1 was literally running it.

## 3. Proof-by-proof analysis (the ruthless pass)

Read order: every file, oldest first, proofs re-derived by hand. Per-file verdicts:

**`ForMathlib/Analysis/SoftmaxJacobianBound.lean`** — unchanged since first audit;
re-verified. Rayleigh route sound; variance identities and Popoviciu bound correct; the
`L2Operator` scope is opened so `‖·‖` is genuinely spectral. Tightness claim checks
(`a=(½,½)` gives eigenvalues `0, ½`). *Note:* the survey's new §7.1 records a shorter
Mathlib-idiomatic route (Loewner order + `Matrix.instCStarRing` +
`CStarAlgebra.nnnorm_le_iff_of_nonneg`) that reuses the two variance lemmas verbatim and
deletes the `toEuclideanCLM`/`IsSymmetric`/`rayleighQuotient` plumbing — relevant to the
Mathlib PR shape (G8).

**`ForMathlib/Analysis/SoftmaxLipschitz.lean`** — the new F2-B closure. Verified:
`softmax_apply`/`_denom_pos`/`_nonneg`/`_sum_one` are correct and discharge R1's
probability-vector hypotheses; `hasFDerivAt_softmax` builds the derivative coordinatewise
(projection∘exp, sum, `hasDerivAt_inv`, product rule) and the `hDeq` `ext`-computation
matching the Mathlib-produced covector to the Jacobian row
`∂ⱼ softmaxᵢ = aᵢ(δᵢⱼ − aⱼ)` is algebraically right (I re-did it:
`exp(sᵢ)·(−Z⁻²)·Σⱼexp(sⱼ)vⱼ + Z⁻¹exp(sᵢ)vᵢ = aᵢvᵢ − aᵢΣⱼaⱼvⱼ`). `lipschitzWith_softmax`
correctly chains the mean-value inequality with the spectral bound. **This is the
strongest single artifact in the repo** — softmax + its derivative + the tight ½ constant,
none of which exists in any Lean source (survey §0/§4). Two defects, neither mathematical:
the **file header still describes the pre-closure state** ("proves … modulo one explicit
hypothesis — that derivative fact is the one remaining piece") — directly contradicting
the theorems below it (G3); and `softmaxJac`/`softmaxJac_mulVec` **verbatim-duplicate** the
`private` `sjJ`/`sjJ_mulVec` (G6).

**`ForMathlib/Analysis/OperatorNormLipschitz.lean`** — `lipschitzWith_listComp` is
correct, minimal, and genuinely reusable; the first audit's F1-comment defect is fixed.
`ForMathlib/Analysis/IntervalArithmeticSound.lean` — unchanged, re-verified sound.

**`LipschitzMargin/Basic.lean`** — `robust_of_deviation_lt_margin` added (the F3 fix);
correct. **`LipschitzMargin/DeepContractiveCNN.lean`** — the T1′ section is right:
`AffLayer.map_lipschitz` (1-Lipschitz activation preserves `‖W‖₊`), `netLipschitz` by
`Forall₂` induction, `netProd_eq`, and the two derived certificates that finally attach
the `dccnn-L-power-iter` edge to the genuine product `∏‖Wᵢ‖₊`. **One modeling nit
(G7):** `netMap` is `foldr (· ∘ ·) id`, so the **head of the list is the outermost map —
applied last** — while `netProd_eq`'s docstring reads the norm list `[σ_proj, λ, …, w_out]`
architecture-order (proj applied first). The product commutes, so every theorem is true
and the certificate is unaffected; but a faithfulness reviewer will trip over the
orientation. One docstring sentence ("the list is outermost-first; the DCCNN list is
`[w_out, λ…, σ_proj]`") or a switch to `foldl` fixes it.

**`SelfAttention/LinearDominance.lean`** — the F3 restatement is faithful:
total-deviation form, no ε double-count, cert condition matches
`linear_dominance.py:206`. **`SelfAttention/LinearDominanceBlock.lean`** — the F2 linear
closure; verified end-to-end: `token_deviation` finally consumes
`linearDominance_token_bound`; `zflat_deviation`'s `√n` pooling is a correct ℓ²
aggregation (and needs its explicit `0 ≤ Bmax`, which is there); `margin_deviation`'s
bias-cancellation and `2‖W_head‖` coordinate extraction are right;
`linearDominance_robust_derived`'s only seams are `hw`/`hV`/`hB` — exactly the code's
`dw`/`dV`/`B_max`, as the audit design demanded. The `private abs_apply_le_norm` should
be Loogle-checked for a Mathlib duplicate before any upstreaming (survey §7.3).

**`SelfAttention/FixedPattern.lean`** — `gap_iff_stability_margin` upgraded to the full
`↔` (F10 fixed); `fixedPattern_robust` is still the assumed-Lipschitz wrapper — expected,
since the derived version is the open G1. Its docstring is honest.
**`SelfAttention/FixedPatternBlock.lean`** — `inner_deviation_bound` and
`score_deviation_unit` are correct and faithful to `compute_L_attn`'s `B_S` (including
the deviation-not-Lipschitz typing). `pooling_leading_coeff` is **only** the identity
`√n·(1/2)·√n = n/2` — see G2. **The file header contradicts the repo** (G3): it says the
softmax-Lipschitz consumer "is the one remaining derivation … not yet closed," while
`SoftmaxLipschitz.lean` closes it.

**`IntervalBounds/Basic.lean`** — `netTrace_mem_netBoxes` added; the `Forall₂` induction
is correct. Its docstring says it is "Consumed by `ExactMILP.Network.bigMReach_complete`"
— **it is not**: `bigMReach_complete` threads `Layer.sound` directly and never mentions
`netTrace_mem_netBoxes`, which currently has **no consumer** (G4). It remains a legitimate
standalone strengthening (and the docstring's `getLast` relationships to
`netEval`/`netProp` are asserted but not stated as lemmas — optional tidy-up).

**`ExactMILP/Basic.lean`** — `label_sound_of_optimal` now concludes ball-disjointness
(F4 fixed) — but its trailing NOTE still says the `advSet`↔`netEval` connection "is
future modelling work" while `Network.lean` *is* that work (G3).
**`ExactMILP/Network.lean`** — the F4b closure; verified in full. `advSet` is faithful
(ties count as adversarial, matching the MILP's `logit_k ≥ logit_y`); the Pi-metric = L∞
observation is correct and load-bearing; `robust_of_lt_infDist_advSet` and the Rmax lemma
(`le_antisymm` squeeze through Mathlib's fixed-radius version) are sound;
`robust_of_no_adv_in_ball` handles the F9 artifact; `BigMReach`'s recursion mirrors
`netProp`; `bigMReach_sound` is bounds-free per-neuron faithfulness (I checked the goal
plumbing through `netEval (relu::rest)`); `bigMReach_complete`'s ReLU witness
(`z = max 0 x`, `a = if x ≤ 0 then 0 else 1`) satisfies all four constraints in both
branches (checked case-by-case); the capstone `iff` and `bigM_adversary_iff` complete
prose Theorem A minus Gurobi. **The display asymmetry — soundness needs no bounds,
completeness is where IBP earns its keep — is correctly realized in the proofs, not just
claimed.** One faithfulness footnote worth one sentence in the file (G9): the code
short-circuits *stable* neurons (`u ≤ 0` ⟹ `z = 0`, `l ≥ 0` ⟹ `z = s`) and spends
binaries only on unstable ones; the formalization spends a binary at every ReLU neuron.
The feasible sets coincide (the constraints force the same `z`), so nothing is unsound —
but the encodings differ and the equivalence is unstated.

**`AlgebraicBoundary/Basic.lean`, `Verifier/Spec.lean`** — unchanged; re-verified. The
empty-boundary note (F9) is present on the AlgebraicBoundary side.

**Vacuity scan (all 52):** the only theorem whose Lean content is materially weaker than
its surrounding narrative is `pooling_leading_coeff` (G2). `netProd_eq`,
`label_sound_net_of_optimal`, and the Tier-3 spec rewrites are thin but correctly
labeled — with one exception: **`formalization.yaml` tags `pooling_leading_coeff` as
`tier: substantive`, which by the yaml's own tier scheme (AUDIT.md §3) it is not** (G5).

## 4. Findings (this pass)

### G1 · HIGH (the one remaining Lean gap) — the fixed-pattern chain is proved in pieces but never assembled

What exists: `score_deviation_unit` (per-entry score deviation), `lipschitzWith_softmax`
(the row contraction tool), `pooling_leading_coeff` (numerology). What does not exist:
any theorem about the fixed-pattern block's **output** — no `‖ΔZᵢ‖` bound, no derived
margin deviation, no `fixedPattern_robust_derived`. Consequently the softmax construction
still certifies only *modulo an assumed Lipschitz constant*, i.e. the exact state the
first audit criticized for the linear construction. The linear case shows the target
shape; the missing sub-lemmas are enumerated in §5 step 1. Note the honest-scope
docstrings *say* this correctly at theorem level — the problem is only that headline
docs claim more (G3) and the edge claim depends on it (G2).

### G2 · HIGH (evidence integrity for an outward-facing claim) — the `n/4` edge is not yet Lean-evidenced

`attn-Lattn-n4-pooling` accuses `compute_L_attn` of a possible 2× unsafe under-estimate.
The recorded Lean anchor is `√n·½·√n = n/2` — an identity about three real numbers, not
about attention. The `n/2` *derivation* lives in prose (GUIDANCE §F2-C.3, docstrings).
Before this edge is raised with UCLA — and it should be, it is potentially the most
valuable single output of the whole exercise — the assembled bound of G1 must exist so the
claim reads: "the formally verified bound has leading coefficient n/2; exhibit the
halving argument or the shipped constant is unsound." Raising it earlier invites the
rebuttal "your n/2 is also just a sketch." (If UCLA produces a valid halving argument,
formalize it and the edge closes as tightness, not soundness — either outcome is a win,
but only with the Lean artifact in hand.)

### G3 · MEDIUM — status statements disagree across four surfaces

Three different answers to "is the softmax thread closed?" coexist:
- `SoftmaxLipschitz.lean` header: *conditional, one hypothesis deliberately left open* —
  *stale, contradicts its own theorems.*
- `FixedPatternBlock.lean` header: *softmax-Lipschitz consumer still open* — *stale.*
- `README.md` headline: "Both audit gaps (F2, F4b) are now **fully closed**" —
  *overclaims G1* (the bullets under it are accurate; the headline is not).
- `formalization.yaml` `review:` — the accurate one ("F2 CLOSED: linear construction
  DERIVED …, softmax score/pooling formalized").
Plus three residual stale spots: `formalization.yaml:status.repository_build.note`
(still the 2026-07-07 text: "ALL 16 target lemmas", "modelling gap remains open"),
`status.scope` ("states its … theorem(s) with `sorry`"), `ExactMILP/Basic.lean`'s
`label_sound_of_optimal` NOTE ("future modelling work"), and cosmetics (README line 3
"Lean 4 scaffold", yaml `authors: AIQ Kitware (scaffold)`). The first audit's F6 lesson
(single-fact-single-place) has not fully taken: status is asserted in ≥6 places again.

### G4 · LOW-MEDIUM — `netTrace_mem_netBoxes` docstring claims a consumer it doesn't have

`bigMReach_complete` uses `Layer.sound` directly. Either reword the docstring ("the
standalone every-stage record; `bigMReach_complete` re-runs the same induction inline"),
or actually refactor the completeness induction to consume it. The theorem itself is fine.

### G5 · LOW-MEDIUM — `pooling_leading_coeff` mislabeled `tier: substantive` in the yaml

By the repo's own tier scheme it is a spec-level identity (Tier 3). The mislabel matters
because the tier column is the repo's defense against the first audit's "counting
overstates coverage" criticism — it must be beyond reproach.

### G6 · LOW — internal duplication: `softmaxJac`/`softmaxJac_mulVec` ≡ `sjJ`/`sjJ_mulVec`

Verbatim re-proof because the originals are `private`. Make one public, delete the other
(survey §7.4). Also Loogle-check `abs_apply_le_norm` before upstream packaging (§7.3).

### G7 · LOW — `netMap` fold orientation vs docstring layer order

`foldr` makes the list head the *last-applied* map; `netProd_eq`'s docstring reads the
list architecture-first. Math unaffected (product commutes); fix the docstring or use
`foldl`. Detail in §3.

### G8 · LOW (upstream-shape) — the Mathlib candidate should be restated in Loewner form

Survey §7.1: the pinned Mathlib's scoped `Matrix.instCStarRing` + Loewner order +
`CStarAlgebra.nnnorm_le_iff_of_nonneg` give a shorter standard route, and — more
important for the PR — maintainers will want the primary statement as
`0 ≤ J ∧ 2•J ≤ 1` (the norm bound as a generic corollary). Verify the instance chain
elaborates over `ℝ`; if it does not, keep the Rayleigh engine but still add the Loewner
corollary as the PR-facing statement.

### G9 · LOW — one-sentence faithfulness footnote for the big-M encoding

The formalized encoding spends a binary at every ReLU neuron; the code eliminates stable
neurons first. Same feasible set; say so in `Network.lean` so a reviewer diffing against
`exact_radius.py:264-287` doesn't flag it.

## 5. Discrete steps to a self-contained, publishable result

Ordered. Step 1 is the only proof work; 2–4 are hours; 5–7 are packaging/process.

1. **Assemble the fixed-pattern derivation (closes G1, evidences G2).** New
   `FixedPatternBlock` content, mirroring `LinearDominanceBlock`:
   a. Glue lemma `‖x − x₀‖₂ ≤ √d · max` (L∞ box → per-token ℓ²; also completes the
      optional step-6 derivation of `hV` in the linear file). ~10 lines.
   b. Row bound: for score rows `S i` with per-entry deviation `≤ B_S·ε`
      (`score_deviation_unit`), `‖ΔS i‖₂ ≤ √n·B_S·ε`; then
      `‖softmax(S i) − softmax(S₀ i)‖ ≤ ½·√n·B_S·ε` by `lipschitzWith_softmax`. ~15 lines.
   c. Convex-combination lemma `‖∑ⱼ cⱼ • vⱼ‖ ≤ ‖c‖₁ · maxⱼ‖vⱼ‖` and the ℓ¹→ℓ² step via
      Mathlib's `sq_sum_le_card_mul_sum_sq` (survey §7.2 — do not hand-roll). ~20 lines.
   d. Product-rule assembly: `‖ΔZᵢ‖ ≤ (n/2)·B_S·ε·V0max + √d·σ_V·ε + (n/2)·B_S·ε·√d·σ_V·ε`
      — the theorem whose leading coefficient **is** the `n/2`, replacing
      `pooling_leading_coeff` as the edge anchor. Note the middle term's coefficient-free
      `√d·σ_V` comes from `‖softmax row‖₁ = 1` (`softmax_sum_one` + `softmax_nonneg`) — a
      nice checkable sub-claim. ~40 lines.
   e. Aggregate + head (reuse the `zflat`/`margin_deviation` pattern verbatim) →
      `fixedPattern_robust_derived`, with the code-vs-derived gap carried as an explicit
      hypothesis `hcode : Lattn_code ≥ derivedBound` if stated against the code's constant.
   f. Then: retire or annotate the assumed-Lipschitz `fixedPattern_robust`; update the
      `attn-Lattn-n4-pooling` edge's `lean:` anchor to the step-d theorem; add the new
      declarations to `AxiomAudit.lean` and re-run `scripts/check.sh`.
   Estimated effort: 1–2 days, no new mathematical risk (all hard tools exist).

2. **Truth-reconciliation sweep (closes G3–G5).** Fix the two stale file headers
   (`SoftmaxLipschitz`, `FixedPatternBlock`), the README headline ("fully closed" →
   "closed for linear; softmax assembled through step-1d" once true, or scoped honestly
   until then), `formalization.yaml` `repository_build.note`/`scope`, the ExactMILP NOTE,
   the `netTrace_mem_netBoxes` docstring, the `pooling_leading_coeff` tier, the
   `AxiomAudit` "(6)" count, and the two "scaffold" cosmetics. Then enforce the rule:
   **status lives only in `formalization.yaml`; every other surface links to it.**

3. **Hygiene (closes G6, G7, G9).** De-duplicate `softmaxJac`/`sjJ`; fold-orientation
   docstring; stable-neuron encoding footnote; Loogle-check `abs_apply_le_norm`.

4. **Loewner restatement of the flagship (G8, survey §7.1).** Add
   `softmaxJac_posSemidef` and `two_smul_softmaxJac_le_one` (Loewner) as the PR-facing
   statements — the variance lemmas already prove them via
   `posSemidef_iff_dotProduct_mulVec` — and try the C\*-route norm corollary over ℝ.
   Half a day; independent of step 1.

5. **Challenge/comparator packaging (DKPS parity — the last missing structural piece).**
   The repo now matches DKPS on per-declaration yaml records, verification artifact, and
   review section; it lacks the `Challenge/` layer. Package **one** candidate the DKPS
   way (Conformance + Leaderboard + comparator config): the softmax pair
   (`softmax_jacobian_opNorm_le_half` in Loewner form + `lipschitzWith_softmax` +
   `hasFDerivAt_softmax`) as the single opening PR — it is self-contained, absent from
   Mathlib (survey-verified), and tight. `lipschitzWith_listComp` is a plausible second,
   pending a Mathlib dup-check. Half a day after step 4.

6. **Version control (deferred F5 — cannot stay deferred for "publishable").** Everything
   above is still untracked on disk. `git init` + submodule wiring per `AGENTS.md` §8 is a
   prerequisite for external review, the UCLA conversation, and any Mathlib PR (which
   needs public provenance). Recommend doing it *before* step 1 so the assembly lands as
   reviewable commits.

7. **The two non-Lean closures.** (a) Take the step-1d theorem to UCLA for the `n/4`
   adjudication (with the Appendix-A power-iteration item); record the outcome on the
   edge. (b) External statement-faithfulness review against the PDFs (AUDIT.md §5 step 7
   checklist still applies) — after step 2, so reviewers read one consistent story.

## 6. Publishable-standard scorecard (vs `aiq-dkps-formalization`)

| DKPS bar | Status here |
|---|---|
| Green build, zero sorry, axiom-clean leaves | ✓ (re-verified this pass) |
| Reproducible verification artifact | ✓ `scripts/check.sh` + `AxiomAudit.lean` |
| Per-declaration yaml records (axioms, sorry_count) | ✓ (fix one `tier` label — G5) |
| `review:`/fidelity metadata with honest open-gaps | ✓ (best status surface in the repo) |
| Single consistent status story | ✗ G3 — four surfaces disagree |
| Challenge/comparator layer for upstream candidates | ✗ step 5 |
| Git provenance | ✗ deferred F5 — blocking for publishable |
| Statements faithful to sources, externally reviewed | ⧗ step 7b; one modeling nit (G7), one encoding footnote (G9) |
| No claim ahead of its formal evidence | ✗ G1/G2 — the `n/4` headline needs step 1 |

**Summary:** after step 1 (the assembly), step 2 (one truthful story), and step 6 (git),
this is a publishable, self-contained evidential product: every certificate family
derived from construction-level quantities or carrying its gap as a named hypothesis, a
tight new softmax result packaged for Mathlib, and one externally actionable soundness
finding backed by a machine-checked bound.
