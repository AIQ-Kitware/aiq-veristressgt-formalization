# AGENTS.md — orientation for anyone (esp. AI agents) picking up this repo

Read this first. It captures *why* this repo exists, *what* has been established, and
the *traps* — the context that is expensive to re-derive and easy to lose. Companion
docs: [`README.md`](README.md) (build + library map), [`theorem-map.md`](theorem-map.md)
(the published-theorem chain), [`ucla-formalization-edges.md`](ucla-formalization-edges.md)
(assumption→relaxation edges + the power-iteration analysis), [`prose/`](prose/)
(faithful transcriptions of every source), [`formalization.yaml`](formalization.yaml)
(per-declaration source map).

---

## 1. What this repo is for (the one-paragraph version)

This is a **Lean 4 formalization of the theorems behind the UCLA "VeriStressGT" MAGNET
evaluation card.** It is one node in a broader AIQ TA1 effort: for each team's
evaluation card, state the *idealized theorem* the card's claim rests on, then draw an
explicit **"assumption → relaxation" edge** from each Lean hypothesis to the empirical
card code that relaxes/approximates it. The point is to make precise **what the proof
actually guarantees vs. what the card measures.** VeriStressGT was chosen as an early
target because its instances are *provably robust by construction* — each construction
instantiates a **published robustness-verification theorem**, so it is genuinely
formalizable (graded **High**).

The precedent and template is the sibling repo
[`../aiq-dkps-formalization`](../aiq-dkps-formalization) (JHU DKPS), which fully
formalizes four papers behind the JHU cards. **We are mirroring its structure.**

### The broader effort (context you will not find in this submodule)

These live in the **parent repo** (`aiq-eval-runner`, two levels up from this repo):

- **`../../docs/planning/ta1-formalization-edges.md`** — the master write-up of the
  "formalization edge" idea, a proof-of-concept on JHU DKPS, and a formalizability
  grading of every TA1 team. VeriStressGT is graded **High**. *Read this to understand
  the mission.*
- **`../../docs/ta1/ucla_veristressgt.md`** — the UCLA/VeriStressGT team doc (contact,
  cards, assets).
- **`../../ta1/VeriStressGT/`** — the actual UCLA code + the evaluation card this repo
  targets (see §3). Constructions under `src/VeriStressGT/robust_constructions/`;
  Difficulty Profile under `src/VeriStressGT/difficulty_profile/`.
- **`../../docs/ta1_evaluation_guide.md`** — how MAGNET cards / evaluations work.

MAGNET is the AIQ evaluation framework: each TA1 team ships **cards** (YAML encoding a
scientific claim + a measurement pipeline); `python -m magnet.evaluation <card>` returns
VERIFIED / FALSIFIED / INCONCLUSIVE.

---

## 2. Provenance & the single most important structural fact

> ✅ **Everything here is published.** Unlike some TA1 threads, both UCLA papers are on
> arXiv — the VeriStressGT paper (**arXiv:2605.17153**) and the polynomial-network
> verification paper (**arXiv:2602.06105**) — and *every certificate theorem the
> constructions instantiate is a well-established published result* (T1–T6, §4). PDFs
> are downloaded (git-ignored) under [`papers/`](papers/); re-fetch with
> `bash papers/fetch_papers.sh`. So there is no unpublished-manuscript caveat here;
> cite the arXiv ids freely.

> ⚠️ **The key structural fact instead:** VeriStressGT is **not one theorem with a
> finite-sample shadow** (that is JHU/DKPS). It is a **certificate factory** — *many
> small, independent certificate theorems*, one per construction, each of the form
>
> > `margin(x₀) > (a Lipschitz/sensitivity constant) · (perturbation ε) ⟹ no adversarial
> > example in the L∞ ε-box ⟹ the VNN-LIB query is UNSAT.`
>
> The construction chooses the network weights so the inequality holds *by construction*,
> then asks a third-party verifier (α-β-CROWN) to **re-derive** the UNSAT verdict under a
> resource budget. So there is **no single capstone** the way DRSB or DKPS have one; the
> "capstone" is the set of per-construction robustness lemmas in each library. See
> [`prose/00-overview-and-provenance.md`](prose/00-overview-and-provenance.md).

---

## 3. What VeriStressGT actually does (so the theorems make sense)

Each generated instance factorises into two logically separate objects:

- **The ground-truth certificate** — a *published theorem* instantiated on the
  constructed weights (a Lipschitz-margin inequality, a softmax-attention sensitivity
  bound, an exact-MILP radius, or a distance-to-the-algebraic-boundary certificate).
  This is what is **formalizable**; its hypotheses are exactly the edges.
- **The card claim** — the **verifier stress test**: α-β-CROWN must return the correct
  UNSAT verdict on **≥ 60%** of the provably-UNSAT instances within a **60 s** timeout
  (`../../ta1/VeriStressGT/cards/evaluation.yaml`, `threshold = 0.6`). This is an
  *empirical, resource-bounded* measurement; **no theorem entails 60%.**

The formalization edge is therefore *not* "theorem vs. its finite-sample shadow"; it is
**(a ground-truth certificate hypothesis) → (the numerical/relaxation/timeout gap by
which a real verifier, or the construction's own numerical checks, could disagree)**.
The edges split into two families (full tables in `ucla-formalization-edges.md`):

- **Family A — construction edges** that could make a shipped instance *mislabeled*
  (false-UNSAT): e.g. `dccnn-L-power-iter` (power-iteration Lipschitz estimate is a
  *lower* bound → certified `L` under-estimates the true `L`; see the edges **Appendix A**
  for the firm, quantified analysis), `poly-nbc-surrogate` (50-restart local search
  instead of the exact ED-degree distance), `milp-incomplete-label` (self-declared in the
  code).
- **Family B — card edges** that bound what "≥ 60%" can mean: verifier soundness is
  *assumed* (exactly what the paper finds violated by float-tolerance bugs) and
  completeness is time-bounded to 60 s.

The **Difficulty Profile** (`difficulty_profile/components.py`: `margin_sample_min`,
`unstable_frac`, `ibp_relative_gap`, `A_tau_effective_log`, …) is UCLA's own instrument
for measuring where each instance sits on the convex-relaxation barrier — so several
edges land on difficulty-profile components, not just verifier output.

---

## 4. The published-theorem chain (what proves what)

Every link is transcribed in [`prose/`](prose/) (source PDFs in [`papers/`](papers/),
**git-ignored** — re-download with `bash papers/fetch_papers.sh`). One Lean library per
certificate family; full crosswalk in [`theorem-map.md`](theorem-map.md).

| Certificate family | Library | Published anchor | arXiv |
|---|---|---|---|
| **T1** Lipschitz-margin: `margin > √2·L·ε ⟹ robust` (+ T1′ `L = ∏‖Wᵢ‖₂`) | `LipschitzMargin` | Tsuzuku–Sato–Sugiyama, NeurIPS 2018 | 1802.04034 |
| **T2** Lipschitz constant of self-attention (softmax-Jacobian `≤ ½`) | `SelfAttention` | Kim–Papamakarios–Mnih, ICML 2021 | 2006.04710 |
| **T3** Exact `L∞` radius via big-M MILP (+ NP-completeness, Katz *Reluplex*) | `ExactMILP` | Tjeng–Xiao–Tedrake, ICLR 2019 / Katz et al. CAV 2017 | 1711.07356 / 1702.01135 |
| **T4** IBP soundness (+ relaxation barrier, linear-region count) | `IntervalBounds` | Gowal et al. 2018 / Salman 2019 / Montúfar 2014 | 1810.12715 / 1902.08722 / 1402.1869 |
| **T5** CROWN / β-CROWN complete branch-and-bound (the verifier under test) | `Verifier` | Zhang et al. 2018 / Wang et al. 2021 | 1811.00866 / 2103.06624 |
| **T6** Distance-to-the-algebraic-boundary (Euclidean-distance degree) | `AlgebraicBoundary` | Alexandr–Duan–Montúfar / Draisma et al. 2016 | 2602.06105 / 1309.0049 |
| Shared reusable results (operator-norm Lipschitz, softmax-Jacobian bound, IBP steps) | `ForMathlib` | classical / Mathlib candidates | — |

The two UCLA papers themselves — **2605.17153** (VeriStressGT) and **2602.06105**
(polynomial verification) — are the empirical framework being formalized, not additional
theorems to relax; see [`prose/00-overview-and-provenance.md`](prose/00-overview-and-provenance.md).

Each `<Library>/Basic.lean` docstring cites the prose file + printed theorem number every
declaration corresponds to.

---

## 5. Repo conventions & workflow (how to work here without breaking things)

- **First-pass policy: STATEMENTS ONLY.** Every theorem body is `:= by sorry`. We are
  matching statements to the papers *first*; proofs come later. Do not start proofs
  unless explicitly asked.
- **Faithfulness rule:** re-derive every statement from `prose/` (which cites the printed
  theorem/eq numbers) and the source PDFs, **not** from memory. Put a `/-- -/` docstring
  on each theorem citing the prose file + source number; inline-comment each hypothesis.
- **Edges are carried as explicit Lean hypotheses.** Where a construction only
  *numerically approximates* a theorem hypothesis, the corresponding theorem takes that
  hypothesis as an explicit premise the shipped code may not satisfy — e.g.
  `LipschitzMargin.dccnn_robust_of_upper_bound` takes `L ≤ L̂`, the upper-bound premise
  the power-iteration `L̂` provably does *not* satisfy (it is a lower bound). This makes
  each edge visible in a type signature rather than buried in prose.
- **Shared vocabulary lives in `ForMathlib`** (operator-norm Lipschitz, the softmax
  Jacobian bound, the IBP affine/ReLU containment steps). A certificate library imports
  only `Mathlib` + the `ForMathlib` files it needs; keep the libraries independent (there
  is no capstone importing all of them — see §2).
- **Syntax-check a single file with `lake env lean <Lib>/Basic.lean`** (fast once Mathlib
  is built; no build lock). **Do NOT run `lake build` in parallel** with another agent —
  it takes a lock. Success = exit 0 with only `warning: declaration uses 'sorry'`; fix
  every red `error:`.
- **`set_option autoImplicit false`** in every file (also set globally in `lakefile.toml`).

### Adding a new certificate library
1. `NewLib.lean` containing only `import NewLib.Basic` (and any submodules).
2. `NewLib/Basic.lean`: `import Mathlib` (+ the `ForMathlib` files it needs),
   `set_option autoImplicit false`, `namespace VeriStressGT.NewLib`, defs + `sorry`
   theorems, each with a prose-citing docstring.
3. Add `[[lean_lib]] name = "NewLib"` to `lakefile.toml` (and to `defaultTargets`).
4. `lake env lean NewLib/Basic.lean` until clean; then update `formalization.yaml`
   `sources`/`main_targets`, `theorem-map.md`, and this file's §4 table.

---

## 6. Known gotchas discovered this session (do not re-learn the hard way)

- **Matrix norms are non-instances behind scoped namespaces.** The softmax-Jacobian
  bound `‖diag a − a aᵀ‖ ≤ 1/2` is about the **L²-operator (spectral)** norm — you must
  `open scoped Matrix.Norms.L2Operator` for `‖·‖` on `Matrix (Fin n) (Fin n) ℝ` to be
  that norm. With Mathlib's *entrywise* sup-norm the same matrix is only `≤ 1/4`, a
  different and weaker statement — a silent faithfulness bug. (Found by the first
  self-review pass; see `ForMathlib/Analysis/SoftmaxJacobianBound.lean`.)
- **`import Mathlib` pulls the whole library.** Every file does `import Mathlib`, so the
  first build must compile Mathlib's full closure. To avoid re-downloading, this repo's
  `.lake/packages` is a symlink to `../aiq-dkps-formalization/.lake/packages` (same pinned
  Mathlib rev / toolchain). After the one-time closure build, single-file checks are fast.
- **We formalize *specifications*, not verifier internals.** `Verifier/Spec.lean` states
  `Sound`/`CompleteInLimit` as the interface the card stands on — it does **not** attempt
  to prove CROWN/β-CROWN correct (a verifier-correctness project of its own). Likewise
  `ExactMILP` formalizes *encoding faithfulness* (`z = max 0 s` iff the big-M constraints
  hold), not that Gurobi is correct; NP-completeness (Katz) is cited context, not a target.
- **The ED-degree machinery is out of scope.** `AlgebraicBoundary` formalizes only the
  metric core (`dist(x₀,𝒱) > ε ⟹ class constant on the box`); the polar-class / homotopy
  machinery of arXiv:2602.06105 that makes the exact distance *computable* is cited
  context and far outside Mathlib.
- **Don't re-stage what Mathlib already has.** The first review deleted a `ForMathlib`
  file that duplicated `Metric.disjoint_closedBall_of_lt_infDist`. Before staging a
  `ForMathlib` candidate, grep the pinned Mathlib source.
- **Vacuity traps.** A statement can elaborate yet assert nothing (a `True` conclusion, a
  `P → P` tautology, or content hidden inside an equality hypothesis). The first review
  caught three; keep conclusions concrete and geometric (e.g. state IBP soundness over a
  real `Layer` inductive, not an abstract propagator that returns its own premise).

---

## 7. Build / environment

- Toolchain **`leanprover/lean4:v4.31.0-rc2`** (pinned in `lean-toolchain`, same as the
  DKPS repo); Mathlib pinned in `lake-manifest.json`.
- Fresh setup: `bash setup_lean.sh` (elan + the pinned toolchain), then either
  `lake exe cache get` (download prebuilt Mathlib oleans) **or** reuse the sibling repo's
  build via the `.lake/packages` symlink, then `lake build`. Builds green, **zero `sorry`**.
- **Verify** with `bash scripts/check.sh` (build + no-sorry grep + `AxiomAudit.lean`
  `#print axioms` sweep — all 30 public theorems in `{propext, Classical.choice, Quot.sound}`).
- **Never commit** `.lake/` or `papers/*.pdf` — both are git-ignored.

## 8. Git / submodule

- This is intended to be committed as its own **git repo** and wired in as a submodule of
  `aiq-eval-runner` under `formalizations/veristressgt`. Commit here; to share, push this
  repo, then in the parent `git add formalizations/veristressgt` to bump the pointer.
- Commit style: follow the parent project's `Co-Authored-By` trailer convention.

## 9. Current status & next steps

- **Done:** repo scaffolded; `ForMathlib` + 6 certificate libraries `lake build` **green**;
  prose transcriptions + PDFs in place; `formalization.yaml` maps every declaration to its
  source. A self-review pass fixed two elaboration blockers, three vacuous statements, and
  one Mathlib duplicate; the real build then caught a big-operator precedence bug the static
  review missed. **Proof pass complete: all libraries proved** — `LipschitzMargin` (incl. the
  T1′ `netLipschitz` composition, audit F1), `SelfAttention` (margin steps), `IntervalBounds`
  (`ibp_network_sound` by induction over a concrete `Layer` list), `ExactMILP` (soundness **and**
  completeness), `Verifier`, `AlgebraicBoundary` (`robust_of_lt_dist_boundary` by IVT), and
  `ForMathlib` (IBP soundness, affine-Lipschitz, list-composition, softmax-Jacobian).
- **A precision self-audit** (2026-07-06/07) corrected two unfaithful claims: (a)
  `bigM_relu_faithful` proved only soundness under a biconditional docstring → split into
  `bigM_relu_faithful` (soundness) + `bigM_relu_complete` (feasibility, which legitimately
  uses `l ≤ s ≤ u`); (b) `linearDominance_robust` / `fixedPattern_robust` docstrings claimed
  to "compose `token_bound`" but actually **assume** the block `LipschitzWith` constant — now
  documented honestly as the margin step *modulo* the Lipschitz-constant derivation.
- **ZERO `sorry`: all 81 audited declarations proved & axiom-clean,** verified by
  `scripts/check.sh` / `AxiomAudit.lean` (both audit gaps F2 and F4b fully closed for BOTH
  attention constructions, incl. the unconditional softmax `LipschitzWith ½` and the assembled
  fixed-pattern output bound — below). Flagship
  `ForMathlib.softmax_jacobian_opNorm_le_half` (spectral `‖diag a − aaᵀ‖₂ ≤ 1/2`, tight) proved
  by the **self-adjoint operator-norm = sup-Rayleigh** route (this Mathlib lacks
  `l2_opNorm ≤ frobenius`): `‖J‖ = ‖toEuclideanCLM J‖` +
  `ContinuousLinearMap.norm_eq_iSup_rayleighQuotient` (needs `(↑T : _ →ₗ _).IsSymmetric` from
  `isSymmetric_toEuclideanLin_iff.mpr` + `J` Hermitian), `⟪Jx,x⟫ = Var_a(ofLp x)` (through
  `toEuclideanCLM_toLp` + `EuclideanSpace.inner_toLp_toLp`), `0 ≤ Var_a ≤ ½∑vᵢ²` (Popoviciu via
  `Finset.exists_max_image` + midpoint). Genuine Mathlib candidate.
- **OUTSIDE AUDIT RESPONSE (AUDIT.md, 2026-07-07).** An independent review found the proved
  content real but narrower than the status lines. Addressed in this pass: **F1** — T1′ is now
  formalized (`netLipschitz`: network `LipschitzWith (∏ᵢ‖Wᵢ‖₊)` via Mathlib's `LipschitzWith.list_prod`;
  `dccnn_robust_via_net_upper` anchors the `dccnn-L-power-iter` edge to the genuine product, not
  an abstract `L`); **F3** — `linearDominance_robust` restated in total-deviation form (no ε
  double-count) via `robust_of_deviation_lt_margin`; **F4** — `label_sound_of_optimal` now
  concludes ball–`advSet` disjointness; **F9/F10** — empty-boundary note + gap `↔`; **F6/F7** —
  doc drift fixed (READMEs, SCAFFOLD notes removed, edges yaml completed); **F11** — reproducible
  `AxiomAudit.lean` + `scripts/check.sh`. **Deferred by request: F5 (git init/submodule).**
- **SECOND AUDIT PASS (GUIDANCE-F2-F4b.md, 2026-07-08/09).** Closed the two open items:
  - **F4b CLOSED.** `ExactMILP/Network.lean`: `advSet` gives the true adversarial set in the
    `IntervalBounds.netEval` vocabulary (`infDist` = exact L∞ radius `r*`, since the default `Pi`
    metric on `Fin n → ℝ` *is* the sup metric); `robust_of_lt_infDist_advSet` /
    `label_sound_net_of_optimal` are the geometric label-soundness endpoint (F4);
    `infDist_inter_closedBall_of_exists_mem_ball` anchors edge `milp-rmax-clamp`; and the
    whole-network big-M relation `BigMReach` has `bigMReach_sound` (bounds-free) +
    `bigMReach_complete` (its `l ≤ s ≤ u` premises discharged by `IntervalBounds.Layer.sound` /
    the new `netTrace_mem_netBoxes`) + capstone `bigM_feasible_iff_netEval`. *Soundness is
    bounds-free; completeness is where IBP earns its keep* — the precise sense of "discharge".
  - **F2 CLOSED for the linear construction.** `SelfAttention/LinearDominanceBlock.lean`:
    `GatedAttn` models the diagonal gated block; `token_deviation` finally consumes
    `linearDominance_token_bound`; `zflat_deviation` is the `√n` pooling (via `dist`/
    `EuclideanSpace.dist_eq` to dodge PiLp subtraction-indexing); `margin_deviation` is the head
    step (bias cancels, two coords each `≤ ‖W_head‖·‖Δzflat‖`); `linearDominance_robust_derived`
    assembles them with `robust_of_deviation_lt_margin` — **no assumed Lipschitz constant**.
  - **F2 fixed-pattern (softmax construction) — ASSEMBLED (AUDIT2.md G1, 2026-07-10).**
    `SelfAttention/FixedPatternBlock.lean`: `inner_deviation_bound`/`score_deviation_unit` (bilinear
    score sensitivity `B_S`, C.1) → `FixedPatternAttn.attn_dist_le` (softmax-row contraction
    `‖Δaᵢ‖ ≤ ½‖ΔSᵢ‖`, consuming `lipschitzWith_softmax`, C.2) → `Z_deviation`/`Z_deviation_n2`
    (product-rule output bound, C.3). The `√n` pooling uses Mathlib `sq_sum_le_card_mul_sum_sq`
    (survey §7.2); the value path is coefficient-free via `attn_l1` (`‖aᵢ‖₁ = 1`). `Z_deviation_n2`
    exhibits the **leading coefficient `n/2`** — the machine-checked anchor for edge
    `attn-Lattn-n4-pooling` (candidate soundness bug: code uses `n/4`; `¼ = maxₐ a(1−a)` is the
    *entrywise* Jacobian bound — the spectral-vs-entrywise trap of §6). Gotcha this pass:
    `EuclideanSpace.dist_eq` + `congr 1` closes `√(∑ dist²)=√(∑|·−·|²)` by defeq (dist on ℝ ≡ abs),
    so no `sum_congr` needed.
- **F2-B CLOSED (unconditional).** `ForMathlib/Analysis/SoftmaxLipschitz.lean`: `softmax` def;
  `softmax_nonneg`/`softmax_sum_one` discharge R1's probability-vector hypotheses;
  **`hasFDerivAt_softmax`** proves the Fréchet derivative is `toEuclideanCLM (softmaxJac (ofLp (softmax s)))`
  — directly on `EuclideanSpace` via `hasFDerivWithinAt_piLp` (coordinatewise into the PiLp codomain) +
  the scalar quotient rule (`ContinuousLinearMap.hasFDerivAt` of `EuclideanSpace.proj` + `HasFDerivAt.exp`/
  `.fun_sum`/`.mul` + `hasDerivAt_inv`), matched to the Jacobian row via `softmaxJac_mulVec`;
  **`lipschitzWith_softmax`** then gives `LipschitzWith ½ softmax` unconditionally (`lipschitzWith_of_nnnorm_fderiv_le`
  + R1). The blunt pre-estimate (wall-prone, ~100–200 lines) held: it took ~7 build iterations, the
  friction being Mathlib API spelling (`hasFDerivAt_piLp` doesn't exist → use `hasFDerivWithinAt_piLp`
  + `hasFDerivWithinAt_univ`; `PiLp.hasFDerivAt_apply` takes `p : ℝ≥0∞` explicitly → use CLM
  `EuclideanSpace.proj`; `.sum` vs `.fun_sum`; `_root_.add_apply`/`smul_apply`/`sum_apply` vs `Matrix.*`;
  the scalar identity needs `div_mul_eq_mul_div` + `← Finset.sum_div` before `field_simp; ring`).
  ½ is tight (arXiv:2510.23012). **Deferred by request: F5 (git).**
- **External Lean survey (`EXTERNAL-LEAN-SURVEY.md`, 2026-07-09):** no drop-in Lean source exists for
  the hard results (R1/R2/R3) — they are our contribution. `girving/interval` is the reuse candidate
  ONLY for a future `float32-export` edge; TorchLean (`nktkt/leanx`) is a statement/differential-oracle
  reference (Lean 4.28, `sorry`'d float layer), not a build dependency.
- **RESEARCH + G8 PASS (2026-07-10, standalone repo aiq-veristressgt-formalization).**
  - **n/4 finding RESOLVED from primary sources → confirmed code-vs-paper bug.** Read the actual
    VeriStressGT paper (arXiv:2605.17153 §A.6): eq. 52/54 use **n/2**, derived from the spectral
    `‖∇softmax‖_op ≤ 1/2` — matching our machine-checked `Z_deviation_n2`. The shipped
    `compute_L_attn` (fixed_pattern.py) uses **n/4** (the *entrywise* Jacobian max `maxₐ a(1−a)=¼`
    mis-substituted for the spectral norm). Kim et al. (2006.04710, the cited source) give NO n/4
    and NO symmetric-halving (their bound is a different, tighter `O(√N log N)` result). So the code
    under-certifies `L_attn` 2× vs its own paper — UNSAFE. Full write-up: `FINDING-attn-Lattn-n4.md`;
    edge `attn-Lattn-n4-pooling` upgraded to `kind: code-vs-paper-bug`. Action shifts from "adjudicate"
    to "report to UCLA".
  - **G8 answered: the C\*-norm route is ℂ-only.** Tested in Lean: `CStarAlgebra (Matrix n n ℝ)`
    fails to synthesize (Mathlib C\*-algebras are complex), so the ~60-line Rayleigh-plumbing deletion
    is NOT available over ℝ — the norm bound stays the Rayleigh proof. What DOES reuse Mathlib and is
    worth having (the PR-facing shape): the **Loewner pair `softmaxJac_posSemidef` (0 ≤ J) +
    `two_smul_softmaxJac_le_one` (2•J ≤ 1)** in `SoftmaxJacobianBound.lean`, both via
    `posSemidef_iff_dotProduct_mulVec` (works over ℝ) reusing the variance lemmas `sj_var_nonneg`/`sj_var_le`.
    Gotchas: `IsSelfAdjoint.all (2:ℝ)` for the smul-Hermitian; `star x = x` via `star_trivial`;
    `Matrix.le_iff` + scoped `MatrixOrder`.
- **External Lean survey (`EXTERNAL-LEAN-SURVEY.md`, 2026-07-09):** no drop-in Lean source exists for
  the hard results (R1/R2/R3) — they are our contribution. `girving/interval` is the reuse candidate
  ONLY for a future `float32-export` edge; TorchLean (`nktkt/leanx`) is a statement/differential-oracle
  reference (Lean 4.28, `sorry`'d float layer), not a build dependency.
- **Next (suggested order):** (1) REPORT the n/4 code-vs-paper bug to UCLA (`FINDING-attn-Lattn-n4.md`);
  (2) external review of *statement faithfulness* to the PDFs (AUDIT.md §5 step 7); (3) optional
  completeness: `fixedPattern_robust_derived` (aggregate `Z_deviation` over tokens + head, mirroring
  `LinearDominanceBlock`); (4) DKPS-parity `Challenge/` packaging of the softmax candidate (now with the
  Loewner forms). F2/F4b done; git now resolved (standalone repo).

<!-- BEGIN llm_resource_tally v1.0.0 (managed block — regenerated by `install`; edits below will be overwritten) -->
## Resource accounting — the LLM compute this work costs (CRITICAL: do this every commit)

Every commit in this repo is produced by an LLM agent; we keep a **measured** per-commit
record of the tokens/model it cost (inference-time, energy & carbon are derived later).

- **After cloning**, wire the hook once (offline, idempotent): `python3 .llm_resource_tally/tool install`
- Thereafter every `git commit` auto-records. To record by hand: `python3 .llm_resource_tally/tool record`
- **At session end** (captures planning/chat that produced no commit): `python3 .llm_resource_tally/tool reconcile && python3 .llm_resource_tally/tool rollup`
- Codex agents: `python3 .llm_resource_tally/tool record --backend codex`
- Other non-Claude agents: `python3 .llm_resource_tally/tool record --backend <name> --transcript <path>`

**Tag what the work was** with `--label` (e.g. `record --label implementation`, or
`reconcile --label planning`) so non-code work is counted and attributable.

Tokens/model are MEASURED from your session transcript (deduped by message id — do NOT
hand-count). The ledger `.llm_resource_tally/ledger/` (at this repo's root) is append-only,
per-session, concurrency-safe, and stores measurements only.
<!-- END llm_resource_tally -->
