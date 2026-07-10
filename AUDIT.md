# Outside audit — VeriStressGT Lean formalization

**Date:** 2026-07-07 · **Auditor:** independent review pass (Claude, at Kitware's request),
distinct from the repo's own self-review/self-audit passes referenced in `AGENTS.md` §9.
**Scope:** everything under `formalizations/veristressgt/` — the seven Lean libraries, the
planning layer (`prose/`, `theorem-map.md`, `ucla-formalization-edges.md`,
`formalization.yaml`), cross-checked against the UCLA empirical code
(`ta1/VeriStressGT/src/VeriStressGT/`), the evaluation card, and the reference repo
`aiq-dkps-formalization`.

---

## 1. Verdict (executive summary)

**The mechanical claims check out.** `lake build` completes green (verified, 8595 jobs,
toolchain `leanprover/lean4:v4.31.0-rc2`, Mathlib pinned to the DKPS rev), there are zero
`sorry`/`admit`/custom `axiom` declarations in the sources, and an independent
`#print axioms` sweep over all 20 public theorem declarations returned only
`{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no `native_decide`. Every
theorem that is stated is genuinely proved, and I found **no mathematically false
statement** among them.

**The completeness claims need qualification.** "All 16 target lemmas proved" is true of
the statements as written, but roughly half the proved lemmas are wrappers or one-line
rewrites, and the two *derivation* halves that would connect the proved margin lemmas to
the actual UCLA constructions are not formalized:

1. **T1′ (the spectral-norm composition bound) is not formalized at all** — every
   `LipschitzMargin` theorem takes `LipschitzWith L g` as an opaque hypothesis, and the
   constant `L = σ_proj·λ^D·‖w_out‖₁` never appears in Lean. A source comment claiming
   the composition is done "inline" is wrong (Finding F1).
2. **T2 (attention) is two proved but disconnected halves** — the repo says this itself
   (`AGENTS.md` §9), and the honesty is commendable, but the audit adds a new concrete
   defect: the `linear_dominance` wrapper's ε-bookkeeping does not match the UCLA
   certificate it cites (Finding F3).

There are also process gaps that matter for the stated goal — *a separate evidential
product of correctness* — the largest being that **the entire `formalizations/` tree is
untracked in git** (Finding F5), and that the axiom audit exists only as this document's
claim rather than as a committed, reproducible artifact (Finding F11).

Bottom line: this is a well-constructed, honestly documented formalization whose proved
content is real but narrower than its status lines suggest. Section 5 gives a concrete
path to a defensible "complete" state.

---

## 2. What was independently verified

| Check | Method | Result |
|---|---|---|
| Build | `lake build` from a clean lock (packages symlinked to the DKPS build) | **green**, 8595 jobs |
| Zero `sorry` | `grep -rn "sorry\|admit\|axiom" --include="*.lean"` excluding `.lake` | only two *docstring* mentions (one stale — F6) |
| Axiom hygiene | temporary file `#print axioms` on all 20 public theorems, `lake env lean` | all `{propext, Classical.choice, Quot.sound}`; `Verifier.sound_unsat_robust` axiom-free |
| Toolchain/pin | `lean-toolchain`, `lake-manifest.json` vs DKPS repo | matches (`v4.31.0-rc2`, mathlib `476fb97b621c…`) |
| Code cross-refs | read the cited lines of `deep_contractive_cnn.py`, `linear_dominance.py`, `fixed_pattern.py`, `exact_radius.py`, `cards/evaluation.yaml` | line citations accurate; one semantic mismatch found (F3) |

Proof-level spot checks (read line-by-line, statements confirmed true and proofs sound):

- `ForMathlib.softmax_jacobian_opNorm_le_half` — the flagship. The Rayleigh-quotient
  route is correct: `J = diag a − aaᵀ` is real-symmetric; `⟪Jv,v⟫ = Var_a(v)`;
  `0 ≤ Var_a(v)` (mean-shift expansion) and `Var_a(v) ≤ ((v_max−v_min)/2)² ≤ ½‖v‖²`
  (Popoviciu via midpoint, then the two-element subsum). Tightness at `a = (½,½)`
  checks out (eigenvalues `0, ½`). The `open scoped Matrix.Norms.L2Operator` correctly
  makes `‖·‖` the spectral norm — the faithfulness trap flagged in `AGENTS.md` §6 is
  properly avoided. This is genuinely a self-contained Mathlib candidate.
- `ibp_affine_sound` / `ibp_relu_sound` / `ibp_network_sound` — the `W⁺/W⁻` sign-split
  per-entry bounds are correct; the whole-network statement is a real induction over a
  concrete `Layer` list with concrete `eval`/`prop` functions (non-vacuous, as claimed).
- `robust_of_margin_gt` and its wrappers — correct; standard Lipschitz-margin argument.
- `linearDominance_token_bound` — correct bilinear product-rule bound.
- `bigM_relu_faithful` / `bigM_relu_complete` — correct, and the earlier self-audit's
  soundness/completeness split is the right fix; together they pin the feasible set.
- `robust_of_lt_dist_boundary` — correct IVT-on-preconnected-ball argument.

---

## 3. Content classification (what "16 lemmas proved" actually covers)

The proved declarations divide into three tiers. This matters for how the result is
represented upstream (to MAGNET, to UCLA, in the parent planning doc):

**Tier 1 — substantive mathematics (the real evidential content):**
`softmax_jacobian_opNorm_le_half`, `ibp_affine_sound`, `ibp_network_sound` (+
`Layer.sound`), `robust_of_margin_gt`, `linearDominance_token_bound`,
`bigM_relu_faithful`, `bigM_relu_complete`, `robust_of_lt_dist_boundary`.

**Tier 2 — thin but honest specializations:** `argmax_stable_of_margin_gt`,
`dccnn_robust_of_true_L`, `dccnn_robust_of_upper_bound`, `robust_of_ibp_lower_pos`,
`robust_of_numerical_lower_bound`, `ibp_relu_sound`, `lipschitz_affine_of_opNorm`.
These are one-to-three-line reductions, but each deliberately carries an edge as a named
hypothesis — that is their point, and it is well executed.

**Tier 3 — trivial under their own definitions:** `sound_unsat_robust` (unfolds `Sound`),
`label_sound_of_optimal` (a rewrite along its equality premise — see F4),
`gap_implies_stability_margin` (multiply an inequality by `α > 0`),
`linearDominance_robust` / `fixedPattern_robust` (both are `robust_of_margin_gt` plus a
`toNNReal` coercion, with the load-bearing Lipschitz fact *assumed*).

Tier 3 being trivial is not itself a defect — spec-level statements are a legitimate
design (the repo says so). The defect is only in *accounting*: status lines that count
"16/16 proved" without this stratification overstate mathematical coverage. Honest
summary: **8 substantive theorems, 7 edge-carrying specializations, 5 spec/rewrite
statements; the two construction-facing derivations (T1′ composition, T2 block
Lipschitz) remain unformalized.**

---

## 4. Findings

Ordered by severity. "Faithfulness" = mismatch between the Lean statement and the
source it claims to render; "completeness" = declared target not actually covered.

### F1 · HIGH (completeness + misleading comment) — T1′ is not formalized, and a comment claims otherwise

`ForMathlib/Analysis/OperatorNormLipschitz.lean:40-43` states the composition bound
`LipschitzWith (∏‖Wᵢ‖₊) net` is "NOT staged here … The LipschitzMargin library composes
it inline rather than restating a tautology." **Nothing composes anything anywhere**:
`grep` for `LipschitzWith.comp` / `∏` over all libraries finds only this comment. Every
`LipschitzMargin` theorem takes `hg : LipschitzWith L g` as an opaque hypothesis; there
is no Lean model of the network `fc ∘ (ReLU∘Conv)^D ∘ ReLU∘Proj`, and the certified
constant `L = σ_proj·λ^D·‖w_out‖₁` (`compute_true_lipschitz_bound`,
`deep_contractive_cnn.py:235`) never appears. Consequently the `dccnn-L-power-iter`
edge — the repo's headline, "severity: high" edge — anchors to
`dccnn_robust_of_upper_bound`, whose premise `L ≤ L̂` is about an *abstract* `L` that
Lean never relates to the product of spectral norms the edge is actually about.

The README's library table ("T1/T1′ — scalar Lipschitz-margin certificate **+
spectral-norm composition**") and `LipschitzMargin/README.md` ("with `L = ∏‖Wᵢ‖₂`")
both imply T1′ coverage that does not exist. `AGENTS.md` §9 names the *attention* block
gap as "the one remaining open item" but not this one — yet it is the same shape of gap
on the CNN thread.

**Fix:** either (a) formalize it — see §5 step 3, it is genuinely small; or (b) correct
the comment and the two READMEs to say T1′ is *not yet* formalized and add it to the
open-gaps list alongside the attention item.

### F2 · HIGH (completeness, acknowledged) — T2 is two proved halves with no bridge

Acknowledged in `AGENTS.md` §9 and in both attention docstrings, recorded here so the
audit is self-contained, with one addition. Proved: the per-token bilinear bound
(`linearDominance_token_bound`) and the softmax-Jacobian seed
(`softmax_jacobian_opNorm_le_half`). Not formalized: everything connecting them to the
certificates — the attention block as a map, `token_bound → LipschitzWith` for the
linear case, and for the softmax case the entire `compute_L_attn` aggregation
(`fixed_pattern.py:56-71`): the `B_S = α(2√d + εd)` score bound, the `n/4` pooling of
the `½` Jacobian bound, the `√d·σ(W_V)` value path, and the cross term. Edge SA-2's own
prose says the per-token accounting is "worth transcribing … into Lean"; it is not
transcribed. The `n/4` bookkeeping is exactly the kind of constant-chasing where errors
hide, and it currently has **no formal witness at all** — only the `½` seed does.

### F3 · MEDIUM (faithfulness, new) — `linearDominance_robust` double-counts ε

The UCLA certificate is `m(X₀) > cert_rhs` with
`cert_rhs = 2·L_h·√n·B_max` (`linear_dominance.py:206`) and **ε already inside
`B_max`** (`dw = ε·2(gate+ε)`, `dV = ε·√d·σ_V`, lines 189–196): `B_max` is a *total
box-deviation* bound, not a per-unit-distance Lipschitz constant. The Lean wrapper's
own file header transcribes this correctly ("cert: m(X₀) > 2·L_h·√n·B_max (line 206)"),
but the theorem then states the margin condition as `(2·√n·Bmax)·ε < g x₀` and the
Lipschitz premise as `LipschitzWith (2·√n·Bmax).toNNReal g` — multiplying by ε **again**.
The theorem is internally consistent (it's just `robust_of_margin_gt` for an arbitrary
constant), but as a rendering of this construction its constant means the wrong thing:
plugging the code's `B_max` in makes the hypothesis one ε-factor weaker than the code's
check, and the assumed `LipschitzWith` constant one the block does not satisfy per unit
distance. Contrast `fixedPattern_robust`, which is dimensionally right (`L_attn` *is* a
sensitivity constant and the code multiplies by ε at `fixed_pattern.py:110`).

**Fix:** restate the linear-dominance margin step in "total deviation" form —
`(∀ x, dist x x₀ ≤ ε → ‖block x − block x₀‖ ≤ D) → margin > 2·L_h·√n·D → robust` — or
divide ε out of `Bmax`'s definition and document it as a sensitivity. Do this *before*
attempting the F2 bridge for the linear case, or the bridge will not typecheck against
the shipped constant.

### F4 · MEDIUM (statement weaker than its docstring) — `label_sound_of_optimal`

The docstring claims "the closed ε-box contains no adversary and UNSAT is the correct
label," but the conclusion is only `ε < Metric.infDist x₀ advSet` — obtained by
rewriting the premise `hoptimal : infDist = rStar`. The geometric endpoint (the ball is
disjoint from `advSet`) is one lemma away (`Metric.disjoint_closedBall_of_lt_infDist`,
which the repo already knows about) and should be the stated conclusion so the theorem
says what its docstring says. Two related accounting issues: (a) `advSet` is fully
opaque — nothing ties it to a network, a box, or misclassification, so the MILP thread
never touches the `Layer`/`netEval` vocabulary that `IntervalBounds` built for it,
despite the cross-repo claim that IBP "discharges the MILP oracle's `(l,u)` validity"
(no Lean statement consumes `ibp_network_sound` from `ExactMILP`); (b) the
`milp-rmax-clamp` edge (rated **high** in `ucla-formalization-edges.md`) is silently
folded into `hoptimal` and absent from `formalization.yaml`'s `edges:` block.

### F5 · HIGH (process) — the work is not under version control

`git status` in the parent repo shows `?? formalizations/` — the entire directory,
including all Lean sources and this planning layer, is untracked: not its own git repo,
not a submodule, no commits, no remote. `AGENTS.md` §8 describes the intended
repo/submodule wiring; it has not been done. For an artifact whose purpose is
*evidential*, provenance is part of the evidence — and right now a disk failure erases
the whole product. This should be fixed before anything else in §5.

### F6 · MEDIUM (documentation drift) — status is recorded in ~10 places and most are stale

The proof pass updated `README.md`, `formalization.yaml:status`, and `AGENTS.md` but
left everything else at scaffold state:

- `ForMathlib/README.md`: "every statement here is currently `sorry`" — false; all proved.
- All six `<Library>/README.md` status columns still say `sorry`.
- `IntervalBounds/README.md` names `robust_of_ibp_margin_pos` — the declaration is
  `robust_of_ibp_lower_pos` (dangling name).
- `ExactMILP/README.md` table omits `bigM_relu_complete` and still describes
  `bigM_relu_faithful` as the biconditional ("⟺") the self-audit split it away from.
- `SelfAttention/FixedPattern.lean:59` docstring: softmax bound "itself still `sorry`" — stale.
- `lakefile.toml` header comment and `formalization.yaml:project.status_note` both say
  "SCAFFOLD … proofs are `sorry` placeholders" — contradicting `status.repository_build`
  in the *same yaml file*.
- `README.md` "Next steps" §2 says "Prove the three recommended first targets" (done) and
  §3 says to land the `edges:` block "once those give real Lean anchors" (already landed).
- The "16 target lemmas" count matches no enumeration I can construct; there are 20
  public theorems (21 with `Layer.sound`). Whatever the intended count, state the list.

Single-fact-single-place discipline would prevent recurrence: keep live status *only* in
`formalization.yaml`, and make every README point at it.

### F7 · MEDIUM (edge accounting) — `formalization.yaml` carries 4 of the 12 documented edges

`ucla-formalization-edges.md` tabulates 8 Family-A + 4 Family-B edges;
`formalization.yaml:edges` records 4. Missing entirely: `milp-rmax-clamp` (**high**),
`attn-fixed-pattern-gap` (med — now has a real Lean anchor in
`gap_implies_stability_margin`), `float32-export`, `poly-line-sampling`,
`empirical-not-proof`, `attn-Lattn-constant`, `card-timeout-incomplete` (has a Lean
anchor in `CompleteInLimit`), `card-threshold-0.6`, `card-cert-mismatch`. If the yaml is
what the MAGNET runner will surface, the two high/anchored ones at minimum belong there.

### F8 · LOW (modelling scope) — `Layer` is constant-width

`IntervalBounds.Layer n` forces square `n×n` affine maps, so the formalized network
type cannot express the actual UCLA MLP shapes (varying widths), nor conv structure.
Soundness is insensitive to this (pad with zeros), but the restriction is nowhere
stated. Generalizing to `Layer : ℕ → ℕ → Type` (heterogeneous dims, e.g. an indexed
list) is routine and would also serve the F1 fix.

### F9 · LOW (statement artifact) — `robust_of_lt_dist_boundary` and the empty boundary

Mathlib's `Metric.infDist x₀ ∅ = 0`, so when `g` has no zeros at all (boundary empty —
the trivially-robust case) the hypothesis `ε < infDist` is unsatisfiable for `ε ≥ 0` and
the theorem is inapplicable exactly where robustness is easiest. Harmless for the UCLA
use (their varieties are nonempty) but worth a docstring note or a
`(g ⁻¹' {0}).Nonempty` companion remark, since a naive user could read "far from an
empty boundary" as `infDist = ∞`.

### F10 · LOW (docstring precision) — `gap_implies_stability_margin` claims equivalence

The docstring says the gap condition "is *equivalent* to `δ_min > ε·C_max`"; the lemma
proves one implication (the one used). Since `α > 0` the equivalence is real — either
prove the `↔` (one extra line) or say "implies."

### F11 · MEDIUM (evidential reproducibility) — the verification story is not an artifact

The DKPS reference repo backs its claims with: per-declaration
`sorry_count`/`axioms` entries in `formalization.yaml`, a `Challenge/` layer with
conformance + leaderboard files, comparator configs, a `scripts/run_challenge_comparator.sh`,
and recorded `#print axioms` sweeps. This repo has none of that: the zero-sorry/green
claims live only in prose (README/yaml notes), and the axiom audit performed for this
document had to be reconstructed by hand. For the "separate evidential product" goal the
checks must be committed and re-runnable — see §5 step 5.

---

## 5. Instructions for reaching a completed state

Ordered; steps 1–2 are hours, steps 3–4 are the real remaining formalization work,
steps 5–7 bring the repo to DKPS evidential parity.

### Step 1 — put the work under version control (first, before touching anything)

Follow `AGENTS.md` §8: `git init` inside `formalizations/veristressgt/`, add a
`.gitignore` for `.lake/` (papers/*.pdf already ignored), commit everything, push to an
`AIQ-Kitware` remote, then wire it into `aiq-eval-runner` as a submodule (`.gitmodules`
entry + `git add formalizations/veristressgt`). Note `.lake/packages` is a symlink into
the sibling DKPS checkout — document that it must be recreated (or replaced by
`lake exe cache get`) on fresh clones; consider replacing the symlink with a
`setup_lean.sh` step so clones are self-contained.

### Step 2 — fix the documentation drift (F1-comment, F6, F7, F10)

Mechanical, no Lean required: correct the OperatorNormLipschitz "composes it inline"
note; update the seven READMEs' status columns (or better, delete their status columns
and point at `formalization.yaml`); fix the `robust_of_ibp_margin_pos` name; add
`bigM_relu_complete` to the ExactMILP table; remove the two "SCAFFOLD" notes and the
stale "still `sorry`" docstring in `FixedPattern.lean`; rewrite README "Next steps" to
the actual frontier (steps 3–4 below); replace "16 target lemmas" with an explicit
enumeration (suggest the §3 three-tier framing); add the missing anchored/high edges to
`formalization.yaml:edges` (`milp-rmax-clamp`, `attn-fixed-pattern-gap`,
`card-timeout-incomplete` at minimum).

### Step 3 — close the T1′ gap (F1) — the highest-value remaining Lean work

Small and well-scoped because the ingredients exist:

1. Generalize `IntervalBounds.Layer` to heterogeneous widths (F8), or add a parallel
   `Net` structure in `LipschitzMargin` — a list of `(W : Matrix (Fin m) (Fin n) ℝ, b)`
   layers interleaved with `1`-Lipschitz activations.
2. Prove `netLipschitz : LipschitzWith (∏ᵢ ‖Wᵢ‖₊) (netEval net)` by induction —
   each step is `lipschitz_affine_of_opNorm` (already proved) composed with the
   activation via `LipschitzWith.comp`. This is the statement the OperatorNormLipschitz
   file already names as the "genuinely reusable packaged bound."
3. Restate `dccnn_robust_of_true_L` with `hg` *discharged* by `netLipschitz` for the
   dccnn shape, so `L = σ_proj·λ^D·‖w_out‖₁` finally appears in Lean (as
   `∏‖Wᵢ‖ = σ_proj · λ^D · ‖w_out‖` under the construction's normalization hypotheses),
   and the `dccnn-L-power-iter` edge premise `L ≤ L̂` attaches to the *product*, which
   is what the edge is actually about.

### Step 4 — close the T2 gap (F2), fixing F3 on the way

Do the linear case first, as planned, but reshape the wrapper before bridging:

1. Restate `linearDominance_robust` in total-deviation form (F3 fix): hypothesis
   `∀ x ∈ box ε x₀, ‖Z x − Z x₀‖ ≤ Bmax` per token, conclusion via a deviation-margin
   lemma (a two-line variant of `robust_of_margin_gt` where `K·ε` is replaced by a
   deviation bound `D` — worth adding to `LipschitzMargin/Basic.lean` as
   `robust_of_deviation_lt_margin`).
2. Model the gated block `Z i x = w i x • V i x` concretely and derive the per-token
   deviation from `linearDominance_token_bound` plus box-bounds on `|w−w₀|` and
   `‖V−V₀‖` (both affine in the input — use `lipschitz_affine_of_opNorm`).
3. The softmax case (`compute_L_attn`'s `n/4` aggregation) is the genuinely hard
   remaining item. If it stays open, state it as an explicit named `Prop`
   (e.g. `LattnBound n d α ε V₀ W_V L`) with a `sorry`-free *definition* and keep the
   certificate conditional on it — that keeps zero-sorry status honest while making the
   open obligation a typed object instead of a docstring caveat. Record it as an edge.

### Step 5 — make the verification claims reproducible artifacts (F11)

1. Commit an `AxiomAudit.lean` (or `scripts/axiom_audit.lean`) that `#print axioms`
   every public theorem, plus a `scripts/check.sh` running
   `lake build && lake env lean AxiomAudit.lean` and grepping the output for anything
   other than the three standard axioms. (The file used for this audit can be taken
   as-is — 20 declarations, all clean on 2026-07-07.)
2. Mirror DKPS `formalization.yaml` per-declaration records: add `sorry_count: 0` and
   `axioms: [propext, Classical.choice, Quot.sound]` to each `main_targets` entry, and
   add `fidelity:` and `review:` sections (current honest values:
   `review.status: "self-assessed"`, this audit as the first outside pass).

### Step 6 — DKPS parity for the upstream candidate

`softmax_jacobian_opNorm_le_half` is the one clear Mathlib candidate. Package it the
DKPS way: a `Challenge/MathlibCandidate/SoftmaxJacobian/` with Conformance + Leaderboard
files and a comparator config. `ibp_affine_sound`/`ibp_relu_sound` are
`MathlibPending`-grade at best (NN-flavored; primitives exist); the rest are
paper-vocabulary and should stay documented-not-challenged, per the DKPS
Challenge/README rationale.

### Step 7 — external review of statements (already planned)

The repo's own next-step list ends here and this audit agrees: after steps 2–4, the
residual risk is *statement faithfulness to the PDFs* (the one thing kernel checking
cannot certify). Concrete asks for a reviewer with the papers open: the `√2` vs
scalar-margin bookkeeping (T1, prose §1 vs `robust_of_margin_gt`); the `2ε`
diameter-vs-radius convention (`dccnn_robust_of_true_L` proves a radius-`2ε` ball, a
*strengthening* of the code's ε-box claim — sound, but should be noted); the big-M
constraint set vs Tjeng et al. Eq. 5–7; and the fixed-pattern gap condition vs
`fixed_pattern.py:82-92` (matches today — F3 shows why this class of check pays).
Feeding the Appendix-A power-iteration analysis back to UCLA (edges doc, next-steps §4)
remains worthwhile and is strengthened by step 3 landing the `∏‖Wᵢ‖` object it refers to.

---

## 6. Assessment against the program goal

For the AIQ "formalization edge" mission this repo is a good instantiation of the
pattern: edges really are carried as named hypotheses in type signatures
(`hupper : L ≤ Lhat`, `hlb : distHat ≤ infDist`, `hoptimal : infDist = rStar`), which is
the design the parent planning doc calls for, and the two-family edge taxonomy is a
genuine conceptual contribution beyond the DKPS template. The mathematics that is proved
is correct and axiom-clean. What separates it from "a completed evidential product" is:
version control (F5), the two derivation gaps that leave the highest-severity edges
anchored to abstract constants rather than the constructions' actual formulas (F1, F2/F3),
reproducible verification artifacts (F11), and a documentation layer that currently
disagrees with itself about what has been done (F6). All four are addressable with the
steps above; none undermines the work already banked.
