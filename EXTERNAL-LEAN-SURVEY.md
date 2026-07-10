# Survey — external (non-Mathlib) Lean 4 sources for VeriStressGT results

**Date:** 2026-07-09 · **Author:** research pass (Claude, at Kitware's request)
**Question asked:** for each difficult result the VeriStressGT formalization needs, is there
an existing non-Mathlib Lean 4 repository we can *source* it from rather than re-prove?
**Scope:** the seven Lean libraries here (`ForMathlib`, `LipschitzMargin`, `SelfAttention`,
`IntervalBounds`, `ExactMILP`, `AlgebraicBoundary`, `Verifier`) and the two open derivation
gaps (F1 T1′ spectral composition, F2-B softmax `LipschitzWith ½`). Cross-refs `AUDIT.md`,
`GUIDANCE-F2-F4b.md`, `theorem-map.md`.

---

## 0. TL;DR

- **No drop-in win exists.** Nobody has published a Lean library that proves VeriStressGT's
  load-bearing results (softmax-Jacobian operator-norm bound, spectral-norm composition,
  big-M ReLU faithfulness) in a form we could `require` and consume. The flagship
  `softmax_jacobian_opNorm_le_half` remains, as the audit said, our own contribution.
- **One genuine reuse candidate as a Lake dependency:** [`girving/interval`](#a-girvinginterval)
  — conservative floating-point interval arithmetic (Apache-2.0, importable). It is the right
  primitive if we ever close the **`float32-export`** edge (real-valued IBP → the Float32 the
  verifier actually runs). It has **no** matrix/vector layer, so it is a primitive, not a
  finished IBP.
- **One high-overlap repo to use as a *statement reference and differential oracle*, not a
  code dependency:** [`nktkt/leanx` (TorchLean)](#b-nktktleanx-torchlean) — Lean 4 IBP +
  CROWN + α,β-CROWN soundness, ReLU/affine/Conv layers, Float32 semantics. Directly parallels
  our T3/T4/T5. But it pins **Lean 4.28** (we are on **4.31-rc2**), its float layer is
  `sorry`-laden, and it is not packaged as an importable library. Value = compare our IBP /
  verifier-spec statements against theirs; do **not** take a build dependency.
- **The exact math for the open F2-B item now has a named source paper:**
  ["Softmax is ½-Lipschitz: a tight bound across all ℓ_p norms"](#f2-b-softmax-lipschitz)
  (arXiv 2510.23012). This confirms our ½ constant is tight and gives the clean argument to
  transcribe — but it is a *paper*, not a Lean artifact.
- **Two adjacent formally-verified robustness certifiers are in other provers** (Dafny, Rocq/Coq)
  and are **not sourceable** into Lean; they are architecture references only.

Bottom line: keep proving the core here. Adopt `girving/interval` only if/when we take the
float-soundness edge seriously. Use TorchLean to sanity-check our IBP/verifier *statements*.

> **Second-audit addendum (2026-07-09):** §7 below records *Mathlib-internal*
> standardization opportunities found while auditing the proofs — places where the pinned
> Mathlib already carries machinery that would replace bespoke arguments here, at the
> expense of some novelty in the proof route (not in the results). The headline: the
> flagship Jacobian bound has a shorter, more Mathlib-idiomatic **C\*-algebra/Loewner-order
> route** whose ingredients are all present in the pinned rev. §8 adds four external repos
> assessed and rejected/parked. All lemma names in §7 were verified against the pinned
> Mathlib source (file:line given).

---

## 1. What "difficult results" we are shopping for

Mapped from the library table (README) and the open findings (AUDIT.md §4–5):

| # | Result (our declaration / gap) | Library | Difficulty |
|---|---|---|---|
| R1 | Softmax Jacobian operator norm `‖diag a − aaᵀ‖₂ ≤ ½` (`softmax_jacobian_opNorm_le_half`) | ForMathlib | **hard** (flagship, self-adjoint Rayleigh route) |
| R2 | Softmax is `LipschitzWith ½` (**open, F2-B** — the consumer of R1) | ForMathlib/SelfAttention | **hard** |
| R3 | Affine map is `‖W‖₂`-Lipschitz; product-of-spectral-norms composition (**T1′, open F1**) | ForMathlib/LipschitzMargin | medium |
| R4 | IBP soundness: interval propagation encloses reachable outputs (`ibp_*_sound`) | IntervalBounds | medium |
| R5 | Big-M ReLU MILP encoding faithful/complete (`bigM_relu_faithful/_complete`) | ExactMILP | medium |
| R6 | Lipschitz-margin robustness certificate `margin > L·ε ⟹ robust` (`robust_of_margin_gt`) | LipschitzMargin | easy–medium |
| R7 | CROWN / α,β-CROWN sound + complete-in-limit *spec* (`VerifierSpec`, `sound_unsat_robust`) | Verifier | spec-level |
| R8 | Distance-to-algebraic-boundary / ED-degree certificate (`robust_of_lt_dist_boundary`) | AlgebraicBoundary | niche |
| R9 | Float32-execution soundness of any of the above (edge `float32-export`, currently *not* modeled) | — | hard, unstarted |

---

## 2. The candidate repos

### A. `girving/interval` — conservative floating-point interval arithmetic
**URL:** github.com/girving/interval · **License:** Apache-2.0 · **Packaging:** Lake package,
`require`-able · **Mathlib:** yes (tracks its own pinned rev).

**What it proves (reusable):** a software `Floating` type (64+64) with conservatively
rounded arithmetic; `Interval` (lower/upper `Floating`); the `Approx A R` typeclass
("`A` conservatively approximates `R`") with instances `Approx Interval ℝ`, `Approx Box ℂ`;
conservative field ops and **special functions `exp`, `log`, powers** with soundness lemmas
(`ApproxAdd`, `ApproxField`, …). This is the mature, battle-tested (used in Irving's Mandelbrot
/ `ray` Hausdorff-dimension project) Lean answer to "interval arithmetic that is sound against
real semantics."

**Fit:** **R9 / the `float32-export` edge, and a hardened R4.** Our `IntervalBounds` proves IBP
sound *over ℝ*. The gap the card actually cares about — α-β-CROWN runs Float32 — is exactly
what `Approx Interval ℝ` closes at the scalar level. If we ever formalize "the exported box is
conservative under rounding," this is the primitive to build on rather than re-deriving
directed rounding.

**Limits:** **no matrix/vector/tensor interval layer** — we would still build `netEval`-shaped
IBP on top. And taking it as a build dependency means reconciling its Mathlib pin with ours
(the DKPS rev). For a scalar-level float-soundness sub-result it is worth it; for the ℝ-valued
IBP we already have, it adds nothing.

### B. `nktkt/leanx` (TorchLean) — Lean 4 NN verification framework
**URL:** github.com/nktkt/leanx · arXiv:2602.22631 · **License:** MIT · **Packaging:** *not*
an importable library (research artifact, 28 files) · **Lean:** **4.28.0** (we are 4.31-rc2) ·
**Mathlib:** limited.

**What it covers (overlaps R4/R5/R6/R7 head-on):** IBP soundness ("IBP output bounds contain
all reachable outputs", `runIBP?` vs `evalGraphRec`); CROWN/LiRPA linear-relaxation soundness;
α-CROWN optimizable bounds; branch-and-bound completeness; ReLU/Linear/MatMul/Conv2D/tanh/exp
layers on a shape-indexed `Tensor α s` IR; adversarial-robustness implications from verified
bounds; reverse-mode AD correctness (Thm 2.1); an IEEE-754 binary32 kernel with a three-level
(abstract/concrete/verified) semantics.

**Fit:** this is the closest thing in existence to *our whole T3/T4/T5 cluster* done
independently. Highest value is as a **differential oracle for statements**: does their
`IBP Soundness (Theorem 1)` quantify enclosure the way our `ibp_network_sound` does? Does their
CROWN soundness match the `VerifierSpec.Sound` we assume in `Verifier`? Agreement is strong
external evidence our specs are faithful; divergence is a finding.

**Why not a dependency:** (1) Lean 4.28 vs our 4.31-rc2 — non-trivial port; (2) the float
theorems "use `sorry` due to opaque native `Float`" — the very trust boundary we would want
is the part they leave open (contrast `girving/interval`, which closes it properly); (3) not
packaged for external `require`. Treat as reference, not source.

**Note on softmax/attention:** TorchLean's soundness theorems do **not** cover softmax/attention
(Appendix D defers it). So it does **not** help R1/R2 — our attention thread stays unique.

### C. `lecopivo/SciLean` — scientific computing in Lean 4
**URL:** github.com/lecopivo/SciLean · **License:** Apache-2.0 · **Packaging:** Lake,
`require`-able · **Mathlib:** transitive.

**What it is:** n-dim arrays, symbolic autodiff *tactics/transformations*, executable numerics
(OpenBLAS). Explicitly "early stage / proof of concept." **It is definitions + AD machinery,
not proved analysis.** No theorem about softmax Jacobian, operator norm, or Lipschitz constants
that we could consume.

**Fit:** low. Only conceivable use is borrowing its softmax/`Tensor` *definitions* as modeling
scaffolding if we grow `SelfAttention` into a concrete attention map (F2 bridge) — but our
needs are proofs, which SciLean does not carry. Not a source.

### D. Floating-point substrate libraries (for R9, if pursued)
- **`girving/interval`'s `Floating`** (see A) — the pragmatic choice; soundness already proved.
- **FLoPS** (arXiv:2602.15965) — "Semantics, Operations, and Properties of P3109 Floating-Point
  Representations in Lean." A newer Lean FP-semantics library; relevant if we want *bit-level*
  Float32 conformance rather than conservative intervals. Heavier than we need for IBP soundness.
- **`MinusGix/flean`** — another Lean floating-point effort (community, less mature). Lower priority.

Use these only in service of the `float32-export` edge; none is needed for the ℝ-level results.

### E. General infrastructure (context, not a source of results)
- **CSLib** (arXiv:2602.04846) — "the Lean Computer Science Library," an emerging Mathlib-analog
  for CS (algorithms, computability, PL, logics). TorchLean cites it as complementary infra. No
  robustness/analysis results today, but it is the natural *destination* for a future
  MILP-encoding-faithfulness or verifier-spec contribution — worth tracking for the upstreaming
  question (parallels our ForMathlib → Mathlib candidate story).

---

## 3. Adjacent formally-verified certifiers — NOT sourceable (other provers)

These solve almost exactly our problem but in provers Lean cannot import from. They are
*architecture / statement references* only, and worth reading before finalizing our specs.

- **Tobler, Syeda, Murray — "A Formally Verified Robustness Certifier for Neural Networks"**
  (arXiv:2505.06958). **Dafny.** A globally-robust-network certifier proved sound; shows prior
  unverified certifiers are exploitably unsound. Directly informs our `Verifier` soundness spec
  and the `card-cert-mismatch` edge. Not Lean → not sourceable.
- **"Lipschitz-Based Robustness Certification Under Floating-Point Execution"**
  (arXiv:2603.13334). **Rocq (Coq).** Shows Lipschitz certification can be *unsound* under
  Float32, certifies no-overflow, and gives a compositional real-vs-float deviation bound that
  patches the classical certification condition. This is the rigorous version of our
  `float32-export` edge and of R6 under rounding. Strong evidence the edge is real; the proof
  is in Coq, so we would re-derive in Lean (on `girving/interval`) if we pursue R9.

---

## 4. Per-result verdict

| # | Result | Best external Lean source | Verdict |
|---|---|---|---|
| R1 | softmax-Jacobian opNorm ≤ ½ | — | **Prove here (done).** Unique; not in any Lean repo. Mathlib candidate. |
| R2 | softmax `LipschitzWith ½` (F2-B) | paper arXiv:2510.23012 (math, not Lean) | **Prove here.** Transcribe the tight-bound argument; no Lean source. |
| R3 | affine/spectral composition (T1′, F1) | Mathlib (`opNorm`, `LipschitzWith.comp`) | **Prove here** from Mathlib; small (AUDIT §5 step 3). No external repo needed. |
| R4 | IBP soundness (ℝ) | TorchLean (reference only) | **Keep ours;** cross-check statement against TorchLean's IBP soundness. |
| R5 | big-M ReLU faithfulness | TorchLean / Dafny (reference only) | **Keep ours;** compare feasible-set framing. |
| R6 | Lipschitz-margin cert | TorchLean (reference) | **Keep ours** (trivial from Mathlib). |
| R7 | CROWN / α,β-CROWN sound-complete spec | TorchLean, Dafny cert (references) | **Keep ours;** high-value to diff our `VerifierSpec` vs TorchLean's CROWN soundness. |
| R8 | ED-degree / algebraic boundary | — (no Lean ED-degree lib found) | **Keep ours** (metric core only, as scoped). |
| R9 | Float32-execution soundness (edge) | **`girving/interval`** (+ FLoPS) | **Source this** *if* we take the edge — real reuse, Apache-2.0, proofs already done. |

---

## 5. Recommendations

1. **Do not re-scope the core around any external repo.** The three hard, evidential results
   (R1, R2, R3) have no Lean source; that is precisely why they are our contribution.
2. **If/when the `float32-export` edge is prioritized: adopt `girving/interval`** as a Lake
   dependency for the scalar conservative-rounding layer, and build the vector/matrix IBP on
   top (mirroring the Rocq deviation-bound argument, arXiv:2603.13334). Budget the Mathlib-pin
   reconciliation. This is the one place external reuse beats re-deriving.
3. **Use TorchLean (`nktkt/leanx`) as a review instrument, not a dependency.** Before external
   review (AUDIT §5 step 7), diff our `ibp_network_sound`, `bigM_relu_*`, and `VerifierSpec`
   statements against TorchLean's IBP/CROWN/α,β-CROWN soundness theorems. Record agreements and
   any divergence as edges. Note their Lean 4.28 vs our 4.31-rc2, and that their float layer is
   `sorry`'d where `girving/interval`'s is not.
4. **For F2-B, cite arXiv:2510.23012** ("Softmax is ½-Lipschitz") in the softmax docstring and
   `theorem-map.md` as the tight-bound provenance for `LipschitzWith ½`, and transcribe its
   argument. This strengthens the F2-B route in `GUIDANCE-F2-F4b.md`.
5. **Track CSLib** as a second possible upstream home (besides Mathlib) for the MILP-faithfulness
   / verifier-spec results, which are CS- rather than analysis-flavored.

---

## 7. Mathlib-internal standardization opportunities (2026-07-09 audit pass)

These are not external repos — they are machinery *already in the pinned Mathlib* that
would standardize or shorten arguments currently done by hand here. Adopting them trades
proof-route novelty for idiomatic-ness, which is the right trade for the upstream story.

### 7.1 R1 via the C\*-algebra / Loewner order (replaces the Rayleigh plumbing)

The pinned Mathlib makes `Matrix n n 𝕜` with the **L²-operator norm** a `CStarRing` —
**scoped under the exact namespace this repo already opens**:
`Matrix.instCStarRing`, `scoped[Matrix.Norms.L2Operator] attribute [instance]`
(`Mathlib/Analysis/CStarAlgebra/Matrix.lean:288-291`). It also has the Loewner order
(`Matrix.instPartialOrder`, `A ≤ B ↔ (B − A).PosSemidef`,
`Mathlib/Analysis/Matrix/Order.lean:47-59`), the quadratic-form characterization
`Matrix.posSemidef_iff_dotProduct_mulVec` (`Mathlib/LinearAlgebra/Matrix/PosDef.lean:296`),
and the C\*-order↔norm bridge `CStarAlgebra.nnnorm_le_iff_of_nonneg` /
`norm_le_one_iff_of_nonneg`
(`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:240,245`).

**The standardized proof of `softmax_jacobian_opNorm_le_half`:** the two variance lemmas
already proved (`sj_var_nonneg`, `sj_var_le`) are *literally* the two Loewner facts
`0 ≤ J` and `2•J ≤ 1` via `posSemidef_iff_dotProduct_mulVec`; then
`nnnorm_le_iff_of_nonneg` gives `‖2J‖ ≤ 1`, i.e. `‖J‖ ≤ ½`, with **no**
`toEuclideanCLM`/`IsSymmetric`/`rayleighQuotient` plumbing (~60 lines deleted; the real
math — the variance bounds — is untouched).

**Caveat to check first:** the CFC-order file's instance requirements for `A` may be
stated for complex C\*-algebras; verify the chain elaborates for `Matrix n n ℝ` (if it
does not, the Loewner *statement* `0 ≤ J ∧ 2•J ≤ 1` is still worth adding as the
PR-shaped corollary, keeping the Rayleigh proof as the engine). **Upstream implication
either way:** Mathlib maintainers will likely prefer the Loewner-order formulation as the
primary statement — the norm bound is then a generic C\*-fact. Restate the PR candidate
accordingly (the `Challenge/` conformance, when built, should expose both forms).

### 7.2 The ℓ¹→ℓ² pooling step: `sq_sum_le_card_mul_sum_sq`

The fixed-pattern assembly (the remaining F2-C Lean work) needs
`(∑ |cⱼ|)² ≤ n · ∑ cⱼ²` — pinned Mathlib has it as `sq_sum_le_card_mul_sum_sq`
(`Mathlib/Algebra/Order/Chebyshev.lean`). Do not hand-roll this Cauchy–Schwarz instance;
it is the provenance of the honest `√n` (and hence the `n/2` total) in the pooling
coefficient, so citing the standard lemma strengthens the `attn-Lattn-n4-pooling` edge
argument.

### 7.3 Coordinate-of-Euclidean-vector bound: possible duplicate

`SelfAttention/LinearDominanceBlock.lean` proves a `private abs_apply_le_norm`
(`|v j| ≤ ‖v‖` on `EuclideanSpace`). Before any upstream packaging, Loogle/grep the
pinned Mathlib for an existing form (candidates: a `PiLp`/`EuclideanSpace` coordinate-norm
lemma, or derive in one line from `abs_inner_le_norm` with `EuclideanSpace.single j 1`).
Same dedup discipline that already caught `Metric.disjoint_closedBall_of_lt_infDist`.

### 7.4 Duplication *inside this repo* (not Mathlib): `softmaxJac` vs `sjJ`

`SoftmaxLipschitz.lean` re-declares the Jacobian matrix (`softmaxJac`) and re-proves
`softmaxJac_mulVec` verbatim because `sjJ`/`sjJ_mulVec` are `private` in
`SoftmaxJacobianBound.lean`. Make one public and delete the other — double maintenance
of a 14-line computation is how statements drift apart.

## 8. Additional externals assessed (2026-07-09) — parked or rejected

- **CvxLean** (verified-optimization/CvxLean; Lean 4, Mathlib-based). Verified convex-
  optimization *modeling/transformation* DSL (reductions to conic form, solver bridge).
  No robustness/NN content; would matter only if we ever formalize the *optimization*
  side of the MILP (relaxations, duality certificates). **Parked.**
- **optlib** (optsuite/optlib; Lean 4). Convex-analysis and first-order-method
  convergence proofs (gradient/subgradient/proximal). Adjacent analysis vocabulary, no
  softmax/attention/operator-norm results we can consume. **Rejected as a source.**
- **madvorak/duality** (Lean 4). LP strong duality / Farkas-type results over ordered
  fields. Relevant *only* to a future "MILP optimum certified by an LP dual bound"
  extension of `ExactMILP` (we formalize encoding faithfulness, not optimality — the
  OPTIMAL premise is deliberately an edge). Track alongside CSLib. **Parked.**
- **lean-smt / proof-producing-verifier pattern** (ufmg-smite/lean-smt; and Marabou's
  proof-production line of work). The architecture in which the *verifier emits a
  certificate that a small checked kernel replays* is the principled endgame for the
  `Verifier` spec's CR-1 edge (soundness assumed → soundness checked per-run). Nothing
  consumable today for α-β-CROWN, but if UCLA's stress test ever adopts a
  proof-producing verifier, `Verifier/Spec.lean` should grow a `CheckedRun` variant.
  **Reference for the spec's future shape.**
- **eric-wieser/lean-matrix-cookbook** (Lean 4). Matrix-identity compendium; nothing
  needed beyond what Mathlib proper already gives us here. **Rejected.**

## 9. Method / coverage note

Searched (2026-07-09): Reservoir/Lake registry, GitHub, arXiv, Lean Zulip archives for Lean 4
work on NN verification, robustness, IBP/CROWN, softmax/attention Lipschitz, operator/spectral
norms beyond Mathlib, interval arithmetic, MILP/ReLU encodings, and ED-degree. Repos assessed:
`nktkt/leanx` (TorchLean), `girving/interval`, `lecopivo/SciLean`, FLoPS, `MinusGix/flean`,
CSLib; adjacent non-Lean certifiers (Dafny 2505.06958, Rocq 2603.13334) noted for context.
Not found in Lean: a proved softmax-Jacobian/opNorm bound, a spectral-norm composition lemma
packaged for reuse, a big-M MILP faithfulness theorem, or any ED-degree machinery. The
"Formalized Hopfield Networks / Boltzmann Machines" Lean work (arXiv:2512.07766) is
NN-formalization but a different domain (convergence/Hebbian) — no overlap. Absence claims are
"not found," not "proven absent."

2026-07-09 addendum coverage: §7 anchors were verified by grepping the pinned Mathlib source
tree (`.lake/packages/mathlib`, rev per `lake-manifest.json`) — `Matrix.instCStarRing`
(CStarAlgebra/Matrix.lean:288), the Loewner order (Analysis/Matrix/Order.lean:47),
`posSemidef_iff_dotProduct_mulVec` (LinearAlgebra/Matrix/PosDef.lean:296),
`nnnorm_le_iff_of_nonneg`/`norm_le_one_iff_of_nonneg`
(CStarAlgebra/ContinuousFunctionalCalculus/Order.lean:240,245), and
`sq_sum_le_card_mul_sum_sq` (Algebra/Order/Chebyshev.lean). §8 repos assessed from prior
knowledge of the Lean ecosystem (CvxLean, optlib, madvorak/duality, lean-smt,
lean-matrix-cookbook); none carries consumable robustness/attention results.
