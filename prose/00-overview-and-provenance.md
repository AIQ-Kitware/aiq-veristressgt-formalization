# Overview & provenance — the UCLA / VeriStressGT formalization thread

## The two UCLA papers

Both are from Guido Montúfar's group at UCLA (the VeriStressGT TA1 team,
submitter `davidtroxell@g.ucla.edu`).

1. **Stress-Testing Neural Network Verifiers with Provably Robust Instances**
   — Troxell, Alexandr, Hunt, Lei, Montúfar. **arXiv:2605.17153**.
   This is the VeriStressGT paper itself. Contribution: a framework that
   *generates verification instances whose robustness label is known by analytic
   construction* (not by running a verifier), plus a **verification Difficulty
   Profile** — a vector of estimable quantities that characterise *why* an
   instance is hard — used to attribute each verifier's failures to a specific
   pipeline component (numeric tolerance, relaxation quality, search).

2. **Robustness Verification of Polynomial Neural Networks**
   — Alexandr, Duan, Montúfar. **arXiv:2602.06105**.
   Certifies a robustness radius for a **polynomial** network as the **distance
   to the algebraic decision boundary**, using metric algebraic geometry: the
   **Euclidean-distance (ED) degree** counts the complex critical points of the
   squared-distance function to the boundary variety, bounding how hard the exact
   certification is. This is the theory behind the `polynomial.algebraic_boundary`
   construction, and the "verifier evaluation" the user expects VeriStressGT to
   mix in for the smoke test.

## The key structural fact (why this thread is different from JHU/DKPS)

DKPS has **one** deep theorem chain (spectral MDS concentration → query
efficiency → inference transfer) formalized end-to-end. VeriStressGT has the
opposite shape: **many small certificate theorems**, one per construction, each
a self-contained inequality of the same family:

> **certified margin at `x₀`  >  (a Lipschitz / sensitivity constant) × (perturbation radius `ε`)   ⟹   no adversarial example in the `L∞` `ε`-box   ⟹   the VNN-LIB query is UNSAT.**

The construction *chooses the network weights so the inequality holds by
construction*, then exports `(ONNX, VNN-LIB)` and asks a third-party verifier to
**re-derive** the UNSAT verdict under a resource budget. So a VeriStressGT
instance factorises into two logically separate objects:

- **The ground-truth certificate** — a *published theorem* instantiated on the
  constructed weights. This is what is **formalizable** (High): a Lipschitz-margin
  inequality, a softmax-attention sensitivity bound, an exact MILP radius, or a
  distance-to-boundary certificate. Its hypotheses are exactly the edges.
- **The card claim** — "α-β-CROWN returns the correct UNSAT verdict on ≥ 60% of
  the instances within a 60 s timeout" (`ta1/VeriStressGT/cards/evaluation.yaml`,
  `threshold = 0.6`). This is a *verifier stress-test measurement* (Low): an
  empirical threshold on a resource-bounded, incomplete verifier. There is no
  theorem entailing 60%.

The formalization edge, therefore, is not "theorem vs. its finite-sample shadow"
(as in JHU). It is:

> **(ground-truth certificate theorem, whose hypotheses the construction claims
> to satisfy)  ⟶  (the numerical/relaxation/timeout gap by which a real verifier,
> or the construction's own numerical checks, could disagree with the theorem).**

The Difficulty Profile is UCLA's own instrument for measuring the size of that
gap per instance — so several edges land on *difficulty-profile components*, not
just on verifier output.

## What is `2ε` doing everywhere?

Every construction certifies over an `L∞` box of radius `ε`. Two points in that
box differ by at most `2ε` per coordinate, so the diameter term in the Lipschitz
bound is `2ε` (e.g. `cert_bound = σ_proj · λ^D · ‖w_out‖₁ · 2ε` in
`deep_contractive_cnn.py:227`). Keep this in mind reading the transcriptions:
the published theorems are usually stated for a radius `ε` around `x₀`; the code
folds the box **diameter** into the constant.

## Provenance / repository anchors

- Empirical repo: `ta1/VeriStressGT/` in `aiq-eval-runner`, submodule of
  `github.com/dtroxell19/VeriStressGT`. Constructions under
  `src/VeriStressGT/robust_constructions/`; Difficulty Profile under
  `src/VeriStressGT/difficulty_profile/`; the card at `cards/evaluation.yaml`.
- Empirical results already banked: `aiq-evaluations`
  `PhaseI_DryRun/UCLA/VeriStressGT_mini_sweep/…/card.yaml` and
  `Debug/UCLA/AlgebraicPNNVerification/…/card.yaml`.
- Planning parent: `docs/planning/ta1-formalization-edges.md` §3.2 (this thread
  is the deep expansion of that section).
- Target Lean home (future): a `VeriStressGT/` library alongside the DKPS
  libraries, once the certificate lemmas are stated. This `prose/` is the
  pre-Lean transcription, exactly as DKPS's `prose/` preceded its Lean.
