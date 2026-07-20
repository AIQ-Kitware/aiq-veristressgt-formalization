# AIQ VeriStressGT Formalization

Lean 4 formalization of the mathematics underlying the UCLA **VeriStressGT** TA1 evaluation
card — a benchmark that ships neural-network robustness-verification instances that are
*provably robust by construction* and measures whether a third-party verifier (α-β-CROWN)
re-derives that verdict under a time budget.

This repository proves the *ground-truth* half of that benchmark: for each way VeriStressGT
constructs an instance, it states and machine-checks the robustness theorem the instance is
built to satisfy — and, in the process, surfaces places where the shipped code departs from a
sound certificate.

> **Orientation:** start with [`AGENTS.md`](AGENTS.md) (why this exists, the key structural
> facts, the working conventions, and the known traps). For a dated, evidence-scoped account
> of what was checked, at which commit, by which command, read [`STATUS.md`](STATUS.md). The
> machine-readable per-declaration status is [`formalization.yaml`](formalization.yaml). Do
> not infer current status from older audit notes.

## What is being proven

VeriStressGT is a **certificate factory**: instead of one headline theorem, it has *many
small, independent robustness certificates*, one per construction, each of the shape

> **certified margin at `x₀`  >  (a sensitivity constant) × (perturbation `ε`)  ⟹  no
> adversarial example in the `L∞` `ε`-box  ⟹  the verification query is UNSAT.**

Each construction picks network weights that make the inequality hold by construction. This
repo formalizes those certificates. In plain terms, the machine-checked results say:

- **Deep contractive CNNs.** If a network's margin at `x₀` beats its Lipschitz constant times
  the box radius, no input in the box flips the prediction — with the Lipschitz constant
  derived as the product of the layers' spectral norms, and coordinatewise ReLU proved
  `1`-Lipschitz.
- **Self-attention (two constructions).** The output of a softmax/linear attention block
  moves by a controlled amount over the box; in particular the softmax attention *pattern*
  (which key each query attends to) stays fixed across the whole box when the score gap is
  large enough, and the linear-dominance output stays close to its dominant value.
- **The softmax sensitivity itself.** Softmax is exactly `½`-Lipschitz in the Euclidean norm
  — proved, and proved *tight* (a witness attains it), via the spectral bound on its
  Jacobian `diag(a) − aaᵀ`.
- **Exact-MILP radius.** The big-M ReLU encoding faithfully represents the network, so an
  optimal MILP solution gives a sound robustness radius / label.
- **Interval bound propagation.** Propagating a box through the network soundly contains the
  true output — the every-stage version that the MILP encoding needs.
- **Polynomial networks.** A certified distance to the algebraic decision boundary implies
  robustness within that distance.
- **The verifier interface.** A soundness/completeness *specification* for the CROWN-style
  verifier the card ultimately stands on, making the card-level assumptions explicit.

A crosswalk from each construction to its published source theorem and its Lean declarations
is in [`theorem-map.md`](theorem-map.md); faithful transcriptions of every source argument
are under [`prose/`](prose/).

### What "proved" means here (scope)

What is machine-checked is the **certificate theorems** and the derivation of their sensitivity
constants from construction-level quantities (weights, token normalization, the margin) — all
with **zero `sorry`** and depending only on the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Lean is the *oracle for the mathematics*: it
establishes, beyond doubt, what the correct constants and thresholds are.

Lean does **not** read or run the shipped Python / ONNX artifacts, and there is no automated
"the code matches the theorem" check. The correspondence between code and theorem is drawn by
hand — transcribed in `prose/` and recorded as explicit **assumption → relaxation edges** (see
[`ucla-formalization-edges.md`](ucla-formalization-edges.md)). Where the code and the theorem
disagree, that is a *finding*: the machine-checked theorem supplies the authoritative value,
and reading the code shows it computes something else.

## Status

`lake build` is **green**; **zero `sorry`** in the production tree; an independent
`#print axioms` sweep over all **101 audited declarations** ([`AxiomAudit.lean`](AxiomAudit.lean),
driven by [`scripts/check.sh`](scripts/check.sh)) shows only `{propext, Classical.choice,
Quot.sound}`. The reproducible gate is a single command:

```bash
bash scripts/check.sh      # lake build + no-sorry scan + axiom audit; exit 0 = green
```

The current dated verification record — commit, toolchain, and per-stage results — is
[`STATUS.md`](STATUS.md). The comparison against the sibling DKPS/DRSB formalizations, and the
development roadmap it drove (all landed), is in `../REFERENCE-COMPARISON.md`.

## Findings

Formalizing the ground truth produced **one confirmed soundness finding** on the shipped
pipeline, plus one candidate that the same machinery later **refuted** — both are recorded, the
refutation included, because the corrected mathematics is itself the point of the method.

1. **Confirmed — self-attention `L_attn` under-counts the softmax pooling by 2×.**
   [`FINDING-attn-Lattn-n4.md`](FINDING-attn-Lattn-n4.md). The shipped `compute_L_attn` uses a
   coefficient `n/4`, where both the source paper and a machine-checked derivation
   (`FixedPatternAttn.Z_deviation_n2`) give `n/2` — the *entrywise* softmax-Jacobian bound
   (`¼`) mis-substituted for the *spectral* one (`½`). The shipped instances set their margin
   slack too small to absorb the 2× gap, so their "robust" labels are unproven by the
   construction's own theorem as shipped. In the *unsafe* direction (a smaller certified
   constant can ship a mislabeled instance).

2. **Refuted — the DCCNN `√d` metric point is a bookkeeping note, not an exposure.**
   [`FINDING-dccnn-linf-sqrtd.md`](FINDING-dccnn-linf-sqrtd.md). A draft claimed the DCCNN
   certificate under-certifies the `L∞` box by omitting the `ℓ∞→ℓ₂` factor `√d`. An audit
   caught the error and it is now machine-checked
   ([`DccnnReadout.lean`](LipschitzMargin/DccnnReadout.lean)): the shipped read-out row is
   *uniform*, so its ℓ₂ operator norm `‖w‖₂ = 1/√flat_dim` is far below the ℓ₁ value the draft
   used, and the all-ℓ₂ certificate clears the shipped margin by ≈ 8.8×. **No shipped instance
   is exposed.** What survives is a latent robustness-of-process note (the formula would be
   unsafe for a *non-uniform* read-out).

Both are documented as edges in [`formalization.yaml`](formalization.yaml) /
[`ucla-formalization-edges.md`](ucla-formalization-edges.md). Finding 1 is stated carefully —
the certificate is *unproven as shipped* (the Lipschitz bound is sufficient, not necessary), so
an empirical check (PGD or a complete verifier at a box corner) is what would tell whether any
individual label is actually false. The separate, still-open `dccnn-L-power-iter` edge (the
reshaped-kernel spectral norm is not the true convolution operator norm) is the strongest
remaining DCCNN concern.

## Libraries

Each top-level library is one certificate family; every declaration's docstring cites its
prose source, and each library's `README.md` gives the construction crosswalk.

| Library | What it proves |
|---|---|
| `ForMathlib` | Reusable, source-agnostic pieces: operator-norm = Lipschitz constant, the softmax-Jacobian spectral bound and its tightness, interval-arithmetic soundness steps. |
| `LipschitzMargin` | The Lipschitz-margin robustness certificate, the spectral-norm composition for deep CNNs (with a concrete ReLU layer), and the honest `L∞`-box threshold with the `√d` factor. |
| `SelfAttention` | Self-attention sensitivity: concrete softmax (fixed-pattern) and linear-dominance blocks, the derived output-deviation bounds, softmax pattern-stability over the box, and the dominant-key bound. |
| `IntervalBounds` | Interval bound propagation soundness, whole-network and every-stage. |
| `ExactMILP` | Faithfulness of the big-M ReLU MILP encoding and soundness of the resulting label / radius. |
| `AlgebraicBoundary` | Distance-to-the-algebraic-boundary robustness for polynomial networks. |
| `Verifier` | The verifier soundness / completeness specification the card stands on. |
| `Challenge` / `comparator` | A Mathlib-candidate comparator package for the softmax result (definition, derivative, tight `½`-Lipschitz, Loewner Jacobian bounds); see [`Challenge/README.md`](Challenge/README.md). Not a default build target. |

## Build

Toolchain `leanprover/lean4:v4.31.0-rc2`; Mathlib pinned in `lake-manifest.json`.

```bash
bash setup_lean.sh      # elan + the pinned toolchain
lake exe cache get      # prebuilt Mathlib oleans (or reuse a sibling build)
lake build              # green: zero `sorry`
```

Check a single file fast (no build lock): `lake env lean LipschitzMargin/Basic.lean`. Reproduce
the whole verification story with [`scripts/check.sh`](scripts/check.sh).

## Layout

```text
.
├── AGENTS.md                       # start here: purpose, structure, conventions, traps
├── STATUS.md                       # dated, evidence-scoped verification record
├── FINDING-*.md                    # substantiated write-ups of the two findings
├── ForMathlib.lean / ForMathlib/   # reusable results (imports: Mathlib only)
├── <Library>.lean / <Library>/     # one library per certificate family
├── Challenge/ + comparator/        # Mathlib-candidate comparator package (softmax)
├── prose/                          # faithful transcriptions of every source argument
├── theorem-map.md                  # construction ⟷ source-theorem ⟷ Lean crosswalk
├── ucla-formalization-edges.md     # assumption → relaxation edges to the empirical repo
├── formalization.yaml              # machine-readable metadata, targets, status, edges
├── AxiomAudit.lean / scripts/check.sh   # the reproducible verification gate
└── lakefile.toml / lake-manifest.json / lean-toolchain / setup_lean.sh
```

The pre-Lean layer (`theorem-map.md`, `ucla-formalization-edges.md`, `prose/`) identifies the
source theorems, transcribes their arguments, and draws the edges to the empirical repository
`../../ta1/VeriStressGT/`.
