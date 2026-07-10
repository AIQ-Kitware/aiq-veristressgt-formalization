# `Verifier` — T5

**Result:** a *specification* of the verifier the card stands on, so the Family-B
card edges become explicit dropped qualifiers.
**Papers:** CROWN, Zhang et al. 2018 ([arXiv:1811.00866](https://arxiv.org/abs/1811.00866)); β-CROWN, Wang et al. 2021 ([arXiv:2103.06624](https://arxiv.org/abs/2103.06624)).
**Prose:** [`../prose/crown-branch-and-bound.md`](../prose/crown-branch-and-bound.md).
**Grounds:** the `cards/evaluation.yaml` claim (`correct_fraction ≥ 0.6` @ 60 s).

Status tracked in [`../formalization.yaml`](../formalization.yaml); the theorem below is
**proved**, and `Sound`/`CompleteInLimit` are definitions (the spec vocabulary).

| Declaration | File | What it is |
|---|---|---|
| `Sound` | `Spec.lean` | def: `run i = unsat ⟹ robust i` (edge CR-1, **assumed** by card) |
| `CompleteInLimit` | `Spec.lean` | def: robust ⟹ eventually unsat, **no time bound** (edge `card-timeout-incomplete`, CR-2) |
| `sound_unsat_robust` | `Spec.lean` | proved: UNSAT + soundness ⟹ robust |

We do **not** formalize CROWN internals. The point is to name the two qualifiers
the card drops — soundness (assumed; the paper finds it violated by float-tolerance
bugs) and completeness (time-bounded to 60 s) — so `correct_fraction ≥ 0.6` is
visibly a measurement, not a theorem.
