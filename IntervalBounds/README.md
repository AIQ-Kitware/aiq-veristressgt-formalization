# `IntervalBounds` — T4

**Result:** interval bound propagation is **sound** — the propagated output box
contains the true output range over the input box.
**Paper:** Gowal et al. 2018 ([arXiv:1810.12715](https://arxiv.org/abs/1810.12715)); relaxation barrier Salman 2019; linear regions Montúfar 2014.
**Prose:** [`../prose/ibp-relaxation-barrier-linear-regions.md`](../prose/ibp-relaxation-barrier-linear-regions.md).

Status tracked in [`../formalization.yaml`](../formalization.yaml); all **proved**.

| Declaration | File | What it claims |
|---|---|---|
| `Layer.sound` | `Basic.lean` | one affine/ReLU layer's box propagation contains `eval` |
| `ibp_network_sound` | `Basic.lean` | whole-network box containment (induction over a concrete `Layer` list) |
| `robust_of_ibp_lower_pos` | `Basic.lean` | positive IBP lower bound ⟹ true output positive |
| `netTrace_mem_netBoxes` | `Basic.lean` | **every-stage** containment: each trace value lies in its propagated box (audit F4b) |

Doubly load-bearing: (1) grounds the Difficulty Profile coordinates
(`unstable_frac`, `ibp_relative_gap`); (2) its output **discharges** the `(l,u)`-validity
hypothesis of the exact-MILP oracle. `netTrace_mem_netBoxes` is the every-stage
strengthening `ExactMILP/Network.lean` consumes: in `bigMReach_complete` each intermediate
pre-activation's box validity comes from `Layer.sound` propagating along the induction
(edge MILP-1, audit **F4b closed**). The per-step containment lemmas live in
`ForMathlib/Analysis/IntervalArithmeticSound.lean`. **Scope note (audit F8):** `Layer n`
is constant-width (`n×n`); genuinely heterogeneous shapes embed by zero-padding.
