# `ExactMILP` — T3

**Result:** the big-M ReLU MILP **exactly** encodes robustness; given valid
interval bounds and an `OPTIMAL` solve it returns the exact adversarial radius.
**Papers:** Tjeng–Xiao–Tedrake 2019 ([arXiv:1711.07356](https://arxiv.org/abs/1711.07356)); Katz et al. *Reluplex* 2017 ([arXiv:1702.01135](https://arxiv.org/abs/1702.01135)) — NP-completeness (cited, not a target).
**Prose:** [`../prose/exact-milp-and-npcompleteness.md`](../prose/exact-milp-and-npcompleteness.md).
**Grounds:** `mlp_relu.milp.exact_radius` (the ground-truth oracle).

Status is tracked centrally in [`../formalization.yaml`](../formalization.yaml); all
declarations below are **proved** (zero `sorry`).

| Declaration | File | What it claims |
|---|---|---|
| `bigM_relu_faithful` | `Basic.lean` | **soundness**: big-M constraints (+ `a ∈ {0,1}`) ⟹ `z = max 0 s` |
| `bigM_relu_complete` | `Basic.lean` | **completeness**: for `l ≤ s ≤ u`, `z = max 0 s` is feasible for some `a ∈ {0,1}` |
| `label_sound_of_optimal` | `Basic.lean` | valid bounds + OPTIMAL ⟹ the `ε`-box is **disjoint** from the adversarial set (edges MILP-1/2) |
| `advSet` | `Network.lean` | the TRUE adversarial set on `IntervalBounds.netEval`; `infDist` = exact L∞ radius `r*` |
| `robust_of_lt_infDist_advSet` / `label_sound_net_of_optimal` | `Network.lean` | geometric label soundness over the concrete set (F4/F4b) |
| `infDist_inter_closedBall_of_exists_mem_ball` | `Network.lean` | non-binding `Rmax` ⟹ infimum unchanged (edge `milp-rmax-clamp`) |
| `BigMReach` / `bigMReach_sound` / `bigMReach_complete` | `Network.lean` | whole-network big-M encoding: feasible set = true network map (prose Theorem A) |
| `bigM_feasible_iff_netEval` | `Network.lean` | capstone: inside the box, feasible ⟺ `= netEval net x` |

Together `bigM_relu_faithful` (soundness) + `bigM_relu_complete` (completeness) pin the
per-neuron feasible set to `{(max 0 s, indicator)}` — the exact encoding.  We formalize
*encoding faithfulness*, not solver correctness.

**F4b CLOSED:** `Network.lean` wires the `(l,u)`-validity premise to
`IntervalBounds`. The asymmetry is the point: `bigMReach_sound` is **bounds-free** (the
big-M constraints alone pin `z = max 0 s`), while `bigMReach_complete` is where IBP earns
its keep — its per-stage `l ≤ s ≤ u` premises are discharged by `IntervalBounds.Layer.sound`
(and `netTrace_mem_netBoxes`) as the box propagates along the induction. `advSet` gives
the exact-radius oracle its true adversarial set in the network vocabulary. The `OPTIMAL`
premise remains edge `milp-incomplete-label`; a clamped radius is edge `milp-rmax-clamp`
(now anchored by `infDist_inter_closedBall_of_exists_mem_ball`). The remaining unformalized
trust is exactly "Gurobi returns the true optimum" + float-vs-real (`float32-export`).
