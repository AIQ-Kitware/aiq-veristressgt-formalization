# CROWN, β-CROWN, and branch-and-bound (the verifier under test)

**Primary sources:**
- H. Zhang, T.-W. Weng, P.-Y. Chen, C.-J. Hsieh, L. Daniel, *Efficient Neural
  Network Robustness Certification with General Activation Functions* (CROWN),
  NeurIPS 2018. **arXiv:1811.00866**.
- S. Wang, H. Zhang, K. Xu, X. Lin, S. Jana, C.-J. Hsieh, J. Z. Kolter,
  *Beta-CROWN: Efficient Bound Propagation with Per-neuron Split Constraints for
  Complete and Incomplete Neural Network Robustness Verification*, NeurIPS 2021.
  **arXiv:2103.06624**.
- (context) K. Xu et al., *Fast and Complete: Enabling Complete Neural Network
  Verification…* (α-CROWN), ICLR 2021. **arXiv:2011.13824**.

**Grounds:** the **subject of the card** — `α-β-CROWN` is the verifier whose
`correct_fraction ≥ 0.6` within a 60 s timeout is the claim
(`cards/evaluation.yaml`, `verifier_adapters/abcrown.py`). This file transcribes
what the verifier *proves*, so the edge "theorem the verifier could return" vs.
"what the card measures" is precise.

---

## 1. CROWN — linear relaxation bound

> **Theorem (CROWN, Zhang et al. 2018).** For a ReLU network on an `L∞` `ε`-box,
> each unstable neuron `ReLU(s)` with `l<0<u` is bounded by a **linear lower and
> upper envelope**: `α·s ≤ ReLU(s) ≤ (u/(u−l))·(s−l)`, for a slope `α∈[0,1]`.
> Propagating these envelopes backward yields a **sound linear lower bound** on
> the output margin `g(x)` valid over the whole box. If the bound is `> 0`, the
> instance is certified robust.

This is an *incomplete* certifier: `bound > 0 ⟹ robust`, but `bound ≤ 0` is
inconclusive (the bound may be loose — see the **relaxation barrier**,
[`ibp-relaxation-barrier-linear-regions.md`](ibp-relaxation-barrier-linear-regions.md) §2).

## 2. β-CROWN — completeness via branch-and-bound

> **Theorem (β-CROWN, Wang et al. 2021).** Augment CROWN with per-neuron split
> constraints encoded by dual variables `β`: forcing a neuron to its active
> (`s≥0`) or inactive (`s≤0`) branch. Branch-and-bound over these splits, with
> β-CROWN bounding each subproblem, is **sound and complete**: given unbounded
> time it decides robustness exactly, matching the MILP answer, while each bound
> is GPU-parallel and far cheaper than an LP.

So α-β-CROWN interpolates: cheap incomplete CROWN bound first; if inconclusive,
split unstable neurons (the `unstable_frac` ones) and recurse. **Completeness is
asymptotic in the compute budget** — and this is the crux for the card.

## 3. The load-bearing gap: complete *in the limit*, incomplete *under a timeout*

> **The edge.** β-CROWN is complete **given unbounded time**. The card runs it
> with a **60 s per-instance timeout** (`cards/evaluation.yaml:69`,
> `algo_params.timeout: 60`). Under a finite budget the verifier is **incomplete**:
> on a hard instance it may exhaust 60 s inside branch-and-bound and return
> `unknown`/`timeout`, which the runner scores as *not correct*. By Katz et al.
> NP-completeness, some provably-UNSAT instances *will* blow the budget — by
> design, since VeriStressGT constructs high-`unstable_frac` instances.

Hence the card's `correct_fraction ≥ 0.6` is measuring **"how often does a
resource-bounded, incomplete-under-timeout verifier recover the ground-truth
UNSAT certificate that the construction guarantees."** The *ground truth* is a
theorem (the certificate); the *verifier verdict* is an empirical,
budget-dependent event. That is the whole reason there is no theorem entailing
`0.6`: the number is a property of α-β-CROWN's engineering and the 60 s budget,
not of the mathematics.

## 4. Hypotheses to scrutinize (edge candidates `CR-#`)

- **CR-1 (soundness assumed, not verified).** The card trusts that when
  α-β-CROWN returns UNSAT it is *correct* (verifier soundness). VeriStressGT's
  entire point is to test this: the paper reports finding **numeric-tolerance
  bugs** where a verifier returns the wrong verdict on a provably-robust instance.
  So CR-1 is the edge the benchmark most wants to expose — "verifier claims UNSAT"
  vs. "the certificate theorem says UNSAT" can *disagree* through float tolerance.
- **CR-2 (completeness → timeout).** The proved property is asymptotic
  completeness; the measured property is decision-within-60 s. The gap is the
  branch-and-bound tree size, predicted by `unstable_frac` / linear-region count
  (DP-1, DP-2). This is the theorem↔card altitude gap for the verifier side.
- **CR-3 (CROWN relaxation vs. the construction's Lipschitz cert).** For
  `deep_contractive_cnn`, the *construction* certifies via a global-Lipschitz
  argument; CROWN certifies via *local linear envelopes*. These are different
  proofs of the same fact — an instance easy for one can be hard for the other.
  The edge: the ground-truth certificate and the verifier's certificate are **not
  the same theorem**, so "verifier fails" ≠ "instance not robust."

## 5. Formalization target (Lean)

Not a target to formalize CROWN/β-CROWN internals (that is a verifier
correctness project of its own). The formal object here is the **specification**:
`sound(verifier) : verifier(x)=UNSAT → robust(x)` and
`complete(verifier) : robust(x) → eventually verifier(x)=UNSAT` (no time bound).
State these as the interface, then the card edge is literally the two dropped
qualifiers — soundness *assumed* (CR-1) and completeness *time-bounded* (CR-2).
This is the cleanest way to make "the card stands on verifier soundness" a
checkable pointer rather than a footnote.
