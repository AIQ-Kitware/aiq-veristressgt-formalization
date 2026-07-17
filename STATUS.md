# STATUS — evidence-scoped verification record

Single dated record of *what was checked, at which commit, by which command* (bridging step
B5, REFERENCE-COMPARISON.md §6 — the DRSB `STATUS.md` discipline). This file states only what
was actually run; it does not generalize a green build into repository-wide claims beyond the
declarations the axiom audit covers. The machine-readable mirror is
[`formalization.yaml`](formalization.yaml) (`review:` section); narrative context is in
[`AGENTS.md`](AGENTS.md) and [`README.md`](README.md).

## Latest verification

- **Date:** 2026-07-16
- **Commit checked:** `f442d23` (`feat(B2): paper Prop 6 pattern stability on the concrete instance`)
  and the doc/status commit that follows it.
- **Toolchain:** `leanprover/lean4:v4.31.0-rc2`; Mathlib pinned in `lake-manifest.json`.
- **Command:** `bash scripts/check.sh` (`scripts/check.sh` sha256 `16a8d126…e98a096`).
- **Result: PASS.** Exit 0. The three stages reported:
  1. `lake build` — completed successfully, no errors.
  2. no-`sorry`/`admit` scan over `ForMathlib LipschitzMargin SelfAttention IntervalBounds
     ExactMILP AlgebraicBoundary Verifier` — `OK: no sorry/admit tactics.`
  3. axiom audit — `#print axioms` over all **82 audited declarations**
     ([`AxiomAudit.lean`](AxiomAudit.lean)) shows only `{propext, Classical.choice, Quot.sound}`
     (no `sorryAx`, `native_decide`, or `ofReduceBool`).

**Scope of the claim.** "Proved" here means the *published certificate theorems* (T1–T6
templates) and, for the concrete constructions, the derivation of the sensitivity constants
from construction-level quantities. It is **not** a claim that every *shipped* instance is
certifiably robust — see the two findings below. The 82 audited declarations are exactly the
list in `AxiomAudit.lean`; nothing outside that list is asserted axiom-clean by this record.

## Reference-comparison roadmap (REFERENCE-COMPARISON.md §6)

| Step | Status | Anchor |
|---|---|---|
| B1 concretization layer | ✅ landed | `fixedPattern_robust_concrete`, `linearDominance_robust_concrete`, `reluLayer` |
| B2 pattern stability (Prop 6) | ✅ landed | `dotProductAttn_pattern_stable` |
| B3 tightness as theorems | ✅ landed | `softmaxJac_opNorm_eq_half_witness`, `lipschitzWith_softmax_optimal` |
| B4 model unification + LM-4 | ✅ landed | `Layer.toAffLayer_eval`, `dccnn_robust_linf_box` |
| B5 process parity | ✅ this file | — |
| B6 optional depth | ✅ Lemma 8 landed | `attn_dominant_key_bound` (heterogeneous-width `Layer` + sharper softmax row remain as further optional depth) |

## Confirmed findings (machine-checked anchors; NON-LEAN action = report to UCLA)

1. **`attn-Lattn-n4`** — `compute_L_attn` uses `n/4`; the paper (eq. 54) and the machine-checked
   `Z_deviation_n2` use `n/2`. Code under-certifies `L_attn` ~2× (unsafe). Shipped fixed-pattern
   instances at `margin_slack = 1.05 < 2` are in the exposed regime.
   [`FINDING-attn-Lattn-n4.md`](FINDING-attn-Lattn-n4.md).
2. **`dccnn-linf-sqrtd-metric`** — ⚠️ **exposure claim REFUTED by AUDIT4 (2026-07-17, J1); do
   not report as a soundness finding.** The shipped uniform read-out has `‖w_out‖₂ = 1/√flat_dim`,
   and the all-ℓ₂ certificate clears the shipped margin ≈ 8.8×; no shipped instance is exposed.
   Surviving content: a norm-bookkeeping note (formula incoherent as written; unsafe only for a
   non-uniform read-out with `√d·‖w‖₂ > 2‖w‖₁`). See [`AUDIT4.md`](AUDIT4.md) §3 and step N1;
   [`FINDING-dccnn-linf-sqrtd.md`](FINDING-dccnn-linf-sqrtd.md) carries the superseded banner.

## How to reproduce

```bash
bash setup_lean.sh          # elan + pinned toolchain (first time)
lake exe cache get          # prebuilt Mathlib oleans (or reuse the sibling build)
bash scripts/check.sh       # build + no-sorry + axiom audit; exit 0 = green
```

Per-commit LLM resource measurements are in `.llm_resource_tally/ledger/` (see the resource
accounting section of [`AGENTS.md`](AGENTS.md)).
