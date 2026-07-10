/-
Verifier.Spec — the verifier interface as a specification, so the Family-B card
edges become explicit dropped qualifiers rather than prose footnotes.

Paper: Zhang et al. 2018 (CROWN, arXiv:1811.00866); Wang et al. 2021 (β-CROWN,
arXiv:2103.06624).  Transcription: prose/crown-branch-and-bound.md.

The point is NOT to formalize CROWN internals (a verifier-correctness project of
its own) but to state what the card assumes:
  • CR-1 soundness  : verifier UNSAT ⟹ robust     — ASSUMED by the card, and
                       exactly what the paper finds violated by tolerance bugs.
  • CR-2 completeness: robust ⟹ eventually UNSAT   — holds with NO time bound;
                       the card imposes 60 s, making the verifier incomplete.
-/

import Mathlib

set_option autoImplicit false

namespace VeriStressGT.Verifier

/-- Verifier verdicts. -/
inductive Verdict | unsat | sat | timeout

/-- An abstract verifier over an instance type `ι`, with a ground-truth
robustness predicate `Robust`. -/
structure VerifierSpec (ι : Type*) where
  robust : ι → Prop
  run    : ι → Verdict

/-- **CR-1 soundness (assumed by the card).** UNSAT implies truly robust. -/
def Sound {ι : Type*} (V : VerifierSpec ι) : Prop :=
  ∀ i, V.run i = Verdict.unsat → V.robust i

/-- **CR-2 completeness, time-unbounded (proved for β-CROWN).** A budgeted verdict
`runBudget i t`; completeness says a robust instance is eventually decided as the
budget grows.  The card fixes `t = 60 s`, which is NOT `∀ᶠ t`. -/
def CompleteInLimit {ι : Type*} (robust : ι → Prop)
    (runBudget : ι → ℕ → Verdict) : Prop :=
  ∀ i, robust i → ∃ T, ∀ t ≥ T, runBudget i t = Verdict.unsat

/--
**What a ground-truth certificate buys, and what the card measures.**
If the verifier is `Sound` and returns UNSAT, the instance is robust.  The card's
`correct_fraction ≥ 0.6` is the empirical frequency of `run i = unsat` over the
swept instances at a 60 s budget — which, under soundness, lower-bounds the
verifier's recovered-certificate rate but is entailed by NO theorem (edge
`card-threshold-0.6`).  Stated so the two dropped qualifiers are visible. -/
theorem sound_unsat_robust {ι : Type*} (V : VerifierSpec ι)
    (hSound : Sound V) (i : ι) (h : V.run i = Verdict.unsat) :
    V.robust i :=
  hSound i h

end VeriStressGT.Verifier
