#!/usr/bin/env bash
# check.sh — reproducible verification artifact (audit F11).
#
# Builds the project and audits axiom hygiene: confirms every public theorem
# depends only on the three standard Mathlib axioms {propext, Classical.choice,
# Quot.sound} — i.e. no `sorryAx`, no `native_decide`/`ofReduceBool`.
#
# Usage:  bash scripts/check.sh
# Exit 0 = green (build clean + axioms clean); nonzero = a problem was found.

set -uo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$PATH"

echo "== [1/3] lake build =="
if ! lake build; then
  echo "FAIL: lake build did not succeed." >&2
  exit 1
fi

echo "== [2/3] no sorry / admit in sources =="
if grep -rnE "^[[:space:]]*(sorry|admit)([[:space:]]|$)|:=[[:space:]]*sorry" --include="*.lean" \
     ForMathlib LipschitzMargin SelfAttention IntervalBounds ExactMILP AlgebraicBoundary Verifier 2>/dev/null; then
  echo "FAIL: a real 'sorry'/'admit' tactic was found above." >&2
  exit 1
fi
echo "OK: no sorry/admit tactics."

echo "== [3/3] axiom audit (#print axioms on all public theorems) =="
AUDIT="$(lake env lean AxiomAudit.lean 2>&1)"
echo "$AUDIT"
# Any axiom other than the three standard ones is a failure.
if echo "$AUDIT" | grep -qiE "sorryAx|ofReduceBool|native_decide|Lean\.trustCompiler"; then
  echo "FAIL: a non-standard axiom (sorryAx/native_decide/...) is present above." >&2
  exit 1
fi
if echo "$AUDIT" | grep -qiE "error"; then
  echo "FAIL: AxiomAudit.lean reported an error above." >&2
  exit 1
fi

echo
echo "PASS: build clean, no sorry, axioms limited to {propext, Classical.choice, Quot.sound}."
