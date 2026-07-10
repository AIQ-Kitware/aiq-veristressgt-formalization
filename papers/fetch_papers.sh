#!/usr/bin/env bash
# Fetch the source PDFs for the UCLA / VeriStressGT formalization thread.
# PDFs are git-ignored (see .gitignore); this script + MANIFEST.md are the
# committed record. Idempotent: skips files already present.
set -euo pipefail
cd "$(dirname "$0")"

# arXiv id -> local filename (see MANIFEST.md for what each one is)
declare -A PAPERS=(
  [2605.17153]="2605.17153-veristressgt-stress-testing.pdf"
  [2602.06105]="2602.06105-polynomial-nn-verification.pdf"
  [1802.04034]="1802.04034-lipschitz-margin-training.pdf"
  [1704.08847]="1704.08847-parseval-networks.pdf"
  [2006.04710]="2006.04710-lipschitz-constant-self-attention.pdf"
  [1711.07356]="1711.07356-milp-robustness.pdf"
  [1702.01135]="1702.01135-reluplex.pdf"
  [1810.12715]="1810.12715-interval-bound-propagation.pdf"
  [1902.08722]="1902.08722-convex-relaxation-barrier.pdf"
  [1402.1869]="1402.1869-linear-regions.pdf"
  [1811.00866]="1811.00866-crown.pdf"
  [2103.06624]="2103.06624-beta-crown.pdf"
  [1309.0049]="1309.0049-ed-degree.pdf"
)

for id in "${!PAPERS[@]}"; do
  out="${PAPERS[$id]}"
  if [[ -s "$out" ]]; then
    echo "skip  $id ($out already present)"
    continue
  fi
  echo "fetch $id -> $out"
  curl -fsSL --retry 3 -A "Mozilla/5.0 (aiq-eval-runner fetch)" \
    "https://arxiv.org/pdf/${id}" -o "$out" \
    || echo "  WARN: failed to fetch $id (fetch manually from https://arxiv.org/abs/${id})"
  sleep 1  # be polite to arxiv
done

echo "done. PDFs are git-ignored; see MANIFEST.md."
