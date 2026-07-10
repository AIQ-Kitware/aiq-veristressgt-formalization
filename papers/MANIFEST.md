# Source papers — manifest

The PDFs themselves are **git-ignored** (see `.gitignore`); only this manifest and
the fetch script are committed. Run [`fetch_papers.sh`](fetch_papers.sh) to
download them into this directory. Each entry gives the theorem id from
[`../theorem-map.md`](../theorem-map.md), arXiv id, and the local filename.

| Theorem | arXiv | File | Why |
|---|---|---|---|
| — (UCLA paper) | 2605.17153 | `2605.17153-veristressgt-stress-testing.pdf` | The VeriStressGT paper: provably-robust instances + Difficulty Profile |
| T6 | 2602.06105 | `2602.06105-polynomial-nn-verification.pdf` | Polynomial-net verification via ED degree (`algebraic_boundary`; smoke-test mix-in) |
| T1 | 1802.04034 | `1802.04034-lipschitz-margin-training.pdf` | Lipschitz-margin certificate: `margin > √2·L·ε ⟹ robust` |
| T1′ | 1704.08847 | `1704.08847-parseval-networks.pdf` | Parseval/spectral-norm Lipschitz composition (`L=∏‖Wᵢ‖₂`) |
| T2 | 2006.04710 | `2006.04710-lipschitz-constant-self-attention.pdf` | Self-attention is not globally Lipschitz; softmax-Jacobian bound |
| T3 | 1711.07356 | `1711.07356-milp-robustness.pdf` | Exact `L∞` radius via big-M MILP |
| T3 | 1702.01135 | `1702.01135-reluplex.pdf` | NP-completeness of exact ReLU verification |
| T4 | 1810.12715 | `1810.12715-interval-bound-propagation.pdf` | IBP soundness (Difficulty Profile) |
| T4 | 1902.08722 | `1902.08722-convex-relaxation-barrier.pdf` | Convex-relaxation barrier |
| T4 | 1402.1869 | `1402.1869-linear-regions.pdf` | Linear-region count (Montúfar et al.) |
| T5 | 1811.00866 | `1811.00866-crown.pdf` | CROWN linear-relaxation certification |
| T5 | 2103.06624 | `2103.06624-beta-crown.pdf` | β-CROWN complete branch-and-bound (α-β-CROWN) |
| 1309.0049 | 1309.0049 | `1309.0049-ed-degree.pdf` | Euclidean-distance degree of an algebraic variety (T6 foundation) |

All arXiv ids verified against arxiv.org listings on 2026-07-03.
