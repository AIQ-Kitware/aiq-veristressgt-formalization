/-
Root module for the `ForMathlib` staging library (VeriStressGT thread).

Paper-agnostic results the robustness-certificate libraries need, restated in
Mathlib idiom — the potential upstream contributions. One file per proposed
Mathlib destination path, mirroring `aiq-dkps-formalization/ForMathlib`.

See `ForMathlib/README.md` for the candidate list and status.
-/

import ForMathlib.Analysis.OperatorNormLipschitz
import ForMathlib.Analysis.SoftmaxJacobianBound
import ForMathlib.Analysis.SoftmaxLipschitz
import ForMathlib.Analysis.SoftmaxTight
import ForMathlib.Analysis.IntervalArithmeticSound
-- Topology/RobustBallOffClosed removed: the intended lemma already exists as
-- `Metric.disjoint_closedBall_of_lt_infDist` (Mathlib
-- Topology/MetricSpace/HausdorffDistance.lean). AlgebraicBoundary calls it directly.
