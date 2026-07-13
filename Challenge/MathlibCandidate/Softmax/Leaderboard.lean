/-
# Softmax: tight ½-Lipschitz + Loewner Jacobian bounds (Mathlib candidate 01) — solution / axiom audit

Imports the project and runs `#print axioms` on each leaf theorem.  A clean audit
(`{propext, Classical.choice, Quot.sound}`) transitively certifies the whole proof tree,
including `hasFDerivAt_softmax` and `softmax_jacobian_opNorm_le_half`.
-/
import ForMathlib.Analysis.SoftmaxLipschitz
import ForMathlib.Analysis.SoftmaxJacobianBound

#print axioms VeriStressGT.ForMathlib.lipschitzWith_softmax
#print axioms VeriStressGT.ForMathlib.softmaxJac_posSemidef
#print axioms VeriStressGT.ForMathlib.two_smul_softmaxJac_le_one
