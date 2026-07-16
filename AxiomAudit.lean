/-
AxiomAudit.lean — reproducible axiom hygiene check (audit F11).

Runs `#print axioms` on every public theorem in the seven libraries.  A clean run
prints only `{propext, Classical.choice, Quot.sound}` for each (or "does not depend
on any axioms"); any `sorryAx` / `Lean.ofReduceBool` / `native_decide` would show up
here.  Driven by `scripts/check.sh`, which builds the project and greps this file's
output for anything unexpected.

Not a `lean_lib` / default target — run with `lake env lean AxiomAudit.lean` after
`lake build`.
-/

import ForMathlib
import LipschitzMargin
import SelfAttention
import IntervalBounds
import ExactMILP
import AlgebraicBoundary
import Verifier

open VeriStressGT

-- ForMathlib (4)
#print axioms ForMathlib.ibp_affine_sound
#print axioms ForMathlib.ibp_relu_sound
#print axioms ForMathlib.lipschitz_affine_of_opNorm
#print axioms ForMathlib.softmax_jacobian_opNorm_le_half
#print axioms ForMathlib.softmaxJac_posSemidef
#print axioms ForMathlib.two_smul_softmaxJac_le_one

-- ForMathlib.SoftmaxLipschitz — F2-B (softmax LipschitzWith ½, 6)
#print axioms ForMathlib.softmax_nonneg
#print axioms ForMathlib.softmax_sum_one
#print axioms ForMathlib.softmaxJac_opNorm_le_half
#print axioms ForMathlib.softmaxJac_mulVec
#print axioms ForMathlib.hasFDerivAt_softmax
#print axioms ForMathlib.lipschitzWith_softmax

-- ForMathlib.SoftmaxTight — B3 tightness witnesses (2)
#print axioms ForMathlib.softmaxJac_opNorm_eq_half_witness
#print axioms ForMathlib.lipschitzWith_softmax_optimal

-- LipschitzMargin.Basic (3)
#print axioms LipschitzMargin.robust_of_margin_gt
#print axioms LipschitzMargin.argmax_stable_of_margin_gt
#print axioms LipschitzMargin.robust_of_deviation_lt_margin

-- LipschitzMargin.DeepContractiveCNN — T1' + specializations (8)
#print axioms LipschitzMargin.AffLayer.map_lipschitz
#print axioms LipschitzMargin.netLipschitz
#print axioms LipschitzMargin.netProd_eq
#print axioms LipschitzMargin.dccnn_margin_lipschitz
#print axioms LipschitzMargin.dccnn_robust_via_net
#print axioms LipschitzMargin.dccnn_robust_via_net_upper
#print axioms LipschitzMargin.dccnn_robust_of_true_L
#print axioms LipschitzMargin.dccnn_robust_of_upper_bound

-- LipschitzMargin.DeepContractiveCNNConcrete — B1.6 concrete ReLU activation (3)
#print axioms LipschitzMargin.lipschitzWith_reluMap
#print axioms LipschitzMargin.reluLayer_W
#print axioms LipschitzMargin.dccnn_robust_concrete

-- LipschitzMargin.DccnnLInfBox — B4 honest L∞-box √d certificate + model bridge (3)
#print axioms LipschitzMargin.dist_le_sqrt_dim_mul_linf
#print axioms LipschitzMargin.dccnn_robust_linf_box
#print axioms LipschitzMargin.Layer.toAffLayer_eval

-- SelfAttention (5)
#print axioms SelfAttention.linearDominance_token_bound
#print axioms SelfAttention.linearDominance_robust
#print axioms SelfAttention.gap_iff_stability_margin
#print axioms SelfAttention.gap_implies_stability_margin
#print axioms SelfAttention.fixedPattern_robust

-- SelfAttention.LinearDominanceBlock — T2 linear derivation (audit F2, 4)
#print axioms SelfAttention.token_deviation
#print axioms SelfAttention.zflat_deviation
#print axioms SelfAttention.margin_deviation
#print axioms SelfAttention.linearDominance_robust_derived

-- SelfAttention.FixedPatternBlock — T2 fixed-pattern C.1/C.2/C.3 (audit F2-C + AUDIT2 G1, 7)
#print axioms SelfAttention.inner_deviation_bound
#print axioms SelfAttention.score_deviation_unit
#print axioms SelfAttention.pooling_leading_coeff
#print axioms SelfAttention.FixedPatternAttn.attn_dist_le
#print axioms SelfAttention.FixedPatternAttn.attn_l1
#print axioms SelfAttention.FixedPatternAttn.Z_deviation
#print axioms SelfAttention.FixedPatternAttn.Z_deviation_n2
#print axioms SelfAttention.FixedPatternAttn.zflat_deviation
#print axioms SelfAttention.FixedPatternAttn.margin_deviation
#print axioms SelfAttention.fixedPattern_robust_derived
#print axioms SelfAttention.euclid_dist_le_sqrt_card_mul
#print axioms SelfAttention.FixedPatternAttn.score_row_deviation

-- SelfAttention.ConcreteGlue — B1 shared L∞→ℓ² token glue (2)
#print axioms SelfAttention.token_l2_dev
#print axioms SelfAttention.clm_token_dev

-- SelfAttention.FixedPatternConcrete — B1 concrete dot-product instance (3)
#print axioms SelfAttention.dotProductAttn_score_apply
#print axioms SelfAttention.dotProductAttn_V_apply
#print axioms SelfAttention.fixedPattern_robust_concrete

-- SelfAttention.LinearDominanceConcrete — B1 concrete inner-product gate (3)
#print axioms SelfAttention.innerGate_w_apply
#print axioms SelfAttention.innerGate_V_apply
#print axioms SelfAttention.linearDominance_robust_concrete

-- SelfAttention.FixedPatternStable — B2 paper Prop 6 pattern stability (2)
#print axioms SelfAttention.dotProductAttn_score_entry_dev
#print axioms SelfAttention.dotProductAttn_pattern_stable

-- SelfAttention.DominantKey — B6 paper Lemma 8 dominant-key bound (1)
#print axioms SelfAttention.attn_dominant_key_bound

-- IntervalBounds (4)
#print axioms IntervalBounds.Layer.sound
#print axioms IntervalBounds.ibp_network_sound
#print axioms IntervalBounds.robust_of_ibp_lower_pos
#print axioms IntervalBounds.netTrace_mem_netBoxes

-- ExactMILP (3)
#print axioms ExactMILP.bigM_relu_faithful
#print axioms ExactMILP.bigM_relu_complete
#print axioms ExactMILP.label_sound_of_optimal

-- ExactMILP.Network — T3/F4b whole-network big-M + advSet wiring (8)
#print axioms ExactMILP.robust_of_lt_infDist_advSet
#print axioms ExactMILP.label_sound_net_of_optimal
#print axioms ExactMILP.infDist_inter_closedBall_of_exists_mem_ball
#print axioms ExactMILP.robust_of_no_adv_in_ball
#print axioms ExactMILP.bigMReach_sound
#print axioms ExactMILP.bigMReach_complete
#print axioms ExactMILP.bigM_feasible_iff_netEval
#print axioms ExactMILP.bigM_adversary_iff

-- AlgebraicBoundary (2)
#print axioms AlgebraicBoundary.robust_of_lt_dist_boundary
#print axioms AlgebraicBoundary.robust_of_numerical_lower_bound

-- Verifier (1)
#print axioms Verifier.sound_unsat_robust
