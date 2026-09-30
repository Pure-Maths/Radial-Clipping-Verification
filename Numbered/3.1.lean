import SharpRadialClipping.Stochastic
import SharpRadialClipping.StochasticConditionalP1

/-!
Article Theorem 3.1: the stochastic clipping envelope for `1 ≤ p ≤ 2`.
Full proofs: `SharpRadialClipping/Stochastic.lean` and `SharpRadialClipping/StochasticConditionalP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_3_1_gt_one := @stochastic_radialClip_envelope_of_memLp
def article_3_1_p_one := @stochastic_radialClip_envelope_p1

#print axioms article_3_1_gt_one
#print axioms article_3_1_p_one
