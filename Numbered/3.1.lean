import H099.Stochastic
import H099.StochasticConditionalP1

/-!
Article Theorem 3.1: the stochastic clipping envelope for `1 ≤ p ≤ 2`.
Full proofs: `H099/Stochastic.lean` and `H099/StochasticConditionalP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_3_1_gt_one := @stochastic_radialClip_envelope_of_memLp
def article_3_1_p_one := @stochastic_radialClip_envelope_p1

#print axioms article_3_1_gt_one
#print axioms article_3_1_p_one
