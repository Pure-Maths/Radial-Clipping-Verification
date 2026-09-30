import SharpRadialClipping.ConditionalExtended
import SharpRadialClipping.StochasticConditionalP1

/-!
Article Corollary 3.3: conditional envelope, including random measurable thresholds.
Full proofs: `SharpRadialClipping/ConditionalExtended.lean` and
`SharpRadialClipping/StochasticConditionalP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_3_3_gt_one := @conditional_radialClip_envelope_variable_full
def article_3_3_p_one := @conditional_radialClip_envelope_variable_full_p1

#check article_3_3_gt_one
#check article_3_3_p_one
#print axioms article_3_3_gt_one
#print axioms article_3_3_p_one
