import SharpRadialClipping.SignedSupport
import SharpRadialClipping.SignedSupportP1

/-!
Article Corollary 4.3: the full signed support function.
Full proofs: `SharpRadialClipping/SignedSupport.lean` and `SharpRadialClipping/SignedSupportP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_4_3_gt_one := @articleSignedValues_isLUB
def article_4_3_p_one := @signedAttainableValuesP1_isLUB

#print axioms article_4_3_gt_one
#print axioms article_4_3_p_one
