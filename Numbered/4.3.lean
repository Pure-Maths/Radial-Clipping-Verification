import H099.SignedSupport
import H099.SignedSupportP1

/-!
Article Corollary 4.3: the full signed support function.
Full proofs: `H099/SignedSupport.lean` and `H099/SignedSupportP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_4_3_gt_one := @articleSignedValues_isLUB
def article_4_3_p_one := @signedAttainableValuesP1_isLUB

#print axioms article_4_3_gt_one
#print axioms article_4_3_p_one
