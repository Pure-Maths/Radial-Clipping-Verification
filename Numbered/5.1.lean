import SharpRadialClipping.ApplicationReinsuranceFull

/-!
Article Corollary 5.1: risk-adjusted reinsurance cost bound from IID losses.
Full proof: `SharpRadialClipping/ApplicationReinsuranceFull.lean`; random-sum moment
derivations: `SharpRadialClipping/ApplicationRandomSum*.lean` and
`SharpRadialClipping/ApplicationReinsuranceIID.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_5_1_reinsurance := @reinsuranceRiskCost_le_of_iid

#check article_5_1_reinsurance
#print axioms article_5_1_reinsurance
