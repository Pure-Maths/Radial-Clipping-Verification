import H099.ApplicationReinsuranceFull

/-!
Article Corollary 5.1: risk-adjusted reinsurance cost bound from IID losses.
Full proof: `H099/ApplicationReinsuranceFull.lean`; random-sum moment
derivations: `H099/ApplicationRandomSum*.lean` and
`H099/ApplicationReinsuranceIID.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_5_1_reinsurance := @reinsuranceRiskCost_le_of_iid

#print axioms article_5_1_reinsurance
