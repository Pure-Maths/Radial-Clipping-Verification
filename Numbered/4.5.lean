import H099.AllThresholdsFinalPrep

/-!
Article Theorem 4.5: one law in `ℝ³` realizes all clipping thresholds.
Full proof: `H099/AllThresholdsFinalPrep.lean` and the imported
`H099/AllThresholds*.lean` modules.
-/

noncomputable section
set_option linter.defProp false

def article_4_5_all_thresholds := @exists_all_thresholds_three_dimensional_realization

#print axioms article_4_5_all_thresholds
