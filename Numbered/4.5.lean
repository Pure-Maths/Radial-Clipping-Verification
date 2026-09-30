import SharpRadialClipping.AllThresholdsFinalPrep

/-!
Article Theorem 4.5: one law in `ℝ³` realizes all clipping thresholds.
Full proof: `SharpRadialClipping/AllThresholdsFinalPrep.lean` and the imported
`SharpRadialClipping/AllThresholds*.lean` modules.
-/

noncomputable section
set_option linter.defProp false

def article_4_5_all_thresholds := @exists_all_thresholds_three_dimensional_realization

#check article_4_5_all_thresholds
#print axioms article_4_5_all_thresholds
