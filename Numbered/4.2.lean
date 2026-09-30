import SharpRadialClipping.AttainableP1

/-!
Article Remark 4.2: the exact attainable region at p = 1.
Full proof: `SharpRadialClipping/AttainableP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_4_2_attainable_set := @attainableBiasEnergyPairsP1_eq_triangle_diff_top

#check article_4_2_attainable_set
#print axioms article_4_2_attainable_set
