import SharpRadialClipping.TwoAtom

/-!
Article Corollary 4.4: one-dimensional two-atom realization.
Full proof: `SharpRadialClipping/TwoAtom.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_4_4_realization := @articleAttainablePairs_realTwoAtom_realization
def article_4_4_p_one := @p1_articleAttainablePairs_subset_realTwoAtomPairs

#print axioms article_4_4_realization
#print axioms article_4_4_p_one
