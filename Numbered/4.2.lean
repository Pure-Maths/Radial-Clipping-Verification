import SharpRadialClipping.PointwiseArc

/-!
Article Lemma 4.2: the pointwise arc inequality and its equality cases.
Full proof: `SharpRadialClipping/PointwiseArc.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_4_2_inequality := @pointwise_rare_arc_bound
def article_4_2_equality := @pointwise_rare_arc_bound_eq_iff
def article_4_2_p_two_equality := @pointwise_rare_arc_bound_eq_p2

#check article_4_2_inequality
#check article_4_2_equality
#check article_4_2_p_two_equality
#print axioms article_4_2_inequality
#print axioms article_4_2_equality
#print axioms article_4_2_p_two_equality
