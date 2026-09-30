import H099.DeterministicP1

/-!
Article Theorem 2.2: the optimal deterministic constant at `p = 1`.
Full proof: `H099/DeterministicP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_2_2_inequality := @radialClip_envelope_p1_article
def article_2_2_optimality := @K_p_one_smallest_vector_constant

#print axioms article_2_2_inequality
#print axioms article_2_2_optimality
