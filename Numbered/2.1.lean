import SharpRadialClipping.Deterministic

/-!
Article Theorem 2.1: exact deterministic joint envelope.
Full proof: `SharpRadialClipping/Deterministic.lean`; scalar optimization: `SharpRadialClipping/Scalar.lean`.
The two declarations below expose the proved inequality and optimality under
the article number without changing their statements.
-/

noncomputable section
set_option linter.defProp false

def article_2_1_inequality := @radialClip_envelope
def article_2_1_optimality := @K_p_smallest_vector_constant

#check article_2_1_inequality
#check article_2_1_optimality
#print axioms article_2_1_inequality
#print axioms article_2_1_optimality
