import SharpRadialClipping.Sharpness
import SharpRadialClipping.StochasticSharpP1

/-!
Article Proposition 3.2: sharpness of the stochastic constant.
Full proofs: `SharpRadialClipping/Sharpness.lean` and `SharpRadialClipping/StochasticSharpP1.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_3_2_gt_one := @sSup_centeredBoolStochasticRatios_eq_K_p
def article_3_2_p_one := @sSup_p1StochasticRatios_eq_K_p

#print axioms article_3_2_gt_one
#print axioms article_3_2_p_one
