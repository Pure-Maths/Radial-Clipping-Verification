import SharpRadialClipping.Sharpness
import SharpRadialClipping.StochasticSharpP1

/-!
Article Proposition 3.2: sharpness of the stochastic constant.
Full proofs: `SharpRadialClipping/Sharpness.lean` and `SharpRadialClipping/StochasticSharpP1.lean`.
For `1 < p ≤ 2`, the universal upper bound plus a matching supremum on
centered two-point laws gives the article's supremum over all laws.
-/

noncomputable section
set_option linter.defProp false

def article_3_2_all_laws_upper := @stochasticClippingRatio_le_K_p_of_memLp
def article_3_2_gt_one := @sSup_centeredBoolStochasticRatios_eq_K_p
def article_3_2_p_one := @sSup_p1StochasticRatios_eq_K_p

#check article_3_2_all_laws_upper
#check article_3_2_gt_one
#check article_3_2_p_one
#print axioms article_3_2_all_laws_upper
#print axioms article_3_2_gt_one
#print axioms article_3_2_p_one
