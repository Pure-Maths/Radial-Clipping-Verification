import SharpRadialClipping.Article41
import SharpRadialClipping.ConvexHullExact

/-!
Article Theorem 4.1: exact attainable set and explicit excluded arc.
Full proofs: `SharpRadialClipping/Article41.lean`, `SharpRadialClipping/ConvexHullExact.lean`, and
their imported geometry and attainable-set modules.
-/

noncomputable section
set_option linter.defProp false

def article_4_1_exact_set := @articleAttainablePairs_eq_closedHullRegion_diff_explicitCurvedUpperArc
def article_4_1_convex_hull := @closedConvexHull_articleAttainablePairs_eq_signedSupportRegion

#print axioms article_4_1_exact_set
#print axioms article_4_1_convex_hull
