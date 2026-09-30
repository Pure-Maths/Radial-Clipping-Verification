import SharpRadialClipping.ApplicationTrading

/-!
Article Corollary 5.2: trading regret against every constant portfolio weight.
Full proof: `SharpRadialClipping/ApplicationTrading.lean`; auxiliary arguments:
`SharpRadialClipping/ApplicationTradingHelpers.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_5_2_trading := @trading_regret_bound

#print axioms article_5_2_trading
