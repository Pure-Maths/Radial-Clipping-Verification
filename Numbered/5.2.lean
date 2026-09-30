import H099.ApplicationTrading

/-!
Article Corollary 5.2: trading regret against every constant portfolio weight.
Full proof: `H099/ApplicationTrading.lean`; auxiliary arguments:
`H099/ApplicationTradingHelpers.lean`.
-/

noncomputable section
set_option linter.defProp false

def article_5_2_trading := @trading_regret_bound

#print axioms article_5_2_trading
