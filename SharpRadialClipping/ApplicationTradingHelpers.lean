import SharpRadialClipping.Deterministic

/-! Elementary real-variable estimates for the clipped portfolio update. -/

namespace SharpRadialClipping

/-- Projection of a real number onto the no-leverage interval. -/
def projectUnit (x : ℝ) : ℝ := max 0 (min 1 x)

theorem projectUnit_nonneg (x : ℝ) : 0 ≤ projectUnit x := by
  unfold projectUnit
  exact le_max_left _ _

theorem projectUnit_le_one (x : ℝ) : projectUnit x ≤ 1 := by
  unfold projectUnit
  exact max_le (by norm_num) (min_le_left _ _)

theorem portfolio_factor_pos {r w : ℝ} (hr : 0 < r) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 < 1 + w * (r - 1) := by
  have hwr : 0 ≤ w * r := mul_nonneg hw0 hr.le
  rcases lt_or_eq_of_le hw1 with h | h
  · nlinarith
  · subst w
    nlinarith

/-- The logarithmic one-period gain lies below its tangent at the current portfolio weight. -/
theorem log_growth_tangent {r u w : ℝ} (hr : 0 < r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Real.log (1 + u * (r - 1)) - Real.log (1 + w * (r - 1)) ≤
      ((r - 1) / (1 + w * (r - 1))) * (u - w) := by
  let a : ℝ := 1 + u * (r - 1)
  let b : ℝ := 1 + w * (r - 1)
  have ha : 0 < a := portfolio_factor_pos hr hu0 hu1
  have hb : 0 < b := portfolio_factor_pos hr hw0 hw1
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have heq : a / b - 1 = ((r - 1) / b) * (u - w) := by
    field_simp [hb.ne']
    dsimp [a, b]
    ring
  exact heq ▸ h

/-- Metric projection onto `[0,1]` cannot increase distance to a point in the interval. -/
theorem interval_projection_distance {x u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |projectUnit x - u| ≤ |x - u| := by
  unfold projectUnit
  rcases le_total x 0 with hx | hx
  · have hmin : min 1 x = x := min_eq_right (by linarith)
    rw [hmin, max_eq_left hx]
    rw [abs_of_nonpos (by linarith : 0 - u ≤ 0), abs_of_nonpos (by linarith : x - u ≤ 0)]
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · rw [min_eq_right hx1, max_eq_right hx]
    · rw [min_eq_left hx1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      rw [abs_of_nonneg (by linarith : 1 - u ≥ 0),
        abs_of_nonneg (by linarith : x - u ≥ 0)]
      linarith

/-- The projected gradient step yields the usual squared-distance potential estimate. -/
theorem projected_update_potential {w u z μ : ℝ} (hμ : 0 < μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    z * (u - w) ≤
      ((u - w) ^ 2 - (u - projectUnit (w + μ * z)) ^ 2) / (2 * μ) +
        μ / 2 * z ^ 2 := by
  have hdist := interval_projection_distance (x := w + μ * z) hu0 hu1
  have hsq : (u - projectUnit (w + μ * z)) ^ 2 ≤ (u - (w + μ * z)) ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_sub_comm] using hdist
  have hμ0 : 0 < 2 * μ := by positivity
  have hre : μ / 2 * z ^ 2 = μ ^ 2 * z ^ 2 / (2 * μ) := by
    field_simp
  rw [hre, ← add_div]
  apply (le_div_iff₀ hμ0).2
  nlinarith [hsq]

/-- The log of a positive finite-horizon portfolio product is the sum of period log gains. -/
theorem portfolio_log_prod {T : ℕ} {r w : ℕ → ℝ}
    (hr : ∀ t < T, 0 < r t) (hw0 : ∀ t < T, 0 ≤ w t)
    (hw1 : ∀ t < T, w t ≤ 1) :
    Real.log ((Finset.range T).prod (fun t ↦ 1 + w t * (r t - 1))) =
      (Finset.range T).sum (fun t ↦ Real.log (1 + w t * (r t - 1))) := by
  apply Real.log_prod
  intro t ht
  have hlt : t < T := Finset.mem_range.mp ht
  exact (portfolio_factor_pos (hr t hlt) (hw0 t hlt) (hw1 t hlt)).ne'

/-- Consecutive squared-distance potentials telescope. -/
theorem trading_potential_telescope (T : ℕ) (u : ℝ) (w : ℕ → ℝ) :
    (Finset.range T).sum (fun t ↦ (u - w t) ^ 2 - (u - w (t + 1)) ^ 2) =
      (u - w 0) ^ 2 - (u - w T) ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      ring

end SharpRadialClipping

#print axioms SharpRadialClipping.log_growth_tangent
#print axioms SharpRadialClipping.interval_projection_distance
#print axioms SharpRadialClipping.projected_update_potential
#print axioms SharpRadialClipping.portfolio_log_prod
#print axioms SharpRadialClipping.trading_potential_telescope
