import SharpRadialClipping.Deterministic

/-!
# Pointwise estimate used on the upper boundary

This is the elementary radial inequality stated as a lemma inside the proof
of Theorem 4.1 of the article.
-/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise residual--energy comparison at clipping threshold one. -/
theorem pointwise_rare_arc_bound
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (x : E) :
    ‖x - radialClip 1 x‖ + ‖radialClip 1 x‖ ^ 2 ≤
      ‖x‖ * ‖radialClip 1 x‖ ^ (2 * (p - 1) / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 < 2 * (p - 1) / p := div_pos (mul_pos (by norm_num) (sub_pos.mpr hp)) hp0
  by_cases hx0 : ‖x‖ = 0
  · have hx : x = 0 := norm_eq_zero.mp hx0
    subst x
    simp
  by_cases hx1 : ‖x‖ ≤ 1
  · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx0)
    rw [radialClip_of_norm_le hx1, sub_self, norm_zero, zero_add]
    have he : 1 + 2 * (p - 1) / p ≤ 2 := by
      have hq : 2 * (p - 1) / p ≤ 1 :=
        (div_le_iff₀ hp0).2 (by nlinarith)
      linarith
    have hpow : ‖x‖ ^ (2 : ℝ) ≤ ‖x‖ ^ (1 + 2 * (p - 1) / p) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx1 he
    have hright : ‖x‖ * ‖x‖ ^ (2 * (p - 1) / p) =
        ‖x‖ ^ (1 + 2 * (p - 1) / p) := by
      rw [Real.rpow_add hxpos, Real.rpow_one]
    rw [hright]
    simpa only [Real.rpow_two] using hpow
  · have hxlt : 1 < ‖x‖ := lt_of_not_ge hx1
    have hnorm : ‖radialClip 1 x‖ = 1 := by
      rw [norm_radialClip (by norm_num), min_eq_right hxlt.le]
    have hres : ‖x - radialClip 1 x‖ = ‖x‖ - 1 := by
      rw [norm_sub_radialClip (by norm_num), max_eq_left (by linarith)]
    rw [hnorm, hres]
    simp

/-- For `1 < p < 2`, the pointwise inequality is strict strictly inside the
unit ball away from the origin. -/
theorem pointwise_rare_arc_bound_strict_inside
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (x : E)
    (hx0 : 0 < ‖x‖) (hx1 : ‖x‖ < 1) :
    ‖x - radialClip 1 x‖ + ‖radialClip 1 x‖ ^ 2 <
      ‖x‖ * ‖radialClip 1 x‖ ^ (2 * (p - 1) / p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  rw [radialClip_of_norm_le hx1.le, sub_self, norm_zero, zero_add]
  have he : 1 + 2 * (p - 1) / p < 2 := by
    have hq : 2 * (p - 1) / p < 1 :=
      (div_lt_iff₀ hp0).2 (by nlinarith)
    linarith
  have hpow : ‖x‖ ^ (2 : ℝ) < ‖x‖ ^ (1 + 2 * (p - 1) / p) :=
    Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 he
  have hright : ‖x‖ * ‖x‖ ^ (2 * (p - 1) / p) =
      ‖x‖ ^ (1 + 2 * (p - 1) / p) := by
    rw [Real.rpow_add hx0, Real.rpow_one]
  rw [hright]
  simpa only [Real.rpow_two] using hpow

/-- At `p=2`, the pointwise bound is an identity at every radius. -/
theorem pointwise_rare_arc_bound_eq_p2 (x : E) :
    ‖x - radialClip 1 x‖ + ‖radialClip 1 x‖ ^ 2 =
      ‖x‖ * ‖radialClip 1 x‖ ^ (2 * ((2 : ℝ) - 1) / 2) := by
  norm_num
  by_cases hx : ‖x‖ ≤ 1
  · rw [radialClip_of_norm_le hx, sub_self, norm_zero]
    ring
  · have hxlt : 1 < ‖x‖ := lt_of_not_ge hx
    have hnorm : ‖radialClip 1 x‖ = 1 := by
      rw [norm_radialClip (by norm_num), min_eq_right hxlt.le]
    have hres : ‖x - radialClip 1 x‖ = ‖x‖ - 1 := by
      rw [norm_sub_radialClip (by norm_num), max_eq_left (by linarith)]
    rw [hnorm, hres]
    ring

/-- For `1 < p < 2`, equality occurs only at zero or at/above the clipping
radius, as asserted in the article's pointwise lemma. -/
theorem pointwise_rare_arc_bound_eq_iff
    {p : ℝ} (hp : 1 < p) (hp2 : p < 2) (x : E) :
    ‖x - radialClip 1 x‖ + ‖radialClip 1 x‖ ^ 2 =
        ‖x‖ * ‖radialClip 1 x‖ ^ (2 * (p - 1) / p) ↔
      x = 0 ∨ 1 ≤ ‖x‖ := by
  constructor
  · intro heq
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    right
    by_contra hx1
    have hinside : ‖x‖ < 1 := lt_of_not_ge hx1
    have hpositive : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hstrict := pointwise_rare_arc_bound_strict_inside hp hp2 x hpositive hinside
    linarith
  · rintro (hx0 | hx1)
    · subst x
      simp
    · by_cases hx : ‖x‖ = 1
      · have hclip : radialClip 1 x = x := radialClip_of_norm_le hx.le
        rw [hclip, sub_self, norm_zero, zero_add, hx]
        simp
      · have hxlt : 1 < ‖x‖ := lt_of_le_of_ne hx1 (Ne.symm hx)
        have hnorm : ‖radialClip 1 x‖ = 1 := by
          rw [norm_radialClip (by norm_num), min_eq_right hxlt.le]
        have hres : ‖x - radialClip 1 x‖ = ‖x‖ - 1 := by
          rw [norm_sub_radialClip (by norm_num), max_eq_left (by linarith)]
        rw [hnorm, hres]
        simp
