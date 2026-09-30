import SharpRadialClipping.Deterministic

/-!
# Sharp deterministic clipping envelope at `p = 1`

The article's Theorem 2.2 holds in every nontrivial real normed space.  The
upper bound holds without the nontriviality assumption; optimality tests
the radius-one vector and vectors of arbitrarily large radius on one ray.
-/

open Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For radial clipping, the residual and clipped vector split the input
norm exactly. -/
lemma norm_residual_add_norm_radialClip_p1
    {τ : ℝ} (hτ : 0 < τ) (x : E) :
    ‖x - radialClip τ x‖ + ‖radialClip τ x‖ = ‖x‖ := by
  rw [norm_sub_radialClip hτ, norm_radialClip hτ]
  by_cases h : ‖x‖ ≤ τ
  · rw [max_eq_right (sub_nonpos.mpr h), min_eq_left h]
    simp
  · have hτnorm : τ ≤ ‖x‖ := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left (sub_nonneg.mpr hτnorm), min_eq_right hτnorm]
    ring

/-- The clipped quadratic energy, divided by the threshold, never exceeds
the norm of the clipped vector. -/
lemma radialClip_energy_div_le_norm
    {τ : ℝ} (hτ : 0 < τ) (x : E) :
    ‖radialClip τ x‖ ^ 2 / τ ≤ ‖radialClip τ x‖ := by
  have hnorm : ‖radialClip τ x‖ ≤ τ := by
    rw [norm_radialClip hτ]
    exact min_le_right _ _
  have hnonneg : 0 ≤ ‖radialClip τ x‖ := norm_nonneg _
  apply (div_le_iff₀ hτ).2
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hnorm)]

/-- The sharp `p=1` inequality in every real normed space. -/
theorem radialClip_envelope_p1
    {α β τ : ℝ} (_hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (x : E) :
    α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
      ≤ max α β * ‖x‖ := by
  have hq := radialClip_energy_div_le_norm hτ x
  have hres : 0 ≤ ‖x - radialClip τ x‖ := norm_nonneg _
  have hclip : 0 ≤ ‖radialClip τ x‖ := norm_nonneg _
  have hMα : α ≤ max α β := le_max_left _ _
  have hMβ : β ≤ max α β := le_max_right _ _
  calc
    α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2 =
        α * ‖x - radialClip τ x‖ +
          β * (‖radialClip τ x‖ ^ 2 / τ) := by ring
    _ ≤ max α β * ‖x - radialClip τ x‖ +
          max α β * ‖radialClip τ x‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hMα hres
        · calc
            β * (‖radialClip τ x‖ ^ 2 / τ) ≤
                β * ‖radialClip τ x‖ := mul_le_mul_of_nonneg_left hq hβ
            _ ≤ max α β * ‖radialClip τ x‖ :=
              mul_le_mul_of_nonneg_right hMβ hclip
    _ = max α β * ‖x‖ := by
        rw [← mul_add, norm_residual_add_norm_radialClip_p1 hτ]

/-- Testing a proposed constant on a ray beyond the clipping threshold
gives the scalar outer-radius inequality. -/
lemma p1_outer_radius_test [Nontrivial E]
    {α β τ C r : ℝ} (hτ : 0 < τ) (hr : 1 ≤ r)
    (hC : ∀ x : E,
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
        ≤ C * ‖x‖) :
    α * (r - 1) + β ≤ C * r := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  let x : E := (r * τ) • e
  have hnorm : ‖x‖ = r * τ := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, he, mul_one,
      abs_of_nonneg (mul_nonneg (by linarith) hτ.le)]
  have hnormclip : ‖radialClip τ x‖ = τ := by
    rw [norm_radialClip hτ, hnorm, min_eq_right (by nlinarith)]
  have hnormres : ‖x - radialClip τ x‖ = (r - 1) * τ := by
    rw [norm_sub_radialClip hτ, hnorm,
      max_eq_left (by nlinarith : 0 ≤ r * τ - τ)]
    ring
  have hbound := hC x
  rw [hnormclip, hnormres, hnorm] at hbound
  have hfrac : (β / τ) * τ ^ 2 = β * τ := by
    field_simp [hτ.ne']
  rw [hfrac] at hbound
  have hscaled : (α * (r - 1) + β) * τ ≤ (C * r) * τ := by
    nlinarith [hbound]
  nlinarith [hscaled]

/-- The coefficient `max α β` is the smallest uniform constant for the
`p=1` deterministic inequality in a nontrivial normed space. -/
theorem max_alpha_beta_smallest_vector_constant_p1 [Nontrivial E]
    {α β τ C : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hτ : 0 < τ)
    (hC : ∀ x : E,
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
        ≤ C * ‖x‖) :
    max α β ≤ C := by
  have hβC : β ≤ C := by
    have htest := p1_outer_radius_test (E := E)
      (r := 1) hτ (by norm_num) hC
    norm_num at htest
    exact htest
  have hαC : α ≤ C := by
    by_contra hnot
    have hCα : C < α := lt_of_not_ge hnot
    have hαβ : β < α := lt_of_le_of_lt hβC hCα
    let δ : ℝ := α - C
    let b : ℝ := α - β
    have hδ : 0 < δ := sub_pos.mpr hCα
    have hb : 0 < b := sub_pos.mpr hαβ
    let r : ℝ := 1 + b / δ
    have hr : 1 ≤ r := by
      dsimp [r]
      exact le_add_of_nonneg_right (div_nonneg hb.le hδ.le)
    have htest := p1_outer_radius_test (E := E) (r := r) hτ hr hC
    have hrr : δ * r = δ + b := by
      dsimp [r]
      field_simp [hδ.ne']
    dsimp [δ, b] at hrr
    nlinarith [htest, hrr]
  exact max_le hαC hβC

/-- At the boundary exponent, the previously defined sharp constant reduces
to the larger of the two nonnegative weights. -/
theorem K_p_one_eq_max
    {α β : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β) :
    K_p α β 1 = max α β := by
  by_cases h : α ≤ β
  · simp [K_p, h]
  · have h' : β ≤ α := le_of_lt (lt_of_not_ge h)
    simp [K_p, h, c_p, max_eq_left h']

/-- The article's Theorem 2.2 upper estimate, in its original scaling. -/
theorem radialClip_envelope_p1_article
    {α β τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 < τ) (x : E) :
    α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
      ≤ K_p α β 1 * τ ^ (1 - (1 : ℝ)) * ‖x‖ ^ (1 : ℝ) := by
  rw [K_p_one_eq_max hα hβ]
  simpa only [sub_self, Real.rpow_zero, Real.rpow_one, mul_one] using
    radialClip_envelope_p1 hα hβ hτ x

/-- No constant below `K₁(α,β)=max α β` can satisfy the article's
deterministic inequality for all vectors in a nontrivial normed space. -/
theorem K_p_one_smallest_vector_constant [Nontrivial E]
    {α β τ C : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 < τ)
    (hC : ∀ x : E,
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
        ≤ C * τ ^ (1 - (1 : ℝ)) * ‖x‖ ^ (1 : ℝ)) :
    K_p α β 1 ≤ C := by
  rw [K_p_one_eq_max hα hβ]
  apply max_alpha_beta_smallest_vector_constant_p1 (E := E) hα hβ hτ
  intro x
  simpa only [sub_self, Real.rpow_zero, Real.rpow_one, mul_one] using hC x
