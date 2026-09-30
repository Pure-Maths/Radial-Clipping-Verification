import SharpRadialClipping.Stochastic
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Centered stochastic sharpness constructions

This module formalizes the finite two-point laws used to prove that the
stochastic constant cannot be improved.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open unitInterval

noncomputable section

/-- Normalized stochastic clipping objective. -/
def stochasticClippingRatio
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (μ : Measure Ω) (α β p τ : ℝ) (X : Ω → H) : ℝ :=
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let m : H := ∫ ω, X ω ∂μ
  let b : H := ∫ ω, Y ω ∂μ
  (α * ‖b - m‖
      + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)) /
    (τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ))

/-- The scalar ratio obtained from the rare two-point law after dividing
both numerator and denominator by the rare-event probability. -/
def rareReducedRatio (α β p R q : ℝ) : ℝ :=
  (α * (R - 1)
      + β * (1 + q * R ^ 2 / (1 - q) - q * (R - 1) ^ 2)) /
    (R ^ p + q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1))

/-- The rare-law ratio converges to the deterministic scalar objective at
radius `R` as the rare-event probability tends to zero from the right. -/
theorem tendsto_rareReducedRatio
    {α β p R : ℝ} (hp : 1 < p) (hR : 0 < R) :
    Filter.Tendsto (fun q => rareReducedRatio α β p R q)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 ((α * (R - 1) + β) / R ^ p)) := by
  have hq :
      Filter.Tendsto (fun q : ℝ => q)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hone :
      Filter.Tendsto (fun q : ℝ => 1 - q)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hq
  have hpowq0 :
      Filter.Tendsto (fun q : ℝ => q ^ (p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h :=
      (Real.continuous_rpow_const (sub_nonneg.mpr hp.le)).tendsto 0
    have hcomp := h.comp hq
    simpa only [Function.comp_def,
      Real.zero_rpow (sub_pos.mpr hp).ne'] using hcomp
  have hpowone :
      Filter.Tendsto (fun q : ℝ => (1 - q) ^ (p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    have h :=
      (Real.continuous_rpow_const (sub_nonneg.mpr hp.le)).tendsto 1
    simpa only [Function.comp_def, Real.one_rpow] using h.comp hone
  have hqR2 :
      Filter.Tendsto (fun q : ℝ => q * R ^ 2 / (1 - q))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h := (hq.mul_const (R ^ 2)).div hone one_ne_zero
    convert h using 1
    · funext q
      rfl
    · simp
  have hqdiff :
      Filter.Tendsto (fun q : ℝ => q * (R - 1) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa using hq.mul_const ((R - 1) ^ 2)
  have hnum :
      Filter.Tendsto
        (fun q : ℝ =>
          α * (R - 1)
            + β * (1 + q * R ^ 2 / (1 - q) - q * (R - 1) ^ 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 (α * (R - 1) + β)) := by
    have honeconst :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) :=
      tendsto_const_nhds
    have hβconst :
        Filter.Tendsto (fun _ : ℝ => β)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 β) :=
      tendsto_const_nhds
    have hαconst :
        Filter.Tendsto (fun _ : ℝ => α * (R - 1))
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (α * (R - 1))) :=
      tendsto_const_nhds
    have hinner := (honeconst.add hqR2).sub hqdiff
    have hscaled := hβconst.mul hinner
    have htotal := hαconst.add hscaled
    simpa only [add_zero, sub_zero, mul_one] using htotal
  have htail :
      Filter.Tendsto
        (fun q : ℝ => q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have h := (hpowq0.mul_const (R ^ p)).div hpowone one_ne_zero
    convert h using 1
    · funext q
      rw [Pi.div_apply, mul_comm]
    · simp
  have hden :
      Filter.Tendsto
        (fun q : ℝ =>
          R ^ p + q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (R ^ p)) := by
    simpa using tendsto_const_nhds.add htail
  exact hnum.div hden (Real.rpow_pos_of_pos hR p).ne'

/-- At the critical radius, the rare-law scalar limit is exactly the sharp
constant in the second regime. -/
theorem tendsto_rareReducedRatio_r_star
    {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    Filter.Tendsto
      (fun q => rareReducedRatio α β p (r_star α β p) q)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (K_p α β p)) := by
  have hlimit :=
    tendsto_rareReducedRatio (α := α) (β := β) hp
      (r_star_pos hβ hp hreg)
  have hvalue :
      (α * (r_star α β p - 1) + β) /
          (r_star α β p) ^ p =
        K_p α β p := by
    calc
      (α * (r_star α β p - 1) + β) /
            (r_star α β p) ^ p
          = F α β p (r_star α β p) :=
            (F_outer_formula (one_lt_r_star hβ hp hreg).le).symm
      _ = criticalValue α β p := F_at_r_star hβ hp hreg
      _ = K_p α β p := (K_p_eq_criticalValue hβ hp hreg).symm
  simpa only [hvalue] using hlimit

/-- Bernoulli law with rare-event probability `q`. -/
def rareBernoulli (q : I) : Measure Bool :=
  bernoulliMeasure true false q

instance (q : I) : IsProbabilityMeasure (rareBernoulli q) := by
  dsimp [rareBernoulli]
  infer_instance

/-- The centered rare two-point construction before clipping. -/
def rareTwoPoint {H : Type*} [SMul ℝ H]
    (R τ q : ℝ) (e : H) : Bool → H :=
  fun b =>
    if b then
      (R * τ) • e
    else
      (-(q * R * τ / (1 - q))) • e

@[simp]
lemma rareTwoPoint_true {H : Type*} [SMul ℝ H]
    (R τ q : ℝ) (e : H) :
    rareTwoPoint R τ q e true = (R * τ) • e := by
  simp [rareTwoPoint]

@[simp]
lemma rareTwoPoint_false {H : Type*} [SMul ℝ H]
    (R τ q : ℝ) (e : H) :
    rareTwoPoint R τ q e false =
      (-(q * R * τ / (1 - q))) • e := by
  simp [rareTwoPoint]

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

lemma rare_q_lt_one {q : I} {R : ℝ} (hR : 1 < R)
    (hq : (q : ℝ) < 1 / (1 + R)) :
    (q : ℝ) < 1 := by
  have hden : 0 < 1 + R := by linarith
  have hfrac : 1 / (1 + R) < 1 :=
    (div_lt_one hden).2 (by linarith)
  exact hq.trans hfrac

lemma rare_negative_radius_lt
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq : (q : ℝ) < 1 / (1 + R)) :
    (q : ℝ) * R * τ / (1 - (q : ℝ)) < τ := by
  have hdenR : 0 < 1 + R := by linarith
  have hqmul : (q : ℝ) * (1 + R) < 1 :=
    (lt_div_iff₀ hdenR).mp hq
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hdenq : 0 < 1 - (q : ℝ) := sub_pos.mpr hq1
  apply (div_lt_iff₀ hdenq).2
  have hqr : (q : ℝ) * R < 1 - (q : ℝ) := by
    nlinarith
  have := mul_lt_mul_of_pos_right hqr hτ
  nlinarith

lemma integral_rareTwoPoint
    {q : I} {R τ : ℝ} (hR : 1 < R)
    (hq : (q : ℝ) < 1 / (1 + R)) (e : H) :
    (∫ b, rareTwoPoint R τ (q : ℝ) e b ∂rareBernoulli q) = 0 := by
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hqne : 1 - (q : ℝ) ≠ 0 := (sub_pos.mpr hq1).ne'
  rw [rareBernoulli, integral_bernoulliMeasure]
  rw [rareTwoPoint_true, rareTwoPoint_false]
  simp only [smul_smul]
  rw [← add_smul]
  suffices
      (q : ℝ) * (R * τ)
          + (1 - (q : ℝ)) *
              (-((q : ℝ) * R * τ / (1 - (q : ℝ)))) = 0 by
    rw [this, zero_smul]
  field_simp
  ring

omit [CompleteSpace H] in
lemma norm_rareTwoPoint_true
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    {e : H} (he : ‖e‖ = 1) :
    ‖rareTwoPoint R τ (q : ℝ) e true‖ = R * τ := by
  simp only [rareTwoPoint, if_true]
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by linarith), abs_of_pos hτ]

omit [CompleteSpace H] in
lemma norm_rareTwoPoint_false
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    ‖rareTwoPoint R τ (q : ℝ) e false‖ =
      (q : ℝ) * R * τ / (1 - (q : ℝ)) := by
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hscalar : 0 < (q : ℝ) * R * τ / (1 - (q : ℝ)) := by
    positivity
  rw [rareTwoPoint_false]
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_pos hscalar]

omit [CompleteSpace H] in
lemma norm_rareTwoPoint_false_lt
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    ‖rareTwoPoint R τ (q : ℝ) e false‖ < τ := by
  rw [norm_rareTwoPoint_false hR hτ hq0 hq he]
  exact rare_negative_radius_lt hR hτ hq

omit [CompleteSpace H] in
lemma radialClip_rareTwoPoint_true
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    {e : H} (he : ‖e‖ = 1) :
    radialClip τ (rareTwoPoint R τ (q : ℝ) e true) = τ • e := by
  rw [radialClip]
  rw [norm_rareTwoPoint_true hR hτ he]
  rw [if_neg (not_le.mpr (by
    nlinarith [mul_lt_mul_of_pos_right hR hτ]))]
  simp only [rareTwoPoint, ↓reduceIte, smul_smul]
  congr 1
  field_simp [show R ≠ 0 by linarith, hτ.ne']

omit [CompleteSpace H] in
lemma radialClip_rareTwoPoint_false
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    radialClip τ (rareTwoPoint R τ (q : ℝ) e false) =
      rareTwoPoint R τ (q : ℝ) e false := by
  apply radialClip_of_norm_le
  rw [norm_rareTwoPoint_false hR hτ hq0 hq he]
  exact (rare_negative_radius_lt hR hτ hq).le

lemma integral_radialClip_rareTwoPoint
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    (∫ b, radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
      ∂rareBernoulli q) =
      (-(q : ℝ) * τ * (R - 1)) • e := by
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hqne : 1 - (q : ℝ) ≠ 0 := (sub_pos.mpr hq1).ne'
  rw [rareBernoulli, integral_bernoulliMeasure]
  rw [radialClip_rareTwoPoint_true hR hτ he,
    radialClip_rareTwoPoint_false hR hτ hq0 hq he]
  rw [rareTwoPoint_false]
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  field_simp
  ring

lemma norm_integral_radialClip_rareTwoPoint
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    ‖∫ b, radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
      ∂rareBernoulli q‖ =
      (q : ℝ) * τ * (R - 1) := by
  rw [integral_radialClip_rareTwoPoint hR hτ hq0 hq he]
  rw [norm_smul, he, mul_one, Real.norm_eq_abs]
  have hcoef : 0 < (q : ℝ) * τ * (R - 1) := by positivity
  have heq :
      (-(q : ℝ)) * τ * (R - 1) =
        -((q : ℝ) * τ * (R - 1)) := by ring
  rw [heq, abs_neg, abs_of_pos hcoef]

omit [CompleteSpace H] in
lemma integral_norm_radialClip_rareTwoPoint_sq
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    (∫ b, ‖radialClip τ (rareTwoPoint R τ (q : ℝ) e b)‖ ^ 2
      ∂rareBernoulli q) =
      (q : ℝ) * τ ^ 2 *
        (1 + (q : ℝ) * R ^ 2 / (1 - (q : ℝ))) := by
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hqne : 1 - (q : ℝ) ≠ 0 := (sub_pos.mpr hq1).ne'
  have htrue :
      ‖radialClip τ (rareTwoPoint R τ (q : ℝ) e true)‖ = τ := by
    rw [radialClip_rareTwoPoint_true hR hτ he, norm_smul, he,
      mul_one, Real.norm_eq_abs, abs_of_pos hτ]
  have hfalse :
      ‖radialClip τ (rareTwoPoint R τ (q : ℝ) e false)‖ =
        (q : ℝ) * R * τ / (1 - (q : ℝ)) := by
    rw [radialClip_rareTwoPoint_false hR hτ hq0 hq he,
      norm_rareTwoPoint_false hR hτ hq0 hq he]
  rw [rareBernoulli, integral_bernoulliMeasure, htrue, hfalse]
  simp only [smul_eq_mul]
  field_simp

lemma integral_centered_clipped_rareTwoPoint_sq
    {q : I} {R τ : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    (∫ b,
        ‖radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
            - ∫ z, radialClip τ (rareTwoPoint R τ (q : ℝ) e z)
                ∂rareBernoulli q‖ ^ 2
      ∂rareBernoulli q) =
      (q : ℝ) * τ ^ 2 *
        (1 + (q : ℝ) * R ^ 2 / (1 - (q : ℝ))
          - (q : ℝ) * (R - 1) ^ 2) := by
  let Y : Bool → H :=
    fun b => radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
  have hY : Integrable Y (rareBernoulli q) := by
    exact integrable_bernoulliMeasure true false q Y
  have hYsq : Integrable (fun b => ‖Y b‖ ^ 2)
      (rareBernoulli q) := by
    exact integrable_bernoulliMeasure true false q _
  calc
    (∫ b, ‖Y b - ∫ z, Y z ∂rareBernoulli q‖ ^ 2
      ∂rareBernoulli q)
        = (∫ b, ‖Y b‖ ^ 2 ∂rareBernoulli q)
            - ‖∫ z, Y z ∂rareBernoulli q‖ ^ 2 :=
          integral_norm_sub_mean_sq (rareBernoulli q) Y hY hYsq
    _ = (q : ℝ) * τ ^ 2 *
        (1 + (q : ℝ) * R ^ 2 / (1 - (q : ℝ))
          - (q : ℝ) * (R - 1) ^ 2) := by
      dsimp only [Y]
      rw [integral_norm_radialClip_rareTwoPoint_sq hR hτ hq0 hq he,
        norm_integral_radialClip_rareTwoPoint hR hτ hq0 hq he]
      ring

omit [CompleteSpace H] in
lemma integral_norm_rareTwoPoint_rpow
    {q : I} {R τ p : ℝ} (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    (∫ b, ‖rareTwoPoint R τ (q : ℝ) e b‖ ^ p
      ∂rareBernoulli q) =
      (q : ℝ) * τ ^ p *
        (R ^ p
          + (q : ℝ) ^ (p - 1) * R ^ p /
              (1 - (q : ℝ)) ^ (p - 1)) := by
  have hR0 : 0 < R := by linarith
  have hq1 : (q : ℝ) < 1 := rare_q_lt_one hR hq
  have hdenq : 0 < 1 - (q : ℝ) := sub_pos.mpr hq1
  rw [rareBernoulli, integral_bernoulliMeasure,
    norm_rareTwoPoint_true hR hτ he,
    norm_rareTwoPoint_false hR hτ hq0 hq he]
  simp only [smul_eq_mul]
  rw [Real.mul_rpow hR0.le hτ.le]
  rw [Real.div_rpow (by positivity) hdenq.le p]
  rw [Real.mul_rpow (by positivity : 0 ≤ (q : ℝ) * R) hτ.le]
  rw [Real.mul_rpow hq0.le hR0.le]
  rw [Real.rpow_sub_one hq0.ne' p,
    Real.rpow_sub_one hdenq.ne' p]
  field_simp [hq0.ne', hdenq.ne',
    (Real.rpow_pos_of_pos hdenq p).ne']

/-- The normalized stochastic objective of the actual centered Bernoulli
construction is exactly the reduced scalar ratio. -/
theorem normalized_rareTwoPoint_eq_rareReducedRatio
    {q : I} {α β p R τ : ℝ}
    (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    (α *
          ‖(∫ b, radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
                ∂rareBernoulli q)
              - (∫ b, rareTwoPoint R τ (q : ℝ) e b
                  ∂rareBernoulli q)‖
        + (β / τ) *
            (∫ b,
              ‖radialClip τ (rareTwoPoint R τ (q : ℝ) e b)
                  - ∫ z, radialClip τ
                      (rareTwoPoint R τ (q : ℝ) e z)
                      ∂rareBernoulli q‖ ^ 2
              ∂rareBernoulli q))
      /
        (τ ^ (1 - p) *
          (∫ b, ‖rareTwoPoint R τ (q : ℝ) e b‖ ^ p
            ∂rareBernoulli q))
      =
        rareReducedRatio α β p R (q : ℝ) := by
  let A : ℝ :=
    1 + (q : ℝ) * R ^ 2 / (1 - (q : ℝ))
      - (q : ℝ) * (R - 1) ^ 2
  let D : ℝ :=
    R ^ p
      + (q : ℝ) ^ (p - 1) * R ^ p /
          (1 - (q : ℝ)) ^ (p - 1)
  rw [integral_rareTwoPoint hR hq e, sub_zero,
    norm_integral_radialClip_rareTwoPoint hR hτ hq0 hq he,
    integral_centered_clipped_rareTwoPoint_sq hR hτ hq0 hq he,
    integral_norm_rareTwoPoint_rpow hR hτ hq0 hq he]
  change
    (α * ((q : ℝ) * τ * (R - 1))
        + β / τ * ((q : ℝ) * τ ^ 2 * A))
      / (τ ^ (1 - p) * ((q : ℝ) * τ ^ p * D))
      =
        (α * (R - 1) + β * A) / D
  have hnum :
      α * ((q : ℝ) * τ * (R - 1))
          + β / τ * ((q : ℝ) * τ ^ 2 * A)
        =
          (q : ℝ) * τ * (α * (R - 1) + β * A) := by
    field_simp [hτ.ne']
  have hτpow : τ ^ (1 - p) * τ ^ p = τ := by
    rw [← Real.rpow_add hτ]
    norm_num
  have hden :
      τ ^ (1 - p) * ((q : ℝ) * τ ^ p * D)
        = (q : ℝ) * τ * D := by
    calc
      τ ^ (1 - p) * ((q : ℝ) * τ ^ p * D)
          = (q : ℝ) * (τ ^ (1 - p) * τ ^ p) * D := by ring
      _ = (q : ℝ) * τ * D := by rw [hτpow]
  rw [hnum, hden]
  have hqτ : (q : ℝ) * τ ≠ 0 := mul_ne_zero hq0.ne' hτ.ne'
  field_simp [hqτ]

/-- The preceding exact calculation in terms of the named stochastic
ratio. -/
lemma stochasticClippingRatio_rareTwoPoint_eq
    {q : I} {α β p R τ : ℝ}
    (hR : 1 < R) (hτ : 0 < τ)
    (hq0 : 0 < (q : ℝ)) (hq : (q : ℝ) < 1 / (1 + R))
    {e : H} (he : ‖e‖ = 1) :
    stochasticClippingRatio (rareBernoulli q) α β p τ
        (rareTwoPoint R τ (q : ℝ) e)
      = rareReducedRatio α β p R (q : ℝ) := by
  simpa only [stochasticClippingRatio] using
    normalized_rareTwoPoint_eq_rareReducedRatio
      hR hτ hq0 hq he

/-- In the second regime, actual centered two-point laws approach the sharp
constant arbitrarily closely. -/
theorem exists_rare_twoPoint_epsilon_optimal_second_regime
    [Nontrivial H] {α β p τ ε : ℝ}
    (hβ : 0 ≤ β) (hp : 1 < p) (hreg : p * β < α)
    (hτ : 0 < τ) (hε : 0 < ε) :
    ∃ q : I,
      0 < (q : ℝ) ∧
      (q : ℝ) < 1 / (1 + r_star α β p) ∧
      ∃ X : Bool → H,
        (∫ b, X b ∂rareBernoulli q) = 0 ∧
        0 < ∫ b, ‖X b‖ ^ p ∂rareBernoulli q ∧
        K_p α β p - ε <
          stochasticClippingRatio (rareBernoulli q) α β p τ X := by
  let R : ℝ := r_star α β p
  have hR : 1 < R := one_lt_r_star hβ hp hreg
  have hbound : 0 < 1 / (1 + R) := by positivity
  have hlim :
      Filter.Tendsto (fun q => rareReducedRatio α β p R q)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (K_p α β p)) := by
    simpa only [R] using
      tendsto_rareReducedRatio_r_star hβ hp hreg
  have hnear :
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        K_p α β p - ε < rareReducedRatio α β p R q :=
    hlim.eventually (Ioi_mem_nhds (sub_lt_self _ hε))
  have hupper :
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0), q < 1 / (1 + R) :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds hbound)
  have hev :
      ∀ᶠ q in nhdsWithin 0 (Set.Ioi 0),
        0 < q ∧ q < 1 / (1 + R) ∧
          K_p α β p - ε < rareReducedRatio α β p R q := by
    filter_upwards [eventually_mem_nhdsWithin, hupper, hnear] with
      q hq0 hqupper hqnear
    exact ⟨hq0, hqupper, hqnear⟩
  obtain ⟨q, hq0, hqupper, hqnear⟩ := hev.exists
  have hq1 : q < 1 := by
    have hden : 0 < 1 + R := by linarith
    have hfrac : 1 / (1 + R) < 1 :=
      (div_lt_one hden).2 (by linarith)
    exact hqupper.trans hfrac
  let qI : I := ⟨q, hq0.le, hq1.le⟩
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let X : Bool → H := rareTwoPoint R τ q e
  have hcenter : (∫ b, X b ∂rareBernoulli qI) = 0 := by
    dsimp only [X, qI]
    exact integral_rareTwoPoint hR hqupper e
  have hmoment :
      0 < ∫ b, ‖X b‖ ^ p ∂rareBernoulli qI := by
    dsimp only [X, qI]
    rw [integral_norm_rareTwoPoint_rpow hR hτ hq0 hqupper he]
    have hdenq : 0 < 1 - q := sub_pos.mpr hq1
    have htail :
        0 ≤ q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1) :=
      div_nonneg
        (mul_nonneg (Real.rpow_nonneg hq0.le (p - 1))
          (Real.rpow_nonneg (zero_lt_one.trans hR).le p))
        (Real.rpow_nonneg hdenq.le (p - 1))
    have hD :
        0 < R ^ p +
          q ^ (p - 1) * R ^ p / (1 - q) ^ (p - 1) :=
      add_pos_of_pos_of_nonneg
        (Real.rpow_pos_of_pos (zero_lt_one.trans hR) p) htail
    exact mul_pos (mul_pos hq0 (Real.rpow_pos_of_pos hτ p)) hD
  refine ⟨qI, hq0, ?_, X, hcenter, hmoment, ?_⟩
  · exact hqupper
  · rw [stochasticClippingRatio_rareTwoPoint_eq hR hτ hq0 hqupper he]
    exact hqnear

/-- The probability `1/2` as a point of the unit interval. -/
def halfUnit : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- The symmetric Bernoulli probability measure. -/
def symmetricBernoulli : Measure Bool :=
  bernoulliMeasure true false halfUnit

instance : IsProbabilityMeasure symmetricBernoulli := by
  dsimp [symmetricBernoulli]
  infer_instance

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The symmetric law supported at `± τ e`. -/
def symmetricTwoPoint (τ : ℝ) (e : H) : Bool → H :=
  fun b => if b then τ • e else (-τ) • e

lemma integral_symmetricTwoPoint (τ : ℝ) (e : H) :
    (∫ b, symmetricTwoPoint τ e b ∂symmetricBernoulli) = 0 := by
  rw [symmetricBernoulli, integral_bernoulliMeasure]
  simp [symmetricTwoPoint, halfUnit]
  module

omit [CompleteSpace H] in
lemma norm_symmetricTwoPoint {τ : ℝ} (hτ : 0 ≤ τ)
    {e : H} (he : ‖e‖ = 1) (b : Bool) :
    ‖symmetricTwoPoint τ e b‖ = τ := by
  cases b <;> simp [symmetricTwoPoint, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hτ, he]

omit [CompleteSpace H] in
lemma radialClip_symmetricTwoPoint {τ : ℝ} (hτ : 0 < τ)
    {e : H} (he : ‖e‖ = 1) (b : Bool) :
    radialClip τ (symmetricTwoPoint τ e b) = symmetricTwoPoint τ e b := by
  apply radialClip_of_norm_le
  rw [norm_symmetricTwoPoint hτ.le he]

lemma integral_radialClip_symmetricTwoPoint {τ : ℝ} (hτ : 0 < τ)
    {e : H} (he : ‖e‖ = 1) :
    (∫ b, radialClip τ (symmetricTwoPoint τ e b) ∂symmetricBernoulli) = 0 := by
  calc
    (∫ b, radialClip τ (symmetricTwoPoint τ e b) ∂symmetricBernoulli)
        = ∫ b, symmetricTwoPoint τ e b ∂symmetricBernoulli := by
          apply integral_congr_ae
          filter_upwards with b
          rw [radialClip_symmetricTwoPoint hτ he b]
    _ = 0 := integral_symmetricTwoPoint τ e

omit [CompleteSpace H] in
lemma integral_norm_symmetricTwoPoint_rpow {τ p : ℝ} (hτ : 0 < τ)
    {e : H} (he : ‖e‖ = 1) :
    (∫ b, ‖symmetricTwoPoint τ e b‖ ^ p ∂symmetricBernoulli) = τ ^ p := by
  rw [symmetricBernoulli, integral_bernoulliMeasure]
  rw [norm_symmetricTwoPoint hτ.le he true,
    norm_symmetricTwoPoint hτ.le he false]
  simp [halfUnit]
  ring

lemma integral_centered_clipped_symmetricTwoPoint_sq
    {τ : ℝ} (hτ : 0 < τ) {e : H} (he : ‖e‖ = 1) :
    (∫ b,
        ‖radialClip τ (symmetricTwoPoint τ e b)
            - ∫ z, radialClip τ (symmetricTwoPoint τ e z)
                ∂symmetricBernoulli‖ ^ 2
      ∂symmetricBernoulli) = τ ^ 2 := by
  rw [integral_radialClip_symmetricTwoPoint hτ he]
  rw [symmetricBernoulli, integral_bernoulliMeasure]
  simp only [sub_zero]
  rw [radialClip_symmetricTwoPoint hτ he true,
    radialClip_symmetricTwoPoint hτ he false,
    norm_symmetricTwoPoint hτ.le he true,
    norm_symmetricTwoPoint hτ.le he false]
  simp [halfUnit, smul_eq_mul]
  ring

/-- In the first regime, a centered symmetric two-point law attains the
stochastic envelope exactly. -/
theorem symmetric_twoPoint_attains_first_regime
    [Nontrivial H] {α β p τ : ℝ}
    (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (_hp : 1 < p)
    (hreg : α ≤ p * β) (hτ : 0 < τ) :
    ∃ X : Bool → H,
      (∫ b, X b ∂symmetricBernoulli) = 0 ∧
      0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli ∧
      α * ‖(∫ b, radialClip τ (X b) ∂symmetricBernoulli)
            - (∫ b, X b ∂symmetricBernoulli)‖
          + (β / τ) *
              (∫ b,
                ‖radialClip τ (X b)
                    - ∫ z, radialClip τ (X z) ∂symmetricBernoulli‖ ^ 2
                ∂symmetricBernoulli)
        =
          K_p α β p * τ ^ (1 - p) *
            (∫ b, ‖X b‖ ^ p ∂symmetricBernoulli) := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  refine ⟨symmetricTwoPoint τ e, integral_symmetricTwoPoint τ e, ?_, ?_⟩
  · rw [integral_norm_symmetricTwoPoint_rpow hτ he]
    exact Real.rpow_pos_of_pos hτ p
  · rw [integral_centered_clipped_symmetricTwoPoint_sq hτ he,
      integral_norm_symmetricTwoPoint_rpow hτ he,
      integral_symmetricTwoPoint, integral_radialClip_symmetricTwoPoint hτ he]
    rw [K_p, if_pos hreg]
    have hpow : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    rw [mul_assoc, hpow]
    field_simp
    simp

/-- Every admissible `L^p` random vector has normalized stochastic objective
at most the sharp constant. -/
theorem stochasticClippingRatio_le_K_p_of_memLp
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (X : Ω → H)
    (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hmoment : 0 < ∫ ω, ‖X ω‖ ^ p ∂μ) :
    stochasticClippingRatio μ α β p τ X ≤ K_p α β p := by
  have henv :=
    stochastic_radialClip_envelope_of_memLp
      μ hα hβ hp hp2 hτ X hLp
  have hden :
      0 < τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ) :=
    mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) hmoment
  dsimp only [stochasticClippingRatio] at ⊢
  apply (div_le_iff₀ hden).2
  simpa only [mul_assoc] using henv

/-- In the first regime, the normalized objective of an actual centered
symmetric two-point law is exactly `K_p`. -/
theorem exists_symmetric_twoPoint_ratio_eq_K_p
    [Nontrivial H] {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : α ≤ p * β) (hτ : 0 < τ) :
    ∃ X : Bool → H,
      (∫ b, X b ∂symmetricBernoulli) = 0 ∧
      0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli ∧
      stochasticClippingRatio symmetricBernoulli α β p τ X =
        K_p α β p := by
  obtain ⟨X, hcenter, hmoment, heq⟩ :=
    symmetric_twoPoint_attains_first_regime
      (H := H) hα hβ hp hreg hτ
  refine ⟨X, hcenter, hmoment, ?_⟩
  have hden :
      0 < τ ^ (1 - p) *
          (∫ b, ‖X b‖ ^ p ∂symmetricBernoulli) :=
    mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) hmoment
  dsimp only [stochasticClippingRatio]
  rw [heq]
  apply (div_eq_iff hden.ne').2
  ring

/-- `K_p` is the smallest constant that can bound all centered laws.  It
already suffices to test probability measures on the two-point space `Bool`.
Together with `stochasticClippingRatio_le_K_p_of_memLp`, this is the exact
centered stochastic constant statement. -/
theorem K_p_le_of_bound_on_all_centered_bool_laws
    [Nontrivial H] {α β p τ C : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (_hp2 : p ≤ 2)
    (hτ : 0 < τ)
    (hC :
      ∀ (μ : Measure Bool) [IsProbabilityMeasure μ] (X : Bool → H),
        MemLp X (ENNReal.ofReal p) μ →
        (∫ b, X b ∂μ) = 0 →
        0 < ∫ b, ‖X b‖ ^ p ∂μ →
        stochasticClippingRatio μ α β p τ X ≤ C) :
    K_p α β p ≤ C := by
  by_cases hreg : α ≤ p * β
  · obtain ⟨X, hcenter, hmoment, hratio⟩ :=
      exists_symmetric_twoPoint_ratio_eq_K_p
        (H := H) hα hβ hp hreg hτ
    have hLp : MemLp X (ENNReal.ofReal p) symmetricBernoulli :=
      MemLp.of_discrete
    have hbound := hC symmetricBernoulli X hLp hcenter hmoment
    simpa only [hratio] using hbound
  · have hsecond : p * β < α := lt_of_not_ge hreg
    by_contra hnot
    have hCK : C < K_p α β p := lt_of_not_ge hnot
    let ε : ℝ := (K_p α β p - C) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith
    obtain ⟨q, hq0, hqbound, X, hcenter, hmoment, hnear⟩ :=
      exists_rare_twoPoint_epsilon_optimal_second_regime
        (H := H) hβ hp hsecond hτ hε
    have hLp : MemLp X (ENNReal.ofReal p) (rareBernoulli q) :=
      MemLp.of_discrete
    have hbound := hC (rareBernoulli q) X hLp hcenter hmoment
    dsimp only [ε] at hnear
    linarith

/-- The set of normalized objectives of all admissible centered laws on the
two-point measurable space.  These laws already determine the global sharp
constant. -/
def centeredBoolStochasticRatios
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α β p τ : ℝ) : Set ℝ :=
  {v | ∃ (μ : Measure Bool) (_hμ : IsProbabilityMeasure μ)
      (X : Bool → H),
      MemLp X (ENNReal.ofReal p) μ ∧
      (∫ b, X b ∂μ) = 0 ∧
      0 < ∫ b, ‖X b‖ ^ p ∂μ ∧
      v = stochasticClippingRatio μ α β p τ X}

/-- Literal supremum packaging of the exact centered constant.  Since the
upper bound holds on arbitrary probability spaces and the two-point laws
already have supremum `K_p`, this is equivalent to the article's global
supremum statement. -/
theorem sSup_centeredBoolStochasticRatios_eq_K_p
    [Nontrivial H] {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) :
    sSup (centeredBoolStochasticRatios H α β p τ) = K_p α β p := by
  have hnonempty :
      (centeredBoolStochasticRatios H α β p τ).Nonempty := by
    obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
    let X : Bool → H := symmetricTwoPoint τ e
    have hcenter : (∫ b, X b ∂symmetricBernoulli) = 0 := by
      dsimp only [X]
      exact integral_symmetricTwoPoint τ e
    have hmoment :
        0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli := by
      dsimp only [X]
      rw [integral_norm_symmetricTwoPoint_rpow hτ he]
      exact Real.rpow_pos_of_pos hτ p
    refine ⟨stochasticClippingRatio symmetricBernoulli α β p τ X,
      symmetricBernoulli, inferInstance, X, MemLp.of_discrete,
      hcenter, hmoment, rfl⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt hnonempty
  · intro v hv
    rcases hv with ⟨μ, hμ, X, hLp, hcenter, hmoment, rfl⟩
    letI : IsProbabilityMeasure μ := hμ
    exact stochasticClippingRatio_le_K_p_of_memLp
      μ hα hβ hp hp2 hτ X hLp hmoment
  · intro a ha
    by_cases hreg : α ≤ p * β
    · obtain ⟨X, hcenter, hmoment, hratio⟩ :=
        exists_symmetric_twoPoint_ratio_eq_K_p
          (H := H) hα hβ hp hreg hτ
      have hLp : MemLp X (ENNReal.ofReal p) symmetricBernoulli :=
        MemLp.of_discrete
      refine ⟨K_p α β p, ?_, ha⟩
      exact ⟨symmetricBernoulli, inferInstance, X, hLp,
        hcenter, hmoment, hratio.symm⟩
    · have hsecond : p * β < α := lt_of_not_ge hreg
      have hε : 0 < K_p α β p - a := sub_pos.mpr ha
      obtain ⟨q, hq0, hqbound, X, hcenter, hmoment, hnear⟩ :=
        exists_rare_twoPoint_epsilon_optimal_second_regime
          (H := H) hβ hp hsecond hτ hε
      have hLp : MemLp X (ENNReal.ofReal p) (rareBernoulli q) :=
        MemLp.of_discrete
      refine ⟨stochasticClippingRatio (rareBernoulli q) α β p τ X,
        ?_, ?_⟩
      · exact ⟨rareBernoulli q, inferInstance, X, hLp,
          hcenter, hmoment, rfl⟩
      · simpa only [sub_sub_cancel] using hnear

/-- Equality in the deterministic envelope in the second regime forces every
nonzero vector to lie on the unique maximizing sphere. -/
lemma pointwise_eq_implies_norm_eq_rstar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α β p τ : ℝ} (_hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hreg : p * β < α)
    (hτ : 0 < τ) {x : E} (hx0 : x ≠ 0)
    (heq :
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2 =
        K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p) :
    ‖x‖ = r_star α β p * τ := by
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let r : ℝ := ‖x‖ / τ
  have hr : 0 < r := div_pos hx hτ
  have hnorm : ‖x‖ = τ * r := by
    dsimp [r]
    field_simp
  have hmax :
      max (‖x‖ - τ) 0 = τ * max (r - 1) 0 := by
    calc
      max (‖x‖ - τ) 0 = max (τ * (r - 1)) (τ * 0) := by
        rw [hnorm]
        congr 1 <;> ring
      _ = τ * max (r - 1) 0 :=
        (mul_max_of_nonneg (r - 1) 0 hτ.le).symm
  have hmin :
      min ‖x‖ τ = τ * min r 1 := by
    calc
      min ‖x‖ τ = min (τ * r) (τ * 1) := by rw [hnorm, mul_one]
      _ = τ * min r 1 := (mul_min_of_nonneg r 1 hτ.le).symm
  have hpowτ : τ ^ (1 - p) * τ ^ p = τ := by
    rw [← Real.rpow_add hτ]
    norm_num
  have hleft :
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2 =
        τ * (α * max (r - 1) 0 + β * (min r 1) ^ 2) := by
    rw [norm_sub_radialClip hτ, norm_radialClip hτ, hmax, hmin]
    field_simp
  have hright :
      K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p =
        τ * (K_p α β p * r ^ p) := by
    rw [hnorm, Real.mul_rpow hτ.le hr.le]
    calc
      K_p α β p * τ ^ (1 - p) * (τ ^ p * r ^ p) =
          (τ ^ (1 - p) * τ ^ p) * (K_p α β p * r ^ p) := by ring
      _ = τ * (K_p α β p * r ^ p) := by rw [hpowτ]
  rw [hleft, hright] at heq
  have hnum :
      α * max (r - 1) 0 + β * (min r 1) ^ 2 = K_p α β p * r ^ p := by
    exact mul_left_cancel₀ hτ.ne' heq
  have hF : F α β p r = K_p α β p := by
    rw [F]
    exact (div_eq_iff (Real.rpow_pos_of_pos hr p).ne').2 hnum
  have hrstar := maximizing_radius_second_regime hβ hp hp2 hreg hr hF
  rw [hnorm, hrstar]
  ring

/-- In the second regime with positive energy weight, the sharp stochastic
constant is a strict supremum even without a centering assumption. -/
theorem stochasticClippingRatio_lt_K_p_second_regime_of_pos_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβpos : 0 < β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hreg : p * β < α) (hτ : 0 < τ) (X : Ω → H)
    (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hmoment : 0 < ∫ ω, ‖X ω‖ ^ p ∂μ) :
    stochasticClippingRatio μ α β p τ X < K_p α β p := by
  have hβ : 0 ≤ β := hβpos.le
  have hle :=
    stochasticClippingRatio_le_K_p_of_memLp
      μ hα hβ hp hp2 hτ X hLp hmoment
  apply lt_of_le_of_ne hle
  intro hratio
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let m : H := ∫ ω, X ω ∂μ
  let b : H := ∫ ω, Y ω ∂μ
  let D : ℝ := τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ)
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) hmoment
  have hAeq :
      α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ) =
        K_p α β p * D := by
    have hratio' :
        (α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)) / D =
          K_p α β p := by
      simpa only [stochasticClippingRatio, Y, m, b, D] using hratio
    exact (div_eq_iff hD.ne').mp hratio'
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hY : Integrable Y μ := by
    dsimp only [Y]
    exact integrable_radialClip hLp.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ := by
    dsimp only [Y]
    exact integrable_sq_norm_radialClip hLp.1 hτ
  have hXp0 := hLp.integrable_norm_rpow'
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hXp0
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ :=
    (hX.sub hY).norm
  have hbias :
      ‖b - m‖ ≤ ∫ ω, ‖X ω - Y ω‖ ∂μ := by
    calc
      ‖b - m‖ = ‖∫ ω, Y ω - X ω ∂μ‖ := by
        rw [integral_sub hY hX]
      _ ≤ ∫ ω, ‖Y ω - X ω‖ ∂μ :=
        norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω - Y ω‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => norm_sub_rev _ _
  have hvar :
      (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ) =
        (∫ ω, ‖Y ω‖ ^ 2 ∂μ) - ‖b‖ ^ 2 := by
    exact integral_norm_sub_mean_sq μ Y hY hYsq
  have hAleB :
      α * ‖b - m‖ + (β / τ) * (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ) ≤
        α * (∫ ω, ‖X ω - Y ω‖ ∂μ) +
          (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) := by
    rw [hvar]
    have hβτ : 0 ≤ β / τ := div_nonneg hβ hτ.le
    nlinarith [sq_nonneg ‖b‖]
  have hB_le :
      α * (∫ ω, ‖X ω - Y ω‖ ∂μ) +
          (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) ≤
        K_p α β p * D := by
    have hint :=
      integrated_radialClip_envelope μ hα hβ hp hp2 hτ X hLp.1 hXp
    rw [integral_add (hres.const_mul α) (hYsq.const_mul (β / τ)),
      integral_const_mul, integral_const_mul] at hint
    simpa only [Y, D, mul_assoc] using hint
  have hBeq :
      α * (∫ ω, ‖X ω - Y ω‖ ∂μ) +
          (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) =
        K_p α β p * D := by
    linarith
  let L : Ω → ℝ := fun ω =>
    α * ‖X ω - Y ω‖ + (β / τ) * ‖Y ω‖ ^ 2
  let R : Ω → ℝ := fun ω =>
    (K_p α β p * τ ^ (1 - p)) * ‖X ω‖ ^ p
  have hLint : Integrable L μ := by
    exact (hres.const_mul α).add (hYsq.const_mul (β / τ))
  have hRint : Integrable R μ := by
    exact hXp.const_mul (K_p α β p * τ ^ (1 - p))
  have hLR : L ≤ᵐ[μ] R := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp only [L, R, Y]
      simpa only [mul_assoc] using
        radialClip_envelope hα hβ hp hp2 hτ (X ω)
  have hintEq : (∫ ω, L ω ∂μ) = ∫ ω, R ω ∂μ := by
    rw [show (∫ ω, L ω ∂μ) =
        α * (∫ ω, ‖X ω - Y ω‖ ∂μ) +
          (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) by
      dsimp only [L]
      rw [integral_add (hres.const_mul α) (hYsq.const_mul (β / τ)),
        integral_const_mul, integral_const_mul]]
    rw [show (∫ ω, R ω ∂μ) =
        (K_p α β p * τ ^ (1 - p)) *
          (∫ ω, ‖X ω‖ ^ p ∂μ) by
      dsimp only [R]
      rw [integral_const_mul]]
    simpa only [D, mul_assoc] using hBeq
  have hpointEq : L =ᵐ[μ] R :=
    (integral_eq_iff_of_ae_le hLint hRint hLR).mp hintEq
  have hsphere :
      ∀ᵐ ω ∂μ, X ω = 0 ∨ ‖X ω‖ = r_star α β p * τ := by
    filter_upwards [hpointEq] with ω hω
    by_cases hxω : X ω = 0
    · exact Or.inl hxω
    · exact Or.inr (pointwise_eq_implies_norm_eq_rstar
        hα hβ hp hp2 hreg hτ hxω (by
          dsimp only [L, R, Y] at hω
          simpa only [mul_assoc] using hω))
  have hRstar : 0 < r_star α β p := r_star_pos hβ hp hreg
  have hRstar1 : 1 < r_star α β p := one_lt_r_star hβ hp hreg
  have hclip :
      Y =ᵐ[μ] (fun ω => ((r_star α β p)⁻¹ : ℝ) • X ω) := by
    filter_upwards [hsphere] with ω hω
    rcases hω with hx0 | hxnorm
    · simp [Y, hx0, radialClip_zero hτ.le]
    · have hlt : τ < ‖X ω‖ := by rw [hxnorm]; nlinarith
      dsimp only [Y]
      rw [radialClip_of_lt_norm hlt, hxnorm]
      congr 1
      field_simp [hτ.ne', hRstar.ne']
  have hbformula : b = ((r_star α β p)⁻¹ : ℝ) • m := by
    calc
      b = ∫ ω, ((r_star α β p)⁻¹ : ℝ) • X ω ∂μ :=
        integral_congr_ae hclip
      _ = ((r_star α β p)⁻¹ : ℝ) • (∫ ω, X ω ∂μ) := by
        rw [integral_smul]
      _ = ((r_star α β p)⁻¹ : ℝ) • m := by rfl
  have hbzero : b = 0 := by
    have hgap :
        α * ((∫ ω, ‖X ω - Y ω‖ ∂μ) - ‖b - m‖) +
          (β / τ) * ‖b‖ ^ 2 = 0 := by
      rw [hvar] at hAeq
      nlinarith [hAeq, hBeq]
    have hnormgap : 0 ≤ (∫ ω, ‖X ω - Y ω‖ ∂μ) - ‖b - m‖ :=
      sub_nonneg.mpr hbias
    have hbsq : 0 ≤ ‖b‖ ^ 2 := sq_nonneg ‖b‖
    have hbsqzero : ‖b‖ ^ 2 = 0 := by
      have hcoef : 0 < β / τ := div_pos hβpos hτ
      nlinarith [hgap, mul_nonneg hα hnormgap]
    have hbnorm : ‖b‖ = 0 := by nlinarith [norm_nonneg b]
    exact norm_eq_zero.mp hbnorm
  have hmzero : m = 0 := by
    calc
      m = (r_star α β p) • (((r_star α β p)⁻¹ : ℝ) • m) := by
        rw [smul_smul, mul_inv_cancel₀ hRstar.ne', one_smul]
      _ = (r_star α β p) • b := by rw [← hbformula]
      _ = 0 := by rw [hbzero, smul_zero]
  have hAeq0 :
      (β / τ) * (∫ ω, ‖Y ω‖ ^ 2 ∂μ) = K_p α β p * D := by
    rw [hvar] at hAeq
    simpa only [hbzero, hmzero, norm_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by norm_num), sub_zero,
      mul_zero, zero_add, sub_zero, norm_zero] using hAeq
  have hreszero :
      ∫ ω, ‖X ω - Y ω‖ ∂μ = 0 := by
    have hαpos : 0 < α := by
      have : 0 ≤ p * β := mul_nonneg hp0 hβ
      linarith
    nlinarith [hBeq, hAeq0]
  have hresae :
      (fun ω => ‖X ω - Y ω‖) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hres).mp hreszero
  have hXzero : X =ᵐ[μ] 0 := by
    filter_upwards [hresae, hsphere] with ω hresω hsphereω
    rcases hsphereω with hx0 | hxnorm
    · exact hx0
    · exfalso
      have hXY : X ω = Y ω := by
        have : X ω - Y ω = 0 := norm_eq_zero.mp hresω
        exact sub_eq_zero.mp this
      have hynorm : ‖Y ω‖ = τ := by
        dsimp only [Y]
        rw [norm_radialClip hτ, min_eq_right (le_of_lt (by
          rw [hxnorm]
          nlinarith))]
      have : ‖X ω‖ = τ := by rw [hXY, hynorm]
      rw [hxnorm] at this
      nlinarith
  have hmomentzero : (∫ ω, ‖X ω‖ ^ p ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hXzero] with ω hω
    change X ω = 0 at hω
    simp [hω, Real.zero_rpow (ne_of_gt (zero_lt_one.trans hp))]
  linarith

/-- Centered strict nonattainment in the full nonnegative-weight regime.  For
positive energy weight this follows from the stronger uncentered theorem;
the zero-energy endpoint is handled by its equality case. -/
theorem stochasticClippingRatio_lt_K_p_second_regime
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hreg : p * β < α) (hτ : 0 < τ) (X : Ω → H)
    (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hcenter : (∫ ω, X ω ∂μ) = 0)
    (hmoment : 0 < ∫ ω, ‖X ω‖ ^ p ∂μ) :
    stochasticClippingRatio μ α β p τ X < K_p α β p := by
  by_cases hβpos : 0 < β
  · exact stochasticClippingRatio_lt_K_p_second_regime_of_pos_energy
      μ hα hβpos hp hp2 hreg hτ X hLp hmoment
  have hβzero : β = 0 := le_antisymm (le_of_not_gt hβpos) hβ
  have hle := stochasticClippingRatio_le_K_p_of_memLp
    μ hα hβ hp hp2 hτ X hLp hmoment
  apply lt_of_le_of_ne hle
  intro hratio
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let b : H := ∫ ω, Y ω ∂μ
  let D : ℝ := τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ)
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) hmoment
  have hAeq : α * ‖b‖ = K_p α β p * D := by
    have hratio' :
        (α * ‖b‖ + (β / τ) *
          (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ)) / D = K_p α β p := by
      simpa only [stochasticClippingRatio, Y, b, D, hcenter, sub_zero] using hratio
    rw [hβzero, zero_div, zero_mul, add_zero] at hratio'
    have hAeq0 : α * ‖b‖ = K_p α 0 p * D :=
      (div_eq_iff hD.ne').mp hratio'
    simpa [hβzero] using hAeq0
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hY : Integrable Y μ := by
    dsimp only [Y]
    exact integrable_radialClip hLp.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ := by
    dsimp only [Y]
    exact integrable_sq_norm_radialClip hLp.1 hτ
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  have hXp0 := hLp.integrable_norm_rpow'
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hXp0
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ := (hX.sub hY).norm
  have hbias : ‖b‖ ≤ ∫ ω, ‖X ω - Y ω‖ ∂μ := by
    calc
      ‖b‖ = ‖∫ ω, Y ω - X ω ∂μ‖ := by
        rw [integral_sub hY hX, hcenter, sub_zero]
      _ ≤ ∫ ω, ‖Y ω - X ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω - Y ω‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => norm_sub_rev _ _
  have hBeq : α * (∫ ω, ‖X ω - Y ω‖ ∂μ) = K_p α β p * D := by
    have hBbound : α * (∫ ω, ‖X ω - Y ω‖ ∂μ) ≤ K_p α β p * D := by
      have hint := integrated_radialClip_envelope μ hα hβ hp hp2 hτ X hLp.1 hXp
      simpa only [integral_const_mul, hβzero, zero_div, zero_mul, add_zero,
        D, mul_assoc] using hint
    have hαpos : 0 < α := by
      have : 0 ≤ p * β := mul_nonneg hp0 hβ
      linarith
    nlinarith
  let L : Ω → ℝ := fun ω => α * ‖X ω - Y ω‖
  let R : Ω → ℝ := fun ω =>
    (K_p α β p * τ ^ (1 - p)) * ‖X ω‖ ^ p
  have hLint : Integrable L μ := hres.const_mul α
  have hRint : Integrable R μ := hXp.const_mul (K_p α β p * τ ^ (1 - p))
  have hLR : L ≤ᵐ[μ] R := by
    filter_upwards with ω
    dsimp only [L, R, Y]
    simpa only [hβzero, zero_div, zero_mul, add_zero, mul_assoc] using
      (radialClip_envelope hα hβ hp hp2 hτ (X ω))
  have hintEq : (∫ ω, L ω ∂μ) = ∫ ω, R ω ∂μ := by
    rw [show (∫ ω, L ω ∂μ) = α * (∫ ω, ‖X ω - Y ω‖ ∂μ) by
      dsimp only [L]
      rw [integral_const_mul]]
    rw [show (∫ ω, R ω ∂μ) =
      (K_p α β p * τ ^ (1 - p)) * (∫ ω, ‖X ω‖ ^ p ∂μ) by
      dsimp only [R]
      rw [integral_const_mul]]
    simpa only [D, mul_assoc] using hBeq
  have hpointEq : L =ᵐ[μ] R :=
    (integral_eq_iff_of_ae_le hLint hRint hLR).mp hintEq
  have hsphere :
      ∀ᵐ ω ∂μ, X ω = 0 ∨ ‖X ω‖ = r_star α β p * τ := by
    filter_upwards [hpointEq] with ω hω
    by_cases hxω : X ω = 0
    · exact Or.inl hxω
    · exact Or.inr (pointwise_eq_implies_norm_eq_rstar
        hα hβ hp hp2 hreg hτ hxω (by
          dsimp only [L, R, Y] at hω
          simpa only [hβzero, zero_div, zero_mul, add_zero, mul_assoc] using hω))
  have hRstar : 0 < r_star α β p := r_star_pos hβ hp hreg
  have hRstar1 : 1 < r_star α β p := one_lt_r_star hβ hp hreg
  have hclip :
      Y =ᵐ[μ] (fun ω => ((r_star α β p)⁻¹ : ℝ) • X ω) := by
    filter_upwards [hsphere] with ω hω
    rcases hω with hx0 | hxnorm
    · simp [Y, hx0, radialClip_zero hτ.le]
    · have hlt : τ < ‖X ω‖ := by rw [hxnorm]; nlinarith
      dsimp only [Y]
      rw [radialClip_of_lt_norm hlt, hxnorm]
      congr 1
      field_simp [hτ.ne', hRstar.ne']
  have hbzero : b = 0 := by
    calc
      b = ∫ ω, ((r_star α β p)⁻¹ : ℝ) • X ω ∂μ := integral_congr_ae hclip
      _ = ((r_star α β p)⁻¹ : ℝ) • (∫ ω, X ω ∂μ) := by rw [integral_smul]
      _ = 0 := by rw [hcenter, smul_zero]
  have hαpos : 0 < α := by
    have : 0 ≤ p * β := mul_nonneg hp0 hβ
    linarith
  have hKpos : 0 < K_p α β p := by
    rw [hβzero, K_p, if_neg (by simpa [hβzero] using (not_le_of_gt hαpos))]
    unfold c_p
    positivity
  have hratiozero : stochasticClippingRatio μ α β p τ X = 0 := by
    simp [stochasticClippingRatio, Y, b, hcenter, hbzero, hβzero]
  rw [hratiozero] at hratio
  linarith
