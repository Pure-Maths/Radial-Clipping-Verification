import SharpRadialClipping.Scalar
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Deterministic radial clipping envelope

This module lifts the scalar optimization in `SharpRadialClipping.Scalar` to an arbitrary
real normed space.
-/

open Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every nontrivial real normed space contains a unit vector. -/
lemma exists_norm_eq_one [Nontrivial E] : ∃ e : E, ‖e‖ = 1 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨(‖v‖)⁻¹ • v, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)]
  field_simp

/-- Radial clipping at radius `τ`. -/
def radialClip (τ : ℝ) (x : E) : E :=
  if ‖x‖ ≤ τ then x else (τ / ‖x‖) • x

@[simp] lemma radialClip_of_norm_le {τ : ℝ} {x : E} (h : ‖x‖ ≤ τ) :
    radialClip τ x = x := by
  simp [radialClip, h]

lemma radialClip_of_lt_norm {τ : ℝ} {x : E} (h : τ < ‖x‖) :
    radialClip τ x = (τ / ‖x‖) • x := by
  simp [radialClip, not_le_of_gt h]

@[simp] lemma radialClip_zero {τ : ℝ} (hτ : 0 ≤ τ) :
    radialClip τ (0 : E) = 0 := by
  simp [radialClip, hτ]

/-- The norm of the clipped vector is the smaller of `‖x‖` and `τ`. -/
lemma norm_radialClip {τ : ℝ} (hτ : 0 < τ) (x : E) :
    ‖radialClip τ x‖ = min ‖x‖ τ := by
  by_cases h : ‖x‖ ≤ τ
  · simp [radialClip, h]
  · have hlt : τ < ‖x‖ := lt_of_not_ge h
    have hx : 0 < ‖x‖ := hτ.trans hlt
    have hq : 0 < τ / ‖x‖ := div_pos hτ hx
    rw [radialClip_of_lt_norm hlt, norm_smul, Real.norm_eq_abs,
      abs_of_pos hq, min_eq_right hlt.le]
    field_simp

/-- The clipping residual has norm `(‖x‖ - τ)₊`. -/
lemma norm_sub_radialClip {τ : ℝ} (hτ : 0 < τ) (x : E) :
    ‖x - radialClip τ x‖ = max (‖x‖ - τ) 0 := by
  by_cases h : ‖x‖ ≤ τ
  · rw [radialClip_of_norm_le h, sub_self, norm_zero]
    simp [sub_nonpos.mpr h]
  · have hlt : τ < ‖x‖ := lt_of_not_ge h
    have hx : 0 < ‖x‖ := hτ.trans hlt
    have hq : 0 < τ / ‖x‖ := div_pos hτ hx
    have hq1 : τ / ‖x‖ < 1 := (div_lt_one hx).2 hlt
    have hvector :
        x - (τ / ‖x‖) • x = (1 - τ / ‖x‖) • x := by
      module
    rw [radialClip_of_lt_norm hlt, hvector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hq1), max_eq_left (sub_nonneg.mpr hlt.le)]
    field_simp

/-- The exact deterministic bias--energy envelope in an arbitrary real normed
space. -/
theorem radialClip_envelope {α β p τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) (x : E) :
    α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
      ≤ K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p := by
  by_cases hx0 : x = 0
  · subst x
    have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
    simp [radialClip_zero hτ.le, Real.zero_rpow hp0]
  · have hx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
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
    have hleft :
        α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2 =
          τ * (α * max (r - 1) 0 + β * (min r 1) ^ 2) := by
      rw [norm_sub_radialClip hτ, norm_radialClip hτ, hmax, hmin]
      field_simp
    have hpowτ : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    have hright :
        K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p =
          τ * (K_p α β p * r ^ p) := by
      rw [hnorm, Real.mul_rpow hτ.le hr.le]
      calc
        K_p α β p * τ ^ (1 - p) * (τ ^ p * r ^ p)
            = (τ ^ (1 - p) * τ ^ p) * (K_p α β p * r ^ p) := by ring
        _ = τ * (K_p α β p * r ^ p) := by rw [hpowτ]
    rw [hleft, hright]
    exact mul_le_mul_of_nonneg_left
      (scalar_numerator_le hα hβ hp hp2 hr) hτ.le

/-- In every nontrivial normed space, the deterministic envelope is attained
by a vector on a suitable ray. -/
theorem exists_vector_attaining_envelope [Nontrivial E]
    {α β p τ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hτ : 0 < τ) :
    ∃ x : E,
      x ≠ 0 ∧
        α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2 =
          K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p := by
  obtain ⟨r, hr, hFr⟩ := K_p_attained hα hβ hp
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := E)
  have hτr : 0 < τ * r := mul_pos hτ hr
  let x : E := (τ * r) • e
  have hnormx : ‖x‖ = τ * r := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_pos hτr]
  have hmax :
      max (‖x‖ - τ) 0 = τ * max (r - 1) 0 := by
    calc
      max (‖x‖ - τ) 0 = max (τ * (r - 1)) (τ * 0) := by
        rw [hnormx]
        congr 1 <;> ring
      _ = τ * max (r - 1) 0 :=
        (mul_max_of_nonneg (r - 1) 0 hτ.le).symm
  have hmin :
      min ‖x‖ τ = τ * min r 1 := by
    calc
      min ‖x‖ τ = min (τ * r) (τ * 1) := by rw [hnormx, mul_one]
      _ = τ * min r 1 := (mul_min_of_nonneg r 1 hτ.le).symm
  have hnum :
      α * max (r - 1) 0 + β * (min r 1) ^ 2 =
        K_p α β p * r ^ p := by
    rw [F] at hFr
    exact (div_eq_iff (Real.rpow_pos_of_pos hr p).ne').mp hFr
  have hpowτ : τ ^ (1 - p) * τ ^ p = τ := by
    rw [← Real.rpow_add hτ]
    norm_num
  have hxne : x ≠ 0 := by
    exact norm_pos_iff.mp (by rw [hnormx]; exact hτr)
  refine ⟨x, hxne, ?_⟩
  rw [norm_sub_radialClip hτ, norm_radialClip hτ, hmax, hmin]
  calc
    α * (τ * max (r - 1) 0) +
          β / τ * (τ * min r 1) ^ 2
        = τ * (α * max (r - 1) 0 + β * (min r 1) ^ 2) := by
      field_simp
    _ = τ * (K_p α β p * r ^ p) := by rw [hnum]
    _ = K_p α β p * τ ^ (1 - p) * ‖x‖ ^ p := by
      rw [hnormx, Real.mul_rpow hτ.le hr.le]
      calc
        τ * (K_p α β p * r ^ p)
            = (τ ^ (1 - p) * τ ^ p) * (K_p α β p * r ^ p) := by
              rw [hpowτ]
        _ = K_p α β p * τ ^ (1 - p) * (τ ^ p * r ^ p) := by ring

/-- Therefore `K_p` is the smallest uniform constant in the vector envelope
on any nontrivial real normed space. -/
theorem K_p_smallest_vector_constant [Nontrivial E]
    {α β p τ C : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hτ : 0 < τ)
    (hC : ∀ x : E,
      α * ‖x - radialClip τ x‖ + (β / τ) * ‖radialClip τ x‖ ^ 2
        ≤ C * τ ^ (1 - p) * ‖x‖ ^ p) :
    K_p α β p ≤ C := by
  obtain ⟨x₀, hx₀ne, hx₀⟩ :=
    exists_vector_attaining_envelope (E := E) hα hβ hp hτ
  have hbound := hC x₀
  rw [hx₀] at hbound
  have hscale : 0 < τ ^ (1 - p) * ‖x₀‖ ^ p := by
    have hx₀norm : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀ne
    exact mul_pos (Real.rpow_pos_of_pos hτ (1 - p))
      (Real.rpow_pos_of_pos hx₀norm p)
  have hbound' :
      K_p α β p * (τ ^ (1 - p) * ‖x₀‖ ^ p)
        ≤ C * (τ ^ (1 - p) * ‖x₀‖ ^ p) := by
    simpa [mul_assoc] using hbound
  nlinarith
