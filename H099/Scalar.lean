import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Scalar sharp bias--energy envelope

This module formalizes the one-dimensional optimization at the core of the
deterministic and stochastic clipping bounds.

For nonnegative weights `α`, `β`, exponent `1 < p ≤ 2`, and radius `r > 0`,

`F α β p r = (α (r - 1)₊ + β min(r,1)²) / r^p`.

The main results are:

* `F_le_K_p`: the exact uniform upper bound;
* `K_p_attained`: an explicit positive radius attains the bound;
* `K_p_smallest_uniform_constant`: no smaller uniform constant is possible;
* `criticalValue_closed_form`: the critical-radius value equals the closed
  formula in the second regime.

There are no calculus or compactness assumptions in the proof.  The only
analytic input is Bernoulli's inequality for real powers.
-/

open Real
open scoped Topology

noncomputable section

/-- The scalar coefficient `cₚ = (p - 1)^(p - 1) / p^p`. -/
def c_p (p : ℝ) : ℝ := (p - 1) ^ (p - 1) / p ^ p

/-- The normalized scalar clipping objective. -/
def F (α β p r : ℝ) : ℝ :=
  (α * max (r - 1) 0 + β * (min r 1) ^ 2) / r ^ p

/-- The sharp piecewise constant from the theorem contract. -/
def K_p (α β p : ℝ) : ℝ :=
  if α ≤ p * β then β
  else c_p p * α ^ p / (α - β) ^ (p - 1)

/-- The critical radius in the second regime `p β < α`. -/
def r_star (α β p : ℝ) : ℝ :=
  p * (α - β) / (α * (p - 1))

/-- A form of the critical value adapted to the Bernoulli proof. -/
def criticalValue (α β p : ℝ) : ℝ :=
  ((α - β) / (p - 1)) / (r_star α β p) ^ p

/-- Bernoulli's inequality in the normalized form needed below. -/
lemma canonical_bernoulli {p u : ℝ} (hp : 1 ≤ p) (hu : 0 ≤ u) :
    p * u - (p - 1) ≤ u ^ p := by
  have h := one_add_mul_self_le_rpow_one_add
    (s := u - 1) (p := p) (by linarith) hp
  calc
    p * u - (p - 1) = 1 + p * (u - 1) := by ring
    _ ≤ (1 + (u - 1)) ^ p := h
    _ = u ^ p := by ring_nf

/-- Strict Bernoulli inequality away from the normalized maximizer `u = 1`. -/
lemma canonical_bernoulli_strict {p u : ℝ} (hp : 1 < p) (hu : 0 ≤ u)
    (hu1 : u ≠ 1) :
    p * u - (p - 1) < u ^ p := by
  have hs : u - 1 ≠ 0 := sub_ne_zero.mpr hu1
  have h := one_add_mul_self_lt_rpow_one_add
    (s := u - 1) (p := p) (by linarith) hs hp
  calc
    p * u - (p - 1) = 1 + p * (u - 1) := by ring
    _ < (1 + (u - 1)) ^ p := h
    _ = u ^ p := by ring_nf

/-- On the inner region `0 < r ≤ 1`, the objective is `β r^(2-p)`. -/
lemma F_inner_formula {α β p r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    F α β p r = β * r ^ (2 - p) := by
  rw [F]
  have hmax : max (r - 1) 0 = 0 := max_eq_right (sub_nonpos.mpr hr1)
  have hmin : min r 1 = r := min_eq_left hr1
  rw [hmax, hmin, mul_zero, zero_add]
  rw [← Real.rpow_natCast]
  rw [Real.rpow_sub hr]
  ring_nf

/-- The inner region never exceeds the boundary value `β`. -/
lemma F_inner_le_beta {α β p r : ℝ} (hβ : 0 ≤ β) (hp2 : p ≤ 2)
    (hr : 0 < r) (hr1 : r ≤ 1) :
    F α β p r ≤ β := by
  rw [F_inner_formula hr hr1]
  have hpow : r ^ (2 - p) ≤ 1 :=
    Real.rpow_le_one hr.le hr1 (sub_nonneg.mpr hp2)
  nlinarith [Real.rpow_nonneg hr.le (2 - p)]

/-- For positive energy weight and `p < 2`, the inner bound is strict below
the clipping boundary. -/
lemma F_inner_lt_beta {α β p r : ℝ} (hβ : 0 < β) (hp2 : p < 2)
    (hr : 0 < r) (hr1 : r < 1) :
    F α β p r < β := by
  rw [F_inner_formula hr hr1.le]
  have hpow : r ^ (2 - p) < 1 :=
    Real.rpow_lt_one hr.le hr1 (sub_pos.mpr hp2)
  nlinarith [Real.rpow_nonneg hr.le (2 - p)]

/-- On the outer region `1 ≤ r`, the objective has its affine numerator. -/
lemma F_outer_formula {α β p r : ℝ} (hr1 : 1 ≤ r) :
    F α β p r = (α * (r - 1) + β) / r ^ p := by
  rw [F]
  have hmax : max (r - 1) 0 = r - 1 := max_eq_left (sub_nonneg.mpr hr1)
  have hmin : min r 1 = 1 := min_eq_right hr1
  simp [hmax, hmin]

/-- In the first regime, the outer objective is bounded by `β`. -/
lemma F_outer_le_first_regime {α β p r : ℝ} (hβ : 0 ≤ β) (hp : 1 ≤ p)
    (hreg : α ≤ p * β) (hr1 : 1 ≤ r) :
    F α β p r ≤ β := by
  rw [F_outer_formula hr1]
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hr p)).2
  have hb := canonical_bernoulli hp (le_trans (by norm_num) hr1)
  have hscaled := mul_le_mul_of_nonneg_left hb hβ
  have hstep : α * (r - 1) ≤ (p * β) * (r - 1) :=
    mul_le_mul_of_nonneg_right hreg (sub_nonneg.mpr hr1)
  nlinarith

/-- With positive energy weight and `p > 1`, the first-regime outer bound is
strict away from the boundary radius. -/
lemma F_outer_lt_first_regime {α β p r : ℝ} (hβ : 0 < β)
    (hp : 1 < p) (hreg : α ≤ p * β) (hr1 : 1 < r) :
    F α β p r < β := by
  rw [F_outer_formula hr1.le]
  have hr : 0 < r := zero_lt_one.trans hr1
  apply (div_lt_iff₀ (Real.rpow_pos_of_pos hr p)).2
  have hb := canonical_bernoulli_strict hp hr.le (ne_of_gt hr1)
  have hscaled := mul_lt_mul_of_pos_left hb hβ
  have hstep : α * (r - 1) ≤ (p * β) * (r - 1) :=
    mul_le_mul_of_nonneg_right hreg (sub_nonneg.mpr hr1.le)
  nlinarith

/-- The critical radius is positive in the second regime. -/
lemma r_star_pos {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    0 < r_star α β p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hα : 0 < α := by nlinarith
  have hδ : 0 < α - β := by nlinarith
  exact div_pos (mul_pos hp0 hδ) (mul_pos hα (sub_pos.mpr hp))

/-- The critical radius lies strictly outside the clipping boundary. -/
lemma one_lt_r_star {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    1 < r_star α β p := by
  have hα : 0 < α := by nlinarith
  have hden : 0 < α * (p - 1) := mul_pos hα (sub_pos.mpr hp)
  rw [r_star]
  apply (lt_div_iff₀ hden).2
  nlinarith

/-- The critical value is positive in the second regime. -/
lemma criticalValue_pos {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    0 < criticalValue α β p := by
  have hδ : 0 < α - β := by nlinarith
  exact div_pos (div_pos hδ (sub_pos.mpr hp))
    (Real.rpow_pos_of_pos (r_star_pos hβ hp hreg) p)

private lemma alpha_mul_r_star {α β p : ℝ} (hα : α ≠ 0)
    (hp1 : p - 1 ≠ 0) :
    α * r_star α β p = p * (α - β) / (p - 1) := by
  rw [r_star]
  field_simp

/-- Factorization of the outer objective through the normalized radius
`u = r / r_star`. -/
lemma F_outer_second_factorization {α β p r : ℝ} (hβ : 0 ≤ β)
    (hp : 1 < p) (hreg : p * β < α) (hr1 : 1 ≤ r) :
    F α β p r =
      criticalValue α β p *
        ((p * (r / r_star α β p) - (p - 1)) /
          (r / r_star α β p) ^ p) := by
  have hα : 0 < α := by nlinarith
  have hR : 0 < r_star α β p := r_star_pos hβ hp hreg
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let u : ℝ := r / r_star α β p
  have hu : 0 < u := div_pos hr hR
  have hr_eq : r = r_star α β p * u := by
    dsimp [u]
    field_simp
  have hrpow : r ^ p = (r_star α β p) ^ p * u ^ p := by
    rw [hr_eq, Real.mul_rpow hR.le hu.le]
  have hαR : α * r_star α β p = p * (α - β) / (p - 1) :=
    alpha_mul_r_star hα.ne' (sub_ne_zero.mpr hp.ne')
  have hnum :
      α * (r - 1) + β =
        ((α - β) / (p - 1)) * (p * u - (p - 1)) := by
    rw [hr_eq]
    calc
      α * (r_star α β p * u - 1) + β
          = (α * r_star α β p) * u - (α - β) := by ring
      _ = (p * (α - β) / (p - 1)) * u - (α - β) := by rw [hαR]
      _ = ((α - β) / (p - 1)) * (p * u - (p - 1)) := by
        field_simp [sub_ne_zero.mpr hp.ne']
  rw [F_outer_formula hr1, hnum, hrpow]
  dsimp [criticalValue]
  change
    (((α - β) / (p - 1)) * (p * u - (p - 1))) /
        ((r_star α β p) ^ p * u ^ p) =
      (((α - β) / (p - 1)) / (r_star α β p) ^ p) *
        ((p * u - (p - 1)) / u ^ p)
  field_simp

/-- Bernoulli's inequality bounds the second-regime outer objective by the
critical value. -/
lemma F_outer_le_second_regime {α β p r : ℝ} (hβ : 0 ≤ β)
    (hp : 1 < p) (hreg : p * β < α) (hr1 : 1 ≤ r) :
    F α β p r ≤ criticalValue α β p := by
  rw [F_outer_second_factorization hβ hp hreg hr1]
  have hR : 0 < r_star α β p := r_star_pos hβ hp hreg
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hu : 0 < r / r_star α β p := div_pos hr hR
  have hbern := canonical_bernoulli hp.le hu.le
  have hquot :
      (p * (r / r_star α β p) - (p - 1)) /
          (r / r_star α β p) ^ p ≤ 1 :=
    (div_le_one (Real.rpow_pos_of_pos hu p)).2 hbern
  calc
    criticalValue α β p *
          ((p * (r / r_star α β p) - (p - 1)) /
            (r / r_star α β p) ^ p)
        ≤ criticalValue α β p * 1 :=
      mul_le_mul_of_nonneg_left hquot (criticalValue_pos hβ hp hreg).le
    _ = criticalValue α β p := mul_one _

/-- The second-regime outer bound is strict away from `r_star`. -/
lemma F_outer_lt_second_regime {α β p r : ℝ} (hβ : 0 ≤ β)
    (hp : 1 < p) (hreg : p * β < α) (hr1 : 1 ≤ r)
    (hrstar : r ≠ r_star α β p) :
    F α β p r < criticalValue α β p := by
  rw [F_outer_second_factorization hβ hp hreg hr1]
  have hR : 0 < r_star α β p := r_star_pos hβ hp hreg
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hu : 0 < r / r_star α β p := div_pos hr hR
  have hu1 : r / r_star α β p ≠ 1 := by
    intro h
    apply hrstar
    apply (div_eq_one_iff_eq hR.ne').mp h
  have hbern := canonical_bernoulli_strict hp hu.le hu1
  have hquot :
      (p * (r / r_star α β p) - (p - 1)) /
          (r / r_star α β p) ^ p < 1 :=
    (div_lt_one (Real.rpow_pos_of_pos hu p)).2 hbern
  simpa using
    (mul_lt_mul_of_pos_left hquot (criticalValue_pos hβ hp hreg))

/-- The critical-radius representation equals the closed formula appearing in
the theorem contract. -/
lemma criticalValue_closed_form {α β p : ℝ} (hβ : 0 ≤ β)
    (hp : 1 < p) (hreg : p * β < α) :
    criticalValue α β p =
      c_p p * α ^ p / (α - β) ^ (p - 1) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hα : 0 < α := by nlinarith
  have hδ : 0 < α - β := by nlinarith
  have hpow_pm1 :
      (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
    calc
      (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by ring_nf
      _ = (p - 1) ^ (p - 1) * (p - 1) ^ (1 : ℝ) :=
        Real.rpow_add hpm1 (p - 1) 1
      _ = (p - 1) ^ (p - 1) * (p - 1) := by rw [Real.rpow_one]
  have hpow_delta :
      (α - β) ^ p = (α - β) ^ (p - 1) * (α - β) := by
    calc
      (α - β) ^ p = (α - β) ^ ((p - 1) + 1) := by ring_nf
      _ = (α - β) ^ (p - 1) * (α - β) ^ (1 : ℝ) :=
        Real.rpow_add hδ (p - 1) 1
      _ = (α - β) ^ (p - 1) * (α - β) := by rw [Real.rpow_one]
  rw [criticalValue, r_star]
  rw [Real.div_rpow (mul_nonneg hp0.le hδ.le)
      (mul_nonneg hα.le hpm1.le)]
  rw [Real.mul_rpow hp0.le hδ.le, Real.mul_rpow hα.le hpm1.le]
  rw [hpow_pm1, hpow_delta]
  dsimp [c_p]
  field_simp

/-- In the second regime, the piecewise constant is the critical value. -/
lemma K_p_eq_criticalValue {α β p : ℝ} (hβ : 0 ≤ β)
    (hp : 1 < p) (hreg : p * β < α) :
    K_p α β p = criticalValue α β p := by
  rw [K_p, if_neg (not_le_of_gt hreg),
    criticalValue_closed_form hβ hp hreg]

/-- Main scalar theorem: `F(r) ≤ Kₚ(α,β)` for every positive radius. -/
theorem F_le_K_p {α β p r : ℝ} (_hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hr : 0 < r) :
    F α β p r ≤ K_p α β p := by
  by_cases hreg : α ≤ p * β
  · rw [K_p, if_pos hreg]
    by_cases hr1 : r ≤ 1
    · exact F_inner_le_beta hβ hp2 hr hr1
    · exact F_outer_le_first_regime hβ hp.le hreg (le_of_not_ge hr1)
  · have hreg' : p * β < α := lt_of_not_ge hreg
    rw [K_p, if_neg hreg]
    rw [← criticalValue_closed_form hβ hp hreg']
    by_cases hr1 : r ≤ 1
    · calc
        F α β p r ≤ β := F_inner_le_beta hβ hp2 hr hr1
        _ = F α β p 1 := by simp [F]
        _ ≤ criticalValue α β p :=
          F_outer_le_second_regime hβ hp hreg' (le_refl 1)
    · exact F_outer_le_second_regime hβ hp hreg' (le_of_not_ge hr1)

/-- Denominator-free form of the scalar envelope. -/
theorem scalar_numerator_le {α β p r : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p ≤ 2) (hr : 0 < r) :
    α * max (r - 1) 0 + β * (min r 1) ^ 2
      ≤ K_p α β p * r ^ p := by
  have h := F_le_K_p hα hβ hp hp2 hr
  rw [F] at h
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hr p)).mp h

/-- The critical radius exactly attains the critical value. -/
lemma F_at_r_star {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    F α β p (r_star α β p) = criticalValue α β p := by
  rw [F_outer_second_factorization hβ hp hreg (one_lt_r_star hβ hp hreg).le]
  have hRne : r_star α β p ≠ 0 := (r_star_pos hβ hp hreg).ne'
  simp [hRne]

/-- The critical radius is the unique positive maximizer in the second
regime. -/
theorem maximizing_radius_second_regime {α β p r : ℝ}
    (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (hreg : p * β < α) (hr : 0 < r)
    (heq : F α β p r = K_p α β p) :
    r = r_star α β p := by
  have hK : K_p α β p = criticalValue α β p :=
    K_p_eq_criticalValue hβ hp hreg
  have hbeta_lt : β < criticalValue α β p := by
    have hstrict := F_outer_lt_second_regime hβ hp hreg (le_refl 1)
      (ne_of_lt (one_lt_r_star hβ hp hreg))
    simpa [F] using hstrict
  by_cases hr1 : r ≤ 1
  · have hlt : F α β p r < criticalValue α β p :=
      lt_of_le_of_lt (F_inner_le_beta hβ hp2 hr hr1) hbeta_lt
    rw [heq, hK] at hlt
    exact (lt_irrefl _ hlt).elim
  · by_contra hne
    have hlt := F_outer_lt_second_regime hβ hp hreg
      (le_of_not_ge hr1) hne
    rw [heq, hK] at hlt
    exact (lt_irrefl _ hlt).elim

private lemma beta_pos_in_nonzero_first_regime {α β p : ℝ}
    (hp : 0 < p)
    (hreg : α ≤ p * β) (hnonzero : 0 < α ∨ 0 < β) :
    0 < β := by
  rcases hnonzero with hαpos | hβpos
  · nlinarith
  · exact hβpos

/-- For `1 < p < 2` and nonzero first-regime weights, `r = 1` is the unique
positive maximizing radius. -/
theorem maximizing_radius_first_regime_of_lt_two
    {α β p r : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hp : 1 < p) (hp2 : p < 2) (hreg : α ≤ p * β)
    (hnonzero : 0 < α ∨ 0 < β) (hr : 0 < r)
    (heq : F α β p r = K_p α β p) :
    r = 1 := by
  have hβpos : 0 < β :=
    beta_pos_in_nonzero_first_regime (zero_lt_one.trans hp) hreg hnonzero
  have hK : K_p α β p = β := by simp [K_p, hreg]
  rcases lt_trichotomy r 1 with hrlt | hre | hrgt
  · have hlt := F_inner_lt_beta (α := α) hβpos hp2 hr hrlt
    rw [heq, hK] at hlt
    exact (lt_irrefl _ hlt).elim
  · exact hre
  · have hlt := F_outer_lt_first_regime hβpos hp hreg hrgt
    rw [heq, hK] at hlt
    exact (lt_irrefl _ hlt).elim

/-- At `p = 2`, the positive first-regime maximizing radii are exactly
`0 < r ≤ 1`. -/
theorem maximizing_radii_first_regime_p_two
    {α β r : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hreg : α ≤ 2 * β) (hnonzero : 0 < α ∨ 0 < β)
    (hr : 0 < r) :
    F α β 2 r = K_p α β 2 ↔ r ≤ 1 := by
  have hβpos : 0 < β :=
    beta_pos_in_nonzero_first_regime (by norm_num) hreg hnonzero
  constructor
  · intro heq
    by_contra hr1
    have hlt := F_outer_lt_first_regime hβpos (by norm_num) hreg
      (lt_of_not_ge hr1)
    have hK : K_p α β 2 = β := by simp [K_p, hreg]
    rw [heq, hK] at hlt
    exact (lt_irrefl _ hlt).elim
  · intro hr1
    rw [F_inner_formula hr hr1]
    simp [K_p, hreg]

/-- With both weights zero, every positive radius is maximizing. -/
@[simp] theorem every_radius_maximizes_zero_weights {p r : ℝ} :
    F 0 0 p r = K_p 0 0 p := by
  simp [F, K_p]

/-- In both regimes, a concrete positive radius attains `K_p`. -/
theorem K_p_attained {α β p : ℝ} (_hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) :
    ∃ r, 0 < r ∧ F α β p r = K_p α β p := by
  by_cases hreg : α ≤ p * β
  · refine ⟨1, zero_lt_one, ?_⟩
    simp [F, K_p, hreg]
  · have hreg' : p * β < α := lt_of_not_ge hreg
    refine ⟨r_star α β p, r_star_pos hβ hp hreg', ?_⟩
    rw [F_at_r_star hβ hp hreg']
    rw [K_p, if_neg hreg, criticalValue_closed_form hβ hp hreg']

/-- `K_p` is the smallest constant which bounds `F` at every positive radius. -/
theorem K_p_smallest_uniform_constant {α β p C : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hp : 1 < p)
    (hC : ∀ r : ℝ, 0 < r → F α β p r ≤ C) :
    K_p α β p ≤ C := by
  obtain ⟨r, hr, hEq⟩ := K_p_attained hα hβ hp
  rw [← hEq]
  exact hC r hr

/-- Epsilon-optimality, retained as a convenient supremum-style corollary. -/
theorem K_p_optimal {α β p : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hp : 1 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ r, 0 < r ∧ F α β p r > K_p α β p - ε := by
  obtain ⟨r, hr, hEq⟩ := K_p_attained hα hβ hp
  refine ⟨r, hr, ?_⟩
  rw [hEq]
  linarith

/-- The piecewise definition selects the first-branch value at the phase
boundary. -/
lemma K_p_at_boundary {α β p : ℝ} (hαβ : α = p * β) :
    K_p α β p = β := by
  simp [K_p, hαβ]

/-- At every nonzero phase-boundary point, the closed expression from the
second branch also equals the first-branch value. -/
lemma second_branch_closed_form_at_boundary {β p : ℝ}
    (hβ : 0 < β) (hp : 1 < p) :
    c_p p * (p * β) ^ p / (p * β - β) ^ (p - 1) = β := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm1 : 0 < p - 1 := sub_pos.mpr hp
  have hdelta : p * β - β = (p - 1) * β := by ring
  have hβpow :
      β ^ p = β ^ (p - 1) * β := by
    calc
      β ^ p = β ^ ((p - 1) + 1) := by ring_nf
      _ = β ^ (p - 1) * β ^ (1 : ℝ) :=
        Real.rpow_add hβ (p - 1) 1
      _ = β ^ (p - 1) * β := by rw [Real.rpow_one]
  rw [c_p, Real.mul_rpow hp0.le hβ.le, hdelta,
    Real.mul_rpow hpm1.le hβ.le, hβpow]
  field_simp [
    (Real.rpow_pos_of_pos hp0 p).ne',
    (Real.rpow_pos_of_pos hpm1 (p - 1)).ne',
    (Real.rpow_pos_of_pos hβ (p - 1)).ne']

/-- In the open second-regime cone, the closed branch expression lies between
zero and the residual weight `α`. -/
lemma second_branch_closed_form_mem_Icc_alpha
    {α β p : ℝ} (hβ : 0 ≤ β) (hp : 1 < p)
    (hreg : p * β < α) :
    0 ≤ c_p p * α ^ p / (α - β) ^ (p - 1) ∧
      c_p p * α ^ p / (α - β) ^ (p - 1) ≤ α := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hα : 0 < α := by nlinarith
  have hβα : β < α := by nlinarith
  have hδ : 0 < α - β := sub_pos.mpr hβα
  constructor
  · dsimp only [c_p]
    positivity
  · rw [← criticalValue_closed_form hβ hp hreg]
    let R : ℝ := r_star α β p
    have hR : 1 < R := one_lt_r_star hβ hp hreg
    have hRpow : R ≤ R ^ p :=
      Real.self_le_rpow_of_one_le hR.le hp.le
    have hnum : α * (R - 1) + β ≤ α * R := by
      nlinarith
    have hscaled : α * R ≤ α * R ^ p :=
      mul_le_mul_of_nonneg_left hRpow hα.le
    rw [← F_at_r_star hβ hp hreg, F_outer_formula hR.le]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hR) p)).2
      (hnum.trans hscaled)

/-- The closed expression from the second branch has continuous extension
zero at the origin when approached inside its natural nonnegative
second-regime cone. -/
theorem tendsto_second_branch_closed_form_at_origin
    {p : ℝ} (hp : 1 < p) :
    Filter.Tendsto
      (fun z : ℝ × ℝ =>
        c_p p * z.1 ^ p / (z.1 - z.2) ^ (p - 1))
      (nhdsWithin (0, 0)
        {z : ℝ × ℝ | 0 ≤ z.2 ∧ p * z.2 < z.1})
      (𝓝 0) := by
  let S : Set (ℝ × ℝ) :=
    {z : ℝ × ℝ | 0 ≤ z.2 ∧ p * z.2 < z.1}
  have hfst :
      Filter.Tendsto (fun z : ℝ × ℝ => z.1)
        (nhdsWithin (0, 0) S) (𝓝 0) := by
    simpa only using
      (continuous_fst.tendsto (0, 0)).mono_left nhdsWithin_le_nhds
  have hnonneg :
      ∀ᶠ z in nhdsWithin (0, 0) S,
        0 ≤ c_p p * z.1 ^ p / (z.1 - z.2) ^ (p - 1) := by
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    exact (second_branch_closed_form_mem_Icc_alpha hz.1 hp hz.2).1
  have hupper :
      ∀ᶠ z in nhdsWithin (0, 0) S,
        c_p p * z.1 ^ p / (z.1 - z.2) ^ (p - 1) ≤ z.1 := by
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    exact (second_branch_closed_form_mem_Icc_alpha hz.1 hp hz.2).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hfst hnonneg hupper

/-- The sharp constant at the zero direction is zero. -/
@[simp] lemma K_p_zero (p : ℝ) : K_p 0 0 p = 0 := by
  simp [K_p]

/-- The restriction `p ≤ 2` is essential when the energy weight is positive:
for `p > 2`, the normalized scalar objective diverges as the radius tends to
zero from the right. -/
theorem tendsto_F_nhdsGT_zero_atTop_of_two_lt_p
    {α β p : ℝ} (hβ : 0 < β) (hp2 : 2 < p) :
    Filter.Tendsto (fun r => F α β p r) (𝓝[>] 0) Filter.atTop := by
  have hpow :
      Filter.Tendsto (fun r : ℝ => r ^ (2 - p))
        (𝓝[>] 0) Filter.atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hscaled :
      Filter.Tendsto (fun r : ℝ => β * r ^ (2 - p))
        (𝓝[>] 0) Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hβ hpow
  have heq :
      (fun r : ℝ => F α β p r)
        =ᶠ[𝓝[>] 0] (fun r : ℝ => β * r ^ (2 - p)) := by
    have hltone :
        ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Iio_mem_nhds zero_lt_one)
    filter_upwards [eventually_mem_nhdsWithin, hltone] with r hr hlt
    exact F_inner_formula hr hlt.le
  exact hscaled.congr' heq.symm
