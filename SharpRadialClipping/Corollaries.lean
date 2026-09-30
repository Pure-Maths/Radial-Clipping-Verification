import SharpRadialClipping.Deterministic

/-!
# Named corollaries of the sharp envelope
-/

open Real

noncomputable section

/-- The one-parameter sharp constant. -/
def kappa_p (p lam : ℝ) : ℝ := K_p 1 lam p

/-- Explicit one-parameter phase split.  At the boundary the two displayed
branches agree, so choosing the linear branch there is immaterial. -/
lemma kappa_p_eq_piecewise {p lam : ℝ} (hlam : 0 ≤ lam) (hp : 1 < p) :
    kappa_p p lam =
      if 1 ≤ p * lam then lam
      else c_p p * (1 - lam) ^ (1 - p) := by
  rw [kappa_p, K_p]
  split_ifs with hreg
  · rfl
  · have hp0 : 0 < p := zero_lt_one.trans hp
    have hlamlt : lam < 1 := by
      have : p * lam < 1 := lt_of_not_ge hreg
      nlinarith
    have hbase : 0 < 1 - lam := sub_pos.mpr hlamlt
    rw [Real.one_rpow]
    have hexp : 1 - p = -(p - 1) := by ring
    rw [hexp, Real.rpow_neg hbase.le]
    simp only [div_eq_mul_inv, mul_one]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One-parameter form of the deterministic SharpRadialClipping envelope. -/
theorem radialClip_envelope_one_parameter
    {p lam τ : ℝ} (hlam : 0 ≤ lam) (hp : 1 < p) (hp2 : p ≤ 2)
    (hτ : 0 < τ) (x : E) :
    ‖x - radialClip τ x‖ + (lam / τ) * ‖radialClip τ x‖ ^ 2
      ≤ kappa_p p lam * τ ^ (1 - p) * ‖x‖ ^ p := by
  simpa [kappa_p] using
    radialClip_envelope (α := (1 : ℝ)) (β := lam)
      (by norm_num) hlam hp hp2 hτ x

/-- For `p = 2`, the nonlinear branch reduces to
`1 / (4 (1 - lam))`. -/
lemma kappa_two_eq_piecewise {lam : ℝ} (hlam : 0 ≤ lam) :
    kappa_p 2 lam =
      if 1 ≤ 2 * lam then lam else 1 / (4 * (1 - lam)) := by
  rw [kappa_p_eq_piecewise hlam (by norm_num)]
  split_ifs with hreg
  · rfl
  · have hlamlt : lam < 1 := by nlinarith
    have hbase : 0 < 1 - lam := sub_pos.mpr hlamlt
    simp only [c_p]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
