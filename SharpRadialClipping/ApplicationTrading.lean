import SharpRadialClipping.ApplicationTradingHelpers
import SharpRadialClipping.Deterministic

/-!
# Clipped projected trading update

The one-risky-asset regret bound of the application section.  All returns are
arbitrary positive real numbers; no probabilistic assumptions are used.
-/

open Real

noncomputable section

/-- The derivative of one-period log wealth at the chosen risky-asset weight. -/
def tradingSignal (r w : ℝ) : ℝ := (r - 1) / (1 + w * (r - 1))

/-- The total wealth of a sequence of risky-asset fractions, starting from one. -/
def tradingWealth (T : ℕ) (r w : ℕ → ℝ) : ℝ :=
  ∏ t ∈ Finset.range T, (1 + w t * (r t - 1))

/-- Wealth of a fixed rebalanced fraction, starting from one. -/
def fixedFractionWealth (T : ℕ) (r : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∏ t ∈ Finset.range T, (1 + u * (r t - 1))

/-- The article's sharp deterministic clipping bound at exponent two and
trading weights `1` and `μτ/2`. -/
theorem trading_clip_envelope (μ τ g : ℝ) (hμ : 0 < μ) (hτ : 0 < τ) :
    |g - radialClip τ g| + μ / 2 * (radialClip τ g) ^ 2 ≤
      K_p 1 (μ * τ / 2) 2 / τ * g ^ 2 := by
  have h := radialClip_envelope (α := 1) (β := μ * τ / 2) (p := 2)
    (τ := τ) (by norm_num) (by positivity) (by norm_num) (by norm_num) hτ g
  simp only [one_mul, Real.norm_eq_abs] at h
  have hnorm : |radialClip τ g| ^ 2 = (radialClip τ g) ^ 2 := by
    rw [sq_abs]
  rw [hnorm] at h
  have hpow : τ ^ (1 - (2 : ℝ)) = 1 / τ := by
    norm_num [Real.rpow_neg_one]
  rw [hpow] at h
  have hcoef : μ * τ / 2 / τ = μ / 2 := by
    field_simp
  rw [hcoef] at h
  have hgpow : |g| ^ (2 : ℝ) = g ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  rw [hgpow] at h
  convert h using 1
  simp only [div_eq_mul_inv, one_mul]

/-- The clipped projected update yields a regret bound against every fixed
rebalanced risky-asset fraction in `[0,1]`.  The statement includes the
strict positivity of all gross risky-asset returns and uses the exact
deterministic clipping constant. -/
theorem trading_regret_bound (T : ℕ) (r w : ℕ → ℝ) (μ τ u : ℝ)
    (hr : ∀ t < T, 0 < r t) (hμ : 0 < μ) (hτ : 0 < τ)
    (hw0 : 0 ≤ w 0) (hw1 : w 0 ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hupdate : ∀ t < T,
      w (t + 1) = SharpRadialClipping.projectUnit
        (w t + μ * radialClip τ (tradingSignal (r t) (w t)))) :
    Real.log (fixedFractionWealth T r u / tradingWealth T r w) ≤
      (u - w 0) ^ 2 / (2 * μ) +
        K_p 1 (μ * τ / 2) 2 / τ *
          (Finset.range T).sum (fun t ↦ (tradingSignal (r t) (w t)) ^ 2) := by
  have hw : ∀ t ≤ T, 0 ≤ w t ∧ w t ≤ 1 := by
    intro t ht
    induction t with
    | zero => exact ⟨hw0, hw1⟩
    | succ t ih =>
        have hlt : t < T := by omega
        rw [hupdate t hlt]
        exact ⟨SharpRadialClipping.projectUnit_nonneg _, SharpRadialClipping.projectUnit_le_one _⟩
  have hstep (t : ℕ) (ht : t < T) :
      Real.log (1 + u * (r t - 1)) - Real.log (1 + w t * (r t - 1)) ≤
        ((u - w t) ^ 2 - (u - w (t + 1)) ^ 2) / (2 * μ) +
          K_p 1 (μ * τ / 2) 2 / τ * (tradingSignal (r t) (w t)) ^ 2 := by
    let g := tradingSignal (r t) (w t)
    let z := radialClip τ g
    have hwt := hw t (Nat.le_of_lt ht)
    have hlog := SharpRadialClipping.log_growth_tangent (r := r t) (u := u) (w := w t)
      (hr t ht) hu0 hu1 hwt.1 hwt.2
    change Real.log (1 + u * (r t - 1)) -
      Real.log (1 + w t * (r t - 1)) ≤ g * (u - w t) at hlog
    have hdist : |u - w t| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    have herr : g * (u - w t) ≤ z * (u - w t) + |g - z| := by
      have hb : (g - z) * (u - w t) ≤ |g - z| := calc
        _ ≤ |(g - z) * (u - w t)| := le_abs_self _
        _ = |g - z| * |u - w t| := abs_mul _ _
        _ ≤ |g - z| * 1 := mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        _ = |g - z| := mul_one _
      nlinarith
    have hpot := SharpRadialClipping.projected_update_potential (w := w t) (u := u)
      (z := z) (μ := μ) hμ hu0 hu1
    change z * (u - w t) ≤
      ((u - w t) ^ 2 -
        (u - SharpRadialClipping.projectUnit (w t + μ * z)) ^ 2) / (2 * μ) +
          μ / 2 * z ^ 2 at hpot
    rw [← hupdate t ht] at hpot
    have hclip := trading_clip_envelope μ τ g hμ hτ
    change |g - z| + μ / 2 * z ^ 2 ≤
      K_p 1 (μ * τ / 2) 2 / τ * g ^ 2 at hclip
    change Real.log (1 + u * (r t - 1)) -
      Real.log (1 + w t * (r t - 1)) ≤
        ((u - w t) ^ 2 - (u - w (t + 1)) ^ 2) / (2 * μ) +
          K_p 1 (μ * τ / 2) 2 / τ * g ^ 2
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.range T)
    (fun t ht ↦ hstep t (Finset.mem_range.mp ht))
  have hR : 0 < fixedFractionWealth T r u := by
    unfold fixedFractionWealth
    apply Finset.prod_pos
    intro t ht
    exact SharpRadialClipping.portfolio_factor_pos (hr t (Finset.mem_range.mp ht)) hu0 hu1
  have hW : 0 < tradingWealth T r w := by
    unfold tradingWealth
    apply Finset.prod_pos
    intro t ht
    have hwt := hw t (Nat.le_of_lt (Finset.mem_range.mp ht))
    exact SharpRadialClipping.portfolio_factor_pos (hr t (Finset.mem_range.mp ht)) hwt.1 hwt.2
  have hlogR : Real.log (fixedFractionWealth T r u) =
      (Finset.range T).sum (fun t ↦ Real.log (1 + u * (r t - 1))) := by
    simpa only [fixedFractionWealth] using
      (SharpRadialClipping.portfolio_log_prod (r := r) (w := fun _ ↦ u) hr
        (fun _ _ ↦ hu0) (fun _ _ ↦ hu1))
  have hlogW : Real.log (tradingWealth T r w) =
      (Finset.range T).sum (fun t ↦ Real.log (1 + w t * (r t - 1))) := by
    apply SharpRadialClipping.portfolio_log_prod hr
      (fun t ht ↦ (hw t (Nat.le_of_lt ht)).1)
      (fun t ht ↦ (hw t (Nat.le_of_lt ht)).2)
  rw [Real.log_div hR.ne' hW.ne', hlogR, hlogW]
  rw [Finset.sum_sub_distrib] at hsum
  have htelescope := SharpRadialClipping.trading_potential_telescope T u w
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hpot_sum :
      (Finset.range T).sum (fun t ↦
        ((u - w t) ^ 2 - (u - w (t + 1)) ^ 2) / (2 * μ)) =
          ((u - w 0) ^ 2 - (u - w T) ^ 2) / (2 * μ) := by
    rw [← Finset.sum_div, htelescope]
  rw [hpot_sum] at hsum
  have hneg : 0 ≤ (u - w T) ^ 2 / (2 * μ) := by positivity
  rw [sub_div] at hsum
  linarith

#print axioms trading_clip_envelope
#print axioms trading_regret_bound
