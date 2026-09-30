import H099.AllThresholdsApprox
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Limits of clipped and untruncated means under weak convergence

The clipped mean is a bounded-continuous test of a probability law.  For the
unclipped mean, a common integrable radial law gives a uniform tail bound.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

noncomputable section

abbrev H099R3 := EuclideanSpace ℝ (Fin 3)

local instance : MeasurableSpace H099R3 := borel H099R3
local instance : BorelSpace H099R3 := ⟨rfl⟩

/-- Integrals of a fixed clipped vector converge under weak convergence of
probability measures on Euclidean three-space. -/
theorem tendsto_integral_radialClip_of_weak
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (hν : Tendsto νs atTop (nhds ν)) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun n => ∫ x, radialClip τ x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, radialClip τ x ∂(ν : Measure H099R3))) := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have hcoordTend (i : Fin 3) :
      Tendsto (fun n ↦ (e (∫ x, radialClip τ x ∂(νs n : Measure H099R3))) i)
        atTop (nhds ((e (∫ x, radialClip τ x ∂(ν : Measure H099R3))) i)) := by
    let L : H099R3 →L[ℝ] ℝ := EuclideanSpace.proj i
    let f : H099R3 →ᵇ ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup
        (fun x ↦ L (radialClip τ x))
        (L.continuous.comp (continuous_radialClip τ hτ)) τ (by
          intro x
          calc
            ‖L (radialClip τ x)‖ ≤ ‖radialClip τ x‖ := by
              have hcoord : ‖(radialClip τ x) i‖ ≤ ‖radialClip τ x‖ :=
                PiLp.norm_apply_le (radialClip τ x) i
              simpa [L, EuclideanSpace.coe_proj, Real.norm_eq_abs] using hcoord
            _ = min ‖x‖ τ := norm_radialClip hτ x
            _ ≤ τ := min_le_right _ _)
    have htest :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) f
    have hint (μ : ProbabilityMeasure H099R3) : Integrable
        (fun x ↦ radialClip τ x) (μ : Measure H099R3) := by
      exact integrable_radialClip (by fun_prop) hτ
    have hcoord (μ : ProbabilityMeasure H099R3) :
        (e (∫ x, radialClip τ x ∂(μ : Measure H099R3))) i =
          ∫ x, f x ∂(μ : Measure H099R3) := by
      change L (∫ x, radialClip τ x ∂(μ : Measure H099R3)) =
        ∫ x, f x ∂(μ : Measure H099R3)
      dsimp [f]
      rw [ContinuousLinearMap.integral_comp_comm L (hint μ)]
    simpa only [hcoord] using htest
  have hcoords : Tendsto
      (fun n ↦ e (∫ x, radialClip τ x ∂(νs n : Measure H099R3))) atTop
      (nhds (e (∫ x, radialClip τ x ∂(ν : Measure H099R3)))) :=
    tendsto_pi_nhds.mpr hcoordTend
  have hresult := (e.symm.continuous.tendsto
    (e (∫ x, radialClip τ x ∂(ν : Measure H099R3)))).comp hcoords
  simpa only [Function.comp_def, e.symm_apply_apply] using hresult

/-- Weak convergence plus a uniform bound on discarded mean tails implies
convergence of the untruncated vector means.  Radial moment control will
provide the tail hypothesis in the all-thresholds application. -/
theorem tendsto_integral_id_of_weak_of_uniform_clipping_tail
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (hν : Tendsto νs atTop (nhds ν))
    (hId : ∀ n, Integrable (fun x : H099R3 ↦ x) (νs n : Measure H099R3))
    (hIdLim : Integrable (fun x : H099R3 ↦ x) (ν : Measure H099R3))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, 0 < τ ∧
      (∀ n, ‖∫ x, x - radialClip τ x ∂(νs n : Measure H099R3)‖ ≤ ε) ∧
      ‖∫ x, x - radialClip τ x ∂(ν : Measure H099R3)‖ ≤ ε) :
    Tendsto (fun n ↦ ∫ x, x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, x ∂(ν : Measure H099R3))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨τ, hτ, htailSeq, htailLim⟩ := htail (ε / 4) (by positivity)
  have hclip := tendsto_integral_radialClip_of_weak νs ν hν hτ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hclip (ε / 2) (by positivity)
  refine ⟨N, ?_⟩
  intro n hn
  have hClipSeq : Integrable (fun x : H099R3 ↦ radialClip τ x)
      (νs n : Measure H099R3) := integrable_radialClip (hId n).1 hτ
  have hClipLim : Integrable (fun x : H099R3 ↦ radialClip τ x)
      (ν : Measure H099R3) := integrable_radialClip hIdLim.1 hτ
  have hSeqEq :
      (∫ x, x ∂(νs n : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(νs n : Measure H099R3)) =
      ∫ x, x - radialClip τ x ∂(νs n : Measure H099R3) := by
    rw [integral_sub (hId n) hClipSeq]
  have hLimEq :
      (∫ x, x ∂(ν : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(ν : Measure H099R3)) =
      ∫ x, x - radialClip τ x ∂(ν : Measure H099R3) := by
    rw [integral_sub hIdLim hClipLim]
  have hmiddle :
      ‖(∫ x, radialClip τ x ∂(νs n : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(ν : Measure H099R3))‖ < ε / 2 := by
    simpa [dist_eq_norm] using hN n hn
  rw [dist_eq_norm]
  have hdecomp :
      (∫ x, x ∂(νs n : Measure H099R3)) -
        (∫ x, x ∂(ν : Measure H099R3)) =
      ((∫ x, x ∂(νs n : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(νs n : Measure H099R3))) +
      ((∫ x, radialClip τ x ∂(νs n : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(ν : Measure H099R3))) +
      ((∫ x, radialClip τ x ∂(ν : Measure H099R3)) -
        (∫ x, x ∂(ν : Measure H099R3))) := by
    abel
  rw [hdecomp]
  have hlast :
      ‖(∫ x, radialClip τ x ∂(ν : Measure H099R3)) -
        (∫ x, x ∂(ν : Measure H099R3))‖ ≤ ε / 4 := by
    rw [norm_sub_rev, hLimEq]
    exact htailLim
  have hfirst :
      ‖(∫ x, x ∂(νs n : Measure H099R3)) -
        (∫ x, radialClip τ x ∂(νs n : Measure H099R3))‖ ≤ ε / 4 := by
    rw [hSeqEq]
    exact htailSeq n
  exact lt_of_le_of_lt norm_add₃_le (by linarith)

/-- The mean of the part discarded by clipping is bounded by a scalar tail
integral depending only on the radial distribution. -/
theorem norm_integral_residual_le_radial_tail
    (ν : ProbabilityMeasure H099R3) (ρ : Measure ℝ)
    (hρ : Measure.map (fun x : H099R3 ↦ ‖x‖) (ν : Measure H099R3) = ρ)
    {τ : ℝ} (hτ : 0 < τ) :
    ‖∫ x, x - radialClip τ x ∂(ν : Measure H099R3)‖ ≤
      ∫ r, max (r - τ) 0 ∂ρ := by
  have hnorm : AEMeasurable (fun x : H099R3 ↦ ‖x‖)
      (ν : Measure H099R3) := continuous_norm.measurable.aemeasurable
  have htailMeas : AEStronglyMeasurable (fun r : ℝ ↦ max (r - τ) 0)
      (Measure.map (fun x : H099R3 ↦ ‖x‖) (ν : Measure H099R3)) := by
    fun_prop
  calc
    ‖∫ x, x - radialClip τ x ∂(ν : Measure H099R3)‖ ≤
        ∫ x, ‖x - radialClip τ x‖ ∂(ν : Measure H099R3) :=
      norm_integral_le_integral_norm _
    _ = ∫ x, max (‖x‖ - τ) 0 ∂(ν : Measure H099R3) := by
      simp_rw [norm_sub_radialClip hτ]
    _ = ∫ r, max (r - τ) 0 ∂ρ := by
      rw [← hρ, integral_map hnorm htailMeas]

/-- The scalar first-moment tail discarded above a threshold tends to zero.
The domination is by the integrable absolute radius. -/
theorem tendsto_integral_radial_tail_zero
    (ρ : Measure ℝ) (hR : Integrable (fun r : ℝ ↦ r) ρ) :
    Tendsto (fun τ : ℝ ↦ ∫ r, max (r - τ) 0 ∂ρ) atTop (nhds 0) := by
  have hlim : Tendsto (fun τ : ℝ ↦ ∫ r, max (r - τ) 0 ∂ρ)
      atTop (nhds (∫ _ : ℝ, (0 : ℝ) ∂ρ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun r : ℝ ↦ ‖r‖)
    · exact Filter.Eventually.of_forall fun τ ↦ by fun_prop
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
      filter_upwards [] with r
      have hmax : 0 ≤ max (r - τ) 0 := le_max_right _ _
      simp only [Real.norm_eq_abs, abs_of_nonneg hmax]
      apply max_le
      · nlinarith [le_abs_self r]
      · exact abs_nonneg r
    · exact hR.norm
    · filter_upwards [] with r
      have heq : (fun τ : ℝ ↦ max (r - τ) 0) =ᶠ[atTop] (fun _ ↦ 0) := by
        filter_upwards [eventually_ge_atTop r] with τ hτ
        exact max_eq_right (sub_nonpos.mpr hτ)
      exact Tendsto.congr' heq.symm tendsto_const_nhds
  simpa using hlim

/-- Under a common integrable radial distribution, weak convergence in
three-space upgrades to convergence of the (unclipped) vector means. -/
theorem tendsto_integral_id_of_weak_of_same_radial_law
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (ρ : Measure ℝ) (hR : Integrable (fun r : ℝ ↦ r) ρ)
    (hν : Tendsto νs atTop (nhds ν))
    (hId : ∀ n, Integrable (fun x : H099R3 ↦ x) (νs n : Measure H099R3))
    (hIdLim : Integrable (fun x : H099R3 ↦ x) (ν : Measure H099R3))
    (hradialSeq : ∀ n, Measure.map (fun x : H099R3 ↦ ‖x‖)
      (νs n : Measure H099R3) = ρ)
    (hradialLim : Measure.map (fun x : H099R3 ↦ ‖x‖)
      (ν : Measure H099R3) = ρ) :
    Tendsto (fun n ↦ ∫ x, x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, x ∂(ν : Measure H099R3))) := by
  apply tendsto_integral_id_of_weak_of_uniform_clipping_tail νs ν hν hId hIdLim
  intro ε hε
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_radial_tail_zero ρ hR) ε hε
  let τ : ℝ := max T 1
  have hτ : 0 < τ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hτT : T ≤ τ := le_max_left _ _
  have htail : ∫ r, max (r - τ) 0 ∂ρ ≤ ε := by
    have hsmall : |∫ r, max (r - τ) 0 ∂ρ| < ε := by
      simpa [Real.dist_eq] using hT τ hτT
    exact (le_abs_self _).trans hsmall.le
  refine ⟨τ, hτ, ?_, ?_⟩
  · intro n
    exact (norm_integral_residual_le_radial_tail (νs n) ρ
      (hradialSeq n) hτ).trans htail
  · exact (norm_integral_residual_le_radial_tail ν ρ hradialLim hτ).trans htail

/-- The mean-convergence bridge in the discretized-radius case: the
approximating radial tails need only be bounded by one integrable reference
law, while the limiting law has exactly that radial distribution. -/
theorem tendsto_integral_id_of_weak_of_radial_tail_domination
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (ρ : Measure ℝ) (hR : Integrable (fun r : ℝ ↦ r) ρ)
    (hν : Tendsto νs atTop (nhds ν))
    (hId : ∀ n, Integrable (fun x : H099R3 ↦ x) (νs n : Measure H099R3))
    (hIdLim : Integrable (fun x : H099R3 ↦ x) (ν : Measure H099R3))
    (hdom : ∀ n (τ : ℝ), 0 < τ →
      (∫ x, max (‖x‖ - τ) 0 ∂(νs n : Measure H099R3)) ≤
        ∫ r, max (r - τ) 0 ∂ρ)
    (hradialLim : Measure.map (fun x : H099R3 ↦ ‖x‖)
      (ν : Measure H099R3) = ρ) :
    Tendsto (fun n ↦ ∫ x, x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, x ∂(ν : Measure H099R3))) := by
  apply tendsto_integral_id_of_weak_of_uniform_clipping_tail νs ν hν hId hIdLim
  intro ε hε
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp
    (tendsto_integral_radial_tail_zero ρ hR) ε hε
  let τ : ℝ := max T 1
  have hτ : 0 < τ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hτT : T ≤ τ := le_max_left _ _
  have htail : ∫ r, max (r - τ) 0 ∂ρ ≤ ε := by
    have hsmall : |∫ r, max (r - τ) 0 ∂ρ| < ε := by
      simpa [Real.dist_eq] using hT τ hτT
    exact (le_abs_self _).trans hsmall.le
  refine ⟨τ, hτ, ?_, (norm_integral_residual_le_radial_tail ν ρ hradialLim hτ).trans htail⟩
  intro n
  calc
    ‖∫ x, x - radialClip τ x ∂(νs n : Measure H099R3)‖ ≤
        ∫ x, ‖x - radialClip τ x‖ ∂(νs n : Measure H099R3) :=
      norm_integral_le_integral_norm _
    _ = ∫ x, max (‖x‖ - τ) 0 ∂(νs n : Measure H099R3) := by
      simp_rw [norm_sub_radialClip hτ]
    _ ≤ ∫ r, max (r - τ) 0 ∂ρ := hdom n τ hτ
    _ ≤ ε := htail

/-- At each fixed threshold, the mean of the clipped vector and the mean
of the original vector determine the clipping bias continuously. -/
theorem tendsto_clipping_bias_of_weak_and_mean_convergence
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (hν : Tendsto νs atTop (nhds ν))
    (hmean : Tendsto (fun n ↦ ∫ x, x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, x ∂(ν : Measure H099R3))))
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun n ↦ ‖(∫ x, radialClip τ x ∂(νs n : Measure H099R3)) -
      ∫ x, x ∂(νs n : Measure H099R3)‖) atTop
      (nhds (‖(∫ x, radialClip τ x ∂(ν : Measure H099R3)) -
        ∫ x, x ∂(ν : Measure H099R3)‖)) := by
  exact ((tendsto_integral_radialClip_of_weak νs ν hν hτ).sub hmean).norm

/-- The centered clipped energy is a weakly continuous functional of a
probability law at every fixed positive threshold. -/
theorem tendsto_centered_radialClip_energy_of_weak
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (hν : Tendsto νs atTop (nhds ν))
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun n ↦ ∫ x, ‖radialClip τ x -
      ∫ y, radialClip τ y ∂(νs n : Measure H099R3)‖ ^ 2
        ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, ‖radialClip τ x -
        ∫ y, radialClip τ y ∂(ν : Measure H099R3)‖ ^ 2
          ∂(ν : Measure H099R3))) := by
  let f : H099R3 →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x ↦ ‖radialClip τ x‖ ^ 2)
      ((continuous_norm.comp (continuous_radialClip τ hτ)).pow 2)
      (τ ^ 2) (by
        intro x
        have hn : ‖radialClip τ x‖ ≤ τ := by
          rw [norm_radialClip hτ]
          exact min_le_right _ _
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [norm_nonneg (radialClip τ x)])
  have htest := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) f
  have hclip := tendsto_integral_radialClip_of_weak νs ν hν hτ
  have hmeansq : Tendsto
      (fun n ↦ ‖∫ x, radialClip τ x ∂(νs n : Measure H099R3)‖ ^ 2)
      atTop (nhds (‖∫ x, radialClip τ x ∂(ν : Measure H099R3)‖ ^ 2)) :=
    hclip.norm.pow 2
  have hvariance (μ : ProbabilityMeasure H099R3) :
      (∫ x, ‖radialClip τ x -
        ∫ y, radialClip τ y ∂(μ : Measure H099R3)‖ ^ 2
          ∂(μ : Measure H099R3)) =
      (∫ x, f x ∂(μ : Measure H099R3)) -
        ‖∫ x, radialClip τ x ∂(μ : Measure H099R3)‖ ^ 2 := by
    have hY : Integrable (fun x : H099R3 ↦ radialClip τ x)
        (μ : Measure H099R3) := integrable_radialClip (by fun_prop) hτ
    have hYsq : Integrable (fun x : H099R3 ↦ ‖radialClip τ x‖ ^ 2)
        (μ : Measure H099R3) := integrable_sq_norm_radialClip (by fun_prop) hτ
    rw [integral_norm_sub_mean_sq (μ : Measure H099R3) _ hY hYsq]
    rfl
  simpa only [hvariance] using htest.sub hmeansq

/-- If finite approximations reproduce both clipping quantities and their
source values converge, then a weak limit reproduces them as well.  This is
the final analytic passage of the all-thresholds proof; the finite geometric
construction and radial discretization are separate inputs. -/
theorem all_thresholds_bias_energy_of_weak_limit
    (νs : ℕ → ProbabilityMeasure H099R3) (ν : ProbabilityMeasure H099R3)
    (hν : Tendsto νs atTop (nhds ν))
    (hmean : Tendsto (fun n ↦ ∫ x, x ∂(νs n : Measure H099R3)) atTop
      (nhds (∫ x, x ∂(ν : Measure H099R3))))
    (sourceBias sourceEnergy : ℝ → ℝ)
    (approxBias approxEnergy : ℕ → ℝ → ℝ)
    (hsourceBias : ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n ↦ approxBias n τ) atTop (nhds (sourceBias τ)))
    (hsourceEnergy : ∀ τ : ℝ, 0 < τ →
      Tendsto (fun n ↦ approxEnergy n τ) atTop (nhds (sourceEnergy τ)))
    (hbias : ∀ n τ, 0 < τ → approxBias n τ =
      ‖(∫ x, radialClip τ x ∂(νs n : Measure H099R3)) -
        ∫ x, x ∂(νs n : Measure H099R3)‖)
    (henergy : ∀ n τ, 0 < τ → approxEnergy n τ =
      ∫ x, ‖radialClip τ x -
        ∫ y, radialClip τ y ∂(νs n : Measure H099R3)‖ ^ 2
          ∂(νs n : Measure H099R3)) :
    ∀ τ : ℝ, 0 < τ →
      sourceBias τ =
        ‖(∫ x, radialClip τ x ∂(ν : Measure H099R3)) -
          ∫ x, x ∂(ν : Measure H099R3)‖ ∧
      sourceEnergy τ =
        ∫ x, ‖radialClip τ x -
          ∫ y, radialClip τ y ∂(ν : Measure H099R3)‖ ^ 2
            ∂(ν : Measure H099R3) := by
  intro τ hτ
  constructor
  · have h := hsourceBias τ hτ
    simp_rw [hbias _ τ hτ] at h
    exact tendsto_nhds_unique h
      (tendsto_clipping_bias_of_weak_and_mean_convergence νs ν hν hmean hτ)
  · have h := hsourceEnergy τ hτ
    simp_rw [henergy _ τ hτ] at h
    exact tendsto_nhds_unique h
      (tendsto_centered_radialClip_energy_of_weak νs ν hν hτ)
