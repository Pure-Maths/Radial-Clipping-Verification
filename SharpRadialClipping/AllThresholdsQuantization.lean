import SharpRadialClipping.AllThresholdsLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Radial discretization for the all-thresholds theorem

The input norm is clipped at `n + 1` and rounded down to the grid of mesh
`1 / (n + 1)`.  Each discretized norm has finite range and never exceeds the
original nonnegative norm.
-/

noncomputable section

/-- Downward radial quantization with a finite range at each scale. -/
def radialGrid (n : ℕ) (r : ℝ) : ℝ :=
  (⌊((n + 1 : ℕ) : ℝ) * min r (n + 1)⌋₊ : ℝ) / (n + 1)

theorem radialGrid_nonneg (n : ℕ) (r : ℝ) : 0 ≤ radialGrid n r := by
  unfold radialGrid
  positivity

/-- Downward quantization does not increase a nonnegative radius. -/
theorem radialGrid_le (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    radialGrid n r ≤ r := by
  let m : ℝ := (n + 1 : ℕ)
  have hm : 0 < m := by positivity
  have hmin : 0 ≤ min r m := le_min hr hm.le
  have hfloor : (⌊m * min r m⌋₊ : ℝ) ≤ m * min r m :=
    Nat.floor_le (mul_nonneg hm.le hmin)
  calc
    radialGrid n r = (⌊m * min r m⌋₊ : ℝ) / m := by simp [radialGrid, m]
    _ ≤ min r m := (div_le_iff₀ hm).2 (by simpa [mul_comm] using hfloor)
    _ ≤ r := min_le_left _ _

/-- At a fixed scale the set of possible quantized radii is finite. -/
theorem radialGrid_finite_range (n : ℕ) :
    {radialGrid n r | (r : ℝ) (_hr : 0 ≤ r)}.Finite := by
  let m : ℝ := (n + 1 : ℕ)
  have hm : 0 < m := by positivity
  have hbound (r : ℝ) (hr : 0 ≤ r) :
      ⌊m * min r m⌋₊ ≤ (n + 1) ^ 2 := by
    have hmin : 0 ≤ min r m := le_min hr hm.le
    have hmul : m * min r m ≤ m * m := mul_le_mul_of_nonneg_left (min_le_right _ _) hm.le
    have hcast : (⌊m * min r m⌋₊ : ℝ) ≤ ((n + 1) ^ 2 : ℕ) := by
      calc
        (⌊m * min r m⌋₊ : ℝ) ≤ m * min r m := Nat.floor_le (mul_nonneg hm.le hmin)
        _ ≤ m * m := hmul
        _ = ((n + 1) ^ 2 : ℕ) := by simp [m, pow_two]
    exact_mod_cast hcast
  have hfin : (Set.Iic ((n + 1) ^ 2) : Set ℕ).Finite := Set.finite_Iic _
  have himage : ((fun k : ℕ ↦ (k : ℝ) / m) ''
      (Set.Iic ((n + 1) ^ 2) : Set ℕ)).Finite := hfin.image _
  apply himage.subset
  rintro x ⟨r, hr, rfl⟩
  exact ⟨⌊m * min r m⌋₊, hbound r hr, by simp [radialGrid, m]⟩

/-- Pointwise error: one grid cell plus the amount cut off by truncation. -/
theorem radialGrid_error_le (n : ℕ) {r : ℝ} (_hr : 0 ≤ r) :
    r - radialGrid n r ≤ 1 / ((n + 1 : ℕ) : ℝ) +
      max (r - (n + 1)) 0 := by
  let m : ℝ := (n + 1 : ℕ)
  have hm : 0 < m := by positivity
  have hfloor := Nat.lt_floor_add_one (m * min r m)
  have hgap : min r m < radialGrid n r + 1 / m := by
    have h := div_lt_div_of_pos_right hfloor hm
    have hmne : m ≠ 0 := hm.ne'
    calc
      min r m = (m * min r m) / m := by field_simp
      _ < ((⌊m * min r m⌋₊ : ℝ) + 1) / m := h
      _ = radialGrid n r + 1 / m := by
        simp [radialGrid, m, add_div]
  by_cases hle : r ≤ m
  · rw [min_eq_left hle] at hgap
    have hmax : max (r - (n + 1)) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (by simpa [m] using hle))
    rw [hmax, add_zero]
    simpa [m] using (show r - radialGrid n r ≤ 1 / m by linarith)
  · have hge : m ≤ r := le_of_not_ge hle
    rw [min_eq_right hge] at hgap
    have hmax : max (r - (n + 1)) 0 = r - (n + 1) :=
      max_eq_left (sub_nonneg.mpr (by simpa [m] using hge))
    rw [hmax]
    have hdesired : r - radialGrid n r ≤ 1 / m + (r - m) := by linarith
    simpa [m] using hdesired

/-- At each fixed nonnegative radius the quantized radius converges to it. -/
theorem tendsto_radialGrid (r : ℝ) (hr : 0 ≤ r) :
    Filter.Tendsto (fun n : ℕ ↦ radialGrid n r) Filter.atTop (nhds r) := by
  have hevent : ∀ᶠ n : ℕ in Filter.atTop, r ≤ ((n + 1 : ℕ) : ℝ) := by
    have hlim : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      exact tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
    exact hlim.eventually_ge_atTop r
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      r - radialGrid n r ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    filter_upwards [hevent] with n hn
    have he := radialGrid_error_le n hr
    have hmax : max (r - (n + 1)) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (by simpa using hn))
    simpa [hmax] using he
  have hlim : Filter.Tendsto (fun n : ℕ ↦ r - radialGrid n r)
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n ↦
      sub_nonneg.mpr (radialGrid_le n hr)) hupper
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have h := (tendsto_const_nhds (x := r)).sub hlim
  convert h using 1 <;> simp

theorem measurable_radialGrid (n : ℕ) : Measurable (radialGrid n) := by
  unfold radialGrid
  fun_prop

/-- The source vector with the same direction and a discretized radius. -/
def radialQuantized {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (n : ℕ) (x : H) : H := (radialGrid n ‖x‖ / ‖x‖) • x

theorem norm_radialQuantized
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (n : ℕ) (x : H) : ‖radialQuantized n x‖ = radialGrid n ‖x‖ := by
  by_cases hx : x = 0
  · have hzero : radialGrid n 0 = 0 := by
      simp [radialGrid, min_eq_left (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity)]
    simp [radialQuantized, hx, hzero]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [radialQuantized, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (radialGrid_nonneg n _) (norm_nonneg x))]
    exact div_mul_cancel₀ _ hn

theorem norm_radialQuantized_le
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (n : ℕ) (x : H) : ‖radialQuantized n x‖ ≤ ‖x‖ := by
  rw [norm_radialQuantized]
  exact radialGrid_le n (norm_nonneg x)

/-- In any source space, the discretized vectors have only finitely many
possible norms. -/
theorem finite_range_norm_radialQuantized
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (n : ℕ) :
    (Set.range fun x : H ↦ ‖radialQuantized n x‖).Finite := by
  apply (radialGrid_finite_range n).subset
  rintro r ⟨x, rfl⟩
  exact ⟨‖x‖, norm_nonneg x, (norm_radialQuantized n x).symm⟩

theorem measurable_radialQuantized
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] (n : ℕ) :
    Measurable (radialQuantized (H := H) n) := by
  unfold radialQuantized
  exact (((measurable_radialGrid n).comp measurable_norm).div measurable_norm).smul
    measurable_id

theorem tendsto_radialQuantized
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : H) : Filter.Tendsto (fun n : ℕ ↦ radialQuantized n x)
      Filter.atTop (nhds x) := by
  by_cases hx : x = 0
  · simp [radialQuantized, hx]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hq := tendsto_radialGrid ‖x‖ (norm_nonneg x)
    have hs : Filter.Tendsto (fun n : ℕ ↦ radialGrid n ‖x‖ / ‖x‖)
        Filter.atTop (nhds (1 : ℝ)) := by
      simpa [hn] using hq.div_const ‖x‖
    simpa [radialQuantized] using hs.smul (tendsto_const_nhds (x := x))

/-- Radial grid approximation converges in `L¹` for an integrable random
vector.  The domination follows from the fact that rounding never increases
the radius. -/
theorem tendsto_integral_radialQuantized_error_zero
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.Measure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : MeasureTheory.Integrable X μ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, ‖radialQuantized n (X ω) - X ω‖ ∂μ)
      Filter.atTop (nhds (0 : ℝ)) := by
  open MeasureTheory in
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, ‖radialQuantized n (X ω) - X ω‖ ∂μ)
      Filter.atTop (nhds (∫ _ : Ω, (0 : ℝ) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun ω ↦ 2 * ‖X ω‖)
    · exact Filter.Eventually.of_forall fun n ↦ by
        have hf : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖ / ‖X ω‖) :=
          ((measurable_radialGrid n).comp hXm.norm).div hXm.norm
        have hXn : MeasureTheory.AEStronglyMeasurable
            (fun ω : Ω ↦ radialQuantized n (X ω)) μ := by
          exact hf.aestronglyMeasurable.smul hX.aestronglyMeasurable
        exact (hXn.sub hX.aestronglyMeasurable).norm
    · filter_upwards [] with n
      filter_upwards [] with ω
      have hbound : ‖radialQuantized n (X ω) - X ω‖ ≤
          2 * ‖X ω‖ := by
        calc
          ‖radialQuantized n (X ω) - X ω‖ ≤
              ‖radialQuantized n (X ω)‖ + ‖X ω‖ := norm_sub_le _ _
          _ ≤ 2 * ‖X ω‖ := by
            linarith [norm_radialQuantized_le n (X ω)]
      simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound
    · exact hX.norm.const_mul 2
    · filter_upwards [] with ω
      have h := (tendsto_radialQuantized (X ω)).sub
        (tendsto_const_nhds (x := X ω))
      simpa using h.norm
  simpa using hlim

/-- Each radial discretization remains integrable under the original
first-moment hypothesis. -/
theorem integrable_radialQuantized_comp
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.Measure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : MeasureTheory.Integrable X μ) (n : ℕ) :
    MeasureTheory.Integrable (fun ω ↦ radialQuantized n (X ω)) μ := by
  have hf : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖ / ‖X ω‖) :=
    ((measurable_radialGrid n).comp hXm.norm).div hXm.norm
  have hXn : MeasureTheory.AEStronglyMeasurable
      (fun ω : Ω ↦ radialQuantized n (X ω)) μ := by
    exact hf.aestronglyMeasurable.smul hX.aestronglyMeasurable
  apply MeasureTheory.Integrable.mono' hX.norm hXn
  exact Filter.Eventually.of_forall fun ω ↦ norm_radialQuantized_le n (X ω)

/-- The untruncated vector means converge along the radial discretization. -/
theorem tendsto_integral_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.Measure Ω) (X : Ω → H)
    (hXm : Measurable X) (hX : MeasureTheory.Integrable X μ) :
    Filter.Tendsto (fun n : ℕ ↦ ∫ ω, radialQuantized n (X ω) ∂μ)
      Filter.atTop (nhds (∫ ω, X ω ∂μ)) := by
  have hbound (n : ℕ) :
      ‖(∫ ω, radialQuantized n (X ω) ∂μ) - ∫ ω, X ω ∂μ‖ ≤
        ∫ ω, ‖radialQuantized n (X ω) - X ω‖ ∂μ := by
    rw [← MeasureTheory.integral_sub (integrable_radialQuantized_comp μ X hXm hX n) hX]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hzero : Filter.Tendsto
      (fun n : ℕ ↦ ‖(∫ ω, radialQuantized n (X ω) ∂μ) - ∫ ω, X ω ∂μ‖)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n ↦ norm_nonneg _) hbound
      (tendsto_integral_radialQuantized_error_zero μ X hXm hX)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hzero

/-- At a fixed clipping threshold, the clipped means of the radially
quantized observations converge to the clipped mean of the original law. -/
theorem tendsto_integral_radialClip_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (X : Ω → H) (hXm : Measurable X)
    (hX : MeasureTheory.Integrable X μ)
    {τ : ℝ} (hτ : 0 < τ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, radialClip τ (radialQuantized n (X ω)) ∂μ)
      Filter.atTop (nhds (∫ ω, radialClip τ (X ω) ∂μ)) := by
  open MeasureTheory in
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : Ω ↦ τ)
  · exact Filter.Eventually.of_forall fun n ↦ by
      have hf : Measurable (fun ω : Ω ↦ radialGrid n ‖X ω‖ / ‖X ω‖) :=
        ((measurable_radialGrid n).comp hXm.norm).div hXm.norm
      have hXn : MeasureTheory.AEStronglyMeasurable
          (fun ω : Ω ↦ radialQuantized n (X ω)) μ := by
        exact hf.aestronglyMeasurable.smul hX.aestronglyMeasurable
      exact (continuous_radialClip τ hτ).comp_aestronglyMeasurable hXn
  · filter_upwards [] with n
    filter_upwards [] with ω
    rw [norm_radialClip hτ]
    exact min_le_right _ _
  · exact integrable_const τ
  · filter_upwards [] with ω
    exact (continuous_radialClip τ hτ).tendsto _ |>.comp
      (tendsto_radialQuantized (X ω))

/-- The clipping bias of the discretized source law converges at every
fixed threshold. -/
theorem tendsto_bias_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (X : Ω → H) (hXm : Measurable X)
    (hX : MeasureTheory.Integrable X μ)
    {τ : ℝ} (hτ : 0 < τ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ‖(∫ ω, radialClip τ (radialQuantized n (X ω)) ∂μ) -
        ∫ ω, radialQuantized n (X ω) ∂μ‖)
      Filter.atTop
      (nhds (‖(∫ ω, radialClip τ (X ω) ∂μ) - ∫ ω, X ω ∂μ‖)) := by
  exact ((tendsto_integral_radialClip_radialQuantized μ X hXm hX hτ).sub
    (tendsto_integral_radialQuantized μ X hXm hX)).norm

/-- The clipped second moment of the discretized source law converges
without requiring a second moment of the original vector. -/
theorem tendsto_clipped_second_moment_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (X : Ω → H) (hXm : Measurable X)
    (hX : MeasureTheory.Integrable X μ)
    {τ : ℝ} (hτ : 0 < τ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, ‖radialClip τ (radialQuantized n (X ω))‖ ^ 2 ∂μ)
      Filter.atTop (nhds (∫ ω, ‖radialClip τ (X ω)‖ ^ 2 ∂μ)) := by
  open MeasureTheory in
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ : Ω ↦ τ ^ 2)
  · exact Filter.Eventually.of_forall fun n ↦ by
      have hXn := integrable_radialQuantized_comp μ X hXm hX n
      exact ((continuous_norm.comp (continuous_radialClip τ hτ)).pow 2).comp_aestronglyMeasurable
        hXn.aestronglyMeasurable
  · filter_upwards [] with n
    filter_upwards [] with ω
    have hnorm : ‖radialClip τ (radialQuantized n (X ω))‖ ≤ τ := by
      rw [norm_radialClip hτ]
      exact min_le_right _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (radialClip τ (radialQuantized n (X ω)))]
  · exact integrable_const (τ ^ 2)
  · filter_upwards [] with ω
    have h := (continuous_radialClip τ hτ).tendsto _ |>.comp
      (tendsto_radialQuantized (X ω))
    exact h.norm.pow 2

/-- Consequently the centered clipping energy of the discretized source
law converges at each fixed threshold. -/
theorem tendsto_centered_energy_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → H) (hXm : Measurable X)
    (hX : MeasureTheory.Integrable X μ)
    {τ : ℝ} (hτ : 0 < τ) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω,
        ‖radialClip τ (radialQuantized n (X ω)) -
          ∫ ξ, radialClip τ (radialQuantized n (X ξ)) ∂μ‖ ^ 2 ∂μ)
      Filter.atTop
      (nhds (∫ ω, ‖radialClip τ (X ω) -
        ∫ ξ, radialClip τ (X ξ) ∂μ‖ ^ 2 ∂μ)) := by
  open MeasureTheory in
  have hsecond := tendsto_clipped_second_moment_radialQuantized μ X hXm hX hτ
  have hmean := tendsto_integral_radialClip_radialQuantized μ X hXm hX hτ
  have hmeansq := hmean.norm.pow 2
  have hvar (Y : Ω → H) (hY : Integrable Y μ) :
      (∫ ω, ‖radialClip τ (Y ω) -
        ∫ ξ, radialClip τ (Y ξ) ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖radialClip τ (Y ω)‖ ^ 2 ∂μ) -
        ‖∫ ξ, radialClip τ (Y ξ) ∂μ‖ ^ 2 := by
    have hclip : Integrable (fun ω ↦ radialClip τ (Y ω)) μ :=
      integrable_radialClip hY.1 hτ
    have hsq : Integrable (fun ω ↦ ‖radialClip τ (Y ω)‖ ^ 2) μ :=
      integrable_sq_norm_radialClip hY.1 hτ
    exact integral_norm_sub_mean_sq μ _ hclip hsq
  simp_rw [hvar _ (integrable_radialQuantized_comp μ X hXm hX _)]
  rw [hvar X hX]
  exact hsecond.sub hmeansq

/-- The laws of the quantized radii converge weakly to the original radial
law.  This is the law-level counterpart of pointwise radial convergence. -/
theorem tendsto_radial_law_radialQuantized
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : MeasureTheory.ProbabilityMeasure Ω) (X : Ω → H)
    (hXm : Measurable X) :
    let ρn : ℕ → MeasureTheory.ProbabilityMeasure ℝ := fun n ↦
      ⟨MeasureTheory.Measure.map (fun ω ↦ radialGrid n ‖X ω‖)
        (μ : MeasureTheory.Measure Ω),
        MeasureTheory.Measure.isProbabilityMeasure_map
          ((measurable_radialGrid n).comp hXm.norm).aemeasurable⟩
    let ρ : MeasureTheory.ProbabilityMeasure ℝ :=
      ⟨MeasureTheory.Measure.map (fun ω ↦ ‖X ω‖)
        (μ : MeasureTheory.Measure Ω),
        MeasureTheory.Measure.isProbabilityMeasure_map hXm.norm.aemeasurable⟩
    Filter.Tendsto ρn Filter.atTop (nhds ρ) := by
  dsimp only
  apply MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hlim : Filter.Tendsto
      (fun n : ℕ ↦ ∫ ω, f (radialGrid n ‖X ω‖) ∂(μ : MeasureTheory.Measure Ω))
      Filter.atTop
      (nhds (∫ ω, f ‖X ω‖ ∂(μ : MeasureTheory.Measure Ω))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : Ω ↦ ‖f‖)
    · exact Filter.Eventually.of_forall fun n ↦
        (f.continuous.measurable.comp
          ((measurable_radialGrid n).comp hXm.norm)).aestronglyMeasurable
    · filter_upwards [] with n
      filter_upwards [] with ω
      exact f.norm_coe_le_norm _
    · exact MeasureTheory.integrable_const ‖f‖
    · filter_upwards [] with ω
      exact f.continuous.tendsto _ |>.comp
        (tendsto_radialGrid ‖X ω‖ (norm_nonneg (X ω)))
  have hmap (n : ℕ) :
      (∫ r, f r ∂MeasureTheory.Measure.map
        (fun ω ↦ radialGrid n ‖X ω‖) (μ : MeasureTheory.Measure Ω)) =
      ∫ ω, f (radialGrid n ‖X ω‖) ∂(μ : MeasureTheory.Measure Ω) := by
    exact MeasureTheory.integral_map
      (((measurable_radialGrid n).comp hXm.norm).aemeasurable)
      f.continuous.measurable.aestronglyMeasurable
  have hmapLim :
      (∫ r, f r ∂MeasureTheory.Measure.map
        (fun ω ↦ ‖X ω‖) (μ : MeasureTheory.Measure Ω)) =
      ∫ ω, f ‖X ω‖ ∂(μ : MeasureTheory.Measure Ω) := by
    exact MeasureTheory.integral_map hXm.norm.aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  change Filter.Tendsto
    (fun n : ℕ ↦ ∫ r, f r ∂MeasureTheory.Measure.map
      (fun ω ↦ radialGrid n ‖X ω‖) (μ : MeasureTheory.Measure Ω))
    Filter.atTop
    (nhds (∫ r, f r ∂MeasureTheory.Measure.map
      (fun ω ↦ ‖X ω‖) (μ : MeasureTheory.Measure Ω)))
  simpa only [hmap, hmapLim] using hlim
