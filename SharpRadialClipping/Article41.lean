import SharpRadialClipping.AttainableClassification
import SharpRadialClipping.ConvexHullExact
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact attainable-set statement in the form of the article

The preceding module gives a radius-parametric characterization.  Here we
isolate the excluded curved upper arc, including its left endpoint.
-/

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

universe u v

/-- The curved part of the upper boundary, with its left endpoint included
and its right endpoint `(1,0)` omitted. -/
def curvedUpperArc (p : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ r : ℝ, 1 < r ∧ r ≤ p / (p - 1) ∧
    z = (rareEnergy p r, rareBias p r)}

/-- The same excluded arc in the article's displayed energy coordinates. -/
def explicitCurvedUpperArc (p : ℝ) : Set (ℝ × ℝ) :=
  {z | criticalEnergy p ≤ z.1 ∧ z.1 < 1 ∧
    z.2 = z.1 ^ ((p - 1) / p) - z.1}

theorem curvedUpperArc_eq_explicitCurvedUpperArc
    {p : ℝ} (hp : 1 < p) :
    curvedUpperArc p = explicitCurvedUpperArc p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  let R : ℝ := p / (p - 1)
  have hRpos : 0 < R := div_pos hp0 hpm
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨r, hr1, hrR, rfl⟩
    have hrpos : 0 < r := zero_lt_one.trans hr1
    change criticalEnergy p ≤ rareEnergy p r ∧
      rareEnergy p r < 1 ∧
      rareBias p r = (rareEnergy p r) ^ ((p - 1) / p) - rareEnergy p r
    refine ⟨?_, ?_, rareBias_eq_energy_rpow_sub_energy hp0 hrpos⟩
    · rw [← rareEnergy_criticalRadius_eq hp]
      dsimp [rareEnergy, R] at *
      exact Real.rpow_le_rpow_of_nonpos hrpos hrR (by linarith : -p ≤ 0)
    · dsimp [rareEnergy]
      have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : ℝ) < 1)
        hr1 (by linarith : -p < 0)
      simpa using h
  · intro z hz
    rcases z with ⟨w, d⟩
    change criticalEnergy p ≤ w ∧ w < 1 ∧
      d = w ^ ((p - 1) / p) - w at hz
    rcases hz with ⟨hwcrit, hw1, hd⟩
    have hcritpos : 0 < criticalEnergy p := by
      dsimp [criticalEnergy]
      exact Real.rpow_pos_of_pos (div_pos hpm hp0) _
    have hwpos : 0 < w := lt_of_lt_of_le hcritpos hwcrit
    let r : ℝ := w ^ (-1 / p)
    have hrpos : 0 < r := Real.rpow_pos_of_pos hwpos _
    have henergy : rareEnergy p r = w := by
      dsimp [rareEnergy, r]
      rw [← Real.rpow_mul hwpos.le]
      have hexp : (-1 / p) * (-p) = 1 := by field_simp [hp0.ne']
      rw [hexp, Real.rpow_one]
    have hr1 : 1 < r := by
      have h := Real.rpow_lt_rpow_iff_of_neg
        hrpos (by norm_num : (0 : ℝ) < 1) (by linarith : -p < 0)
      have hpow : r ^ (-p) < (1 : ℝ) ^ (-p) := by
        change r ^ (-p) = w at henergy
        rw [henergy]
        simpa using hw1
      exact h.mp hpow
    have hrR : r ≤ R := by
      have h := Real.rpow_le_rpow_iff_of_neg hRpos hrpos
        (by linarith : -p < 0)
      have hpow : R ^ (-p) ≤ r ^ (-p) := by
        rw [← rareEnergy_criticalRadius_eq hp] at hwcrit
        change R ^ (-p) ≤ w at hwcrit
        change r ^ (-p) = w at henergy
        rw [henergy]
        exact hwcrit
      exact h.mp hpow
    refine ⟨r, hr1, hrR, ?_⟩
    apply Prod.ext
    · exact henergy.symm
    · rw [rareBias_eq_energy_rpow_sub_energy hp0 hrpos, henergy]
      exact hd

/-- A support line tangent to the curved branch bounds the energy at its
bias level.  This is the scalar step needed to recover the attainable set
from the closed convex hull. -/
theorem energy_le_rareEnergy_of_signedSupportRegion
    {p r w d : ℝ} (hp : 1 < p) (hr1 : 1 < r)
    (hrR : r < p / (p - 1)) (hd : d = rareBias p r)
    (hmem : (w, d) ∈ signedSupportRegion p) :
    w ≤ rareEnergy p r := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hden : 0 < p - (p - 1) * r := by
    apply (lt_div_iff₀ hpm).mp at hrR
    nlinarith
  let α : ℝ := p / (p - (p - 1) * r)
  have hαpos : 0 < α := div_pos hp0 hden
  have hreg : p * 1 < α := by
    dsimp [α]
    apply (lt_div_iff₀ hden).2
    have hdenlt : p - (p - 1) * r < 1 := by
      nlinarith [mul_lt_mul_of_pos_left hr1 hpm]
    nlinarith
  have hrstar : r_star α 1 p = r := by
    dsimp [r_star, α]
    field_simp [ne_of_gt hp0, ne_of_gt hpm, ne_of_gt hden]
    ring
  have hF : F α 1 p r = K_p α 1 p := by
    rw [← hrstar, F_at_r_star (by norm_num) hp hreg,
      K_p_eq_criticalValue (by norm_num) hp hreg]
  have hsupport : α * rareBias p r + rareEnergy p r = K_p α 1 p := by
    have hcurve := rareCurve_support_eq_F (p := p) (α := α) (β := 1)
      (r := r) hr1.le
    rw [hF] at hcurve
    simpa [add_comm, mul_comm] using hcurve
  have hform : signedSupportFormula α 1 p = K_p α 1 p := by
    simp [signedSupportFormula, K_p]
  have hbound := hmem α 1
  rw [hform, hd, ← hsupport] at hbound
  nlinarith

/-- On the flat top face, the energy cannot pass the transition energy.
This is the right derivative of the support function at the pure-bias
direction. -/
theorem energy_le_criticalEnergy_of_signedSupportRegion_maxBias
    {p w : ℝ} (hp : 1 < p)
    (hmem : (w, c_p p) ∈ signedSupportRegion p) :
    w ≤ criticalEnergy p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  let f : ℝ → ℝ := fun t => (1 - t) ^ (1 - p)
  have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub (1 : ℝ)
  have hf : HasDerivAt f (p - 1) 0 := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ (1 - p))
        ((1 - p) * (1 : ℝ) ^ ((1 - p) - 1)) 1 :=
      Real.hasDerivAt_rpow_const (Or.inl (by norm_num))
    have hpow' : HasDerivAt (fun x : ℝ => x ^ (1 - p))
        ((1 - p) * (1 : ℝ) ^ ((1 - p) - 1)) (1 - (0 : ℝ)) := by
      simpa using hpow
    have h := hpow'.comp 0 hinner
    simpa [f, Function.comp_def] using h
  have hlimit : Filter.Tendsto
      (fun t : ℝ => c_p p * ((f t - 1) / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (c_p p * (p - 1))) := by
    have h := hf.tendsto_slope_zero_right.const_mul (c_p p)
    convert h using 1
    · ext t
      simp [f, smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      w ≤ c_p p * ((f t - 1) / t) := by
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
      self_mem_nhdsWithin
    have htlim : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 / p :=
      (eventually_lt_nhds (div_pos zero_lt_one hp0)).filter_mono nhdsWithin_le_nhds
    filter_upwards [htpos, htlim] with t ht ht1
    have hpt : p * t < 1 := by
      have := (lt_div_iff₀ hp0).mp ht1
      nlinarith
    have ht1' : t < 1 := by nlinarith
    have hone : 0 < 1 - t := by linarith
    have hform : signedSupportFormula 1 t p = c_p p * f t := by
      have hreg : ¬(1 : ℝ) ≤ p * t := not_le_of_gt hpt
      simp only [signedSupportFormula, if_neg (not_lt.mpr ht.le), if_neg hreg,
        one_mul]
      dsimp [f]
      rw [show 1 - p = -(p - 1) by ring, Real.rpow_neg hone.le]
      simp [div_eq_mul_inv]
    have hs := hmem 1 t
    rw [hform] at hs
    have hmul : w * t ≤ c_p p * (f t - 1) := by nlinarith [hs]
    have hdiv : w ≤ c_p p * (f t - 1) / t :=
      (le_div_iff₀ ht).2 (by nlinarith [hmul])
    simpa only [mul_div_assoc] using hdiv
  have hw : w ≤ c_p p * (p - 1) := ge_of_tendsto hlimit hbound
  have hc : c_p p * (p - 1) = criticalEnergy p := by
    have hpow : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
      calc
        (p - 1) ^ p = (p - 1) ^ ((p - 1) + 1) := by congr 1; ring
        _ = (p - 1) ^ (p - 1) * (p - 1) := by
          rw [Real.rpow_add hpm, Real.rpow_one]
    unfold c_p criticalEnergy
    rw [Real.div_rpow hpm.le hp0.le, hpow]
    ring
  simpa [hc] using hw

/-- No point of the curved upper arc is actually attainable. -/
theorem curvedUpperArc_disjoint_articleAttainablePairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    Disjoint (curvedUpperArc p) (articleAttainablePairs.{u, v} H p τ) := by
  apply Set.disjoint_left.mpr
  intro z hzarc hzatt
  rcases hzarc with ⟨r, hr1, hrR, rfl⟩
  rcases lt_or_eq_of_le hrR with hrlt | hre
  · exact rareCurve_open_arc_disjoint_attainable hp hp2 hτ hr1 hrlt hzatt
  · subst r
    rcases hzatt with ⟨law, hpair⟩
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    have hD : stochasticClippingRatio law.μ 1 0 p τ law.X = c_p p := by
      have := congrArg Prod.snd hpair
      have hRone : 1 ≤ p / (p - 1) := by
        have hpm : 0 < p - 1 := sub_pos.mpr hp
        exact (le_div_iff₀ hpm).2 (by linarith)
      have hRstar : r_star 1 0 p = p / (p - 1) := by simp [r_star]
      have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := 0)
        (r := p / (p - 1)) hRone
      rw [← hRstar, F_at_r_star (by norm_num) hp (by norm_num)] at hcurve
      have hcrit := criticalValue_closed_form (α := 1) (β := 0)
        (p := p) (by norm_num) hp (by norm_num)
      have hbias : rareBias p (p / (p - 1)) = c_p p := by
        simpa [hRstar] using hcurve.trans (by simpa using hcrit)
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair, hbias] using this
    have hV : stochasticClippingRatio law.μ 0 1 p τ law.X =
        rareEnergy p (p / (p - 1)) := by
      have := congrArg Prod.fst hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
    have hstrict := maxBias_energy_lt law.μ hp hp2 hτ law.X law.memLp
      law.moment_pos hD
    rw [hV] at hstrict
    exact (lt_irrefl _) hstrict

/-- Removing the exposed curved arc from the closed support region leaves
exactly the radius-parametric attainable region. -/
theorem signedSupportRegion_diff_curvedUpperArc_eq_rareEnvelopeRegion
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    signedSupportRegion p \ curvedUpperArc p = rareEnvelopeRegion p := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases z with ⟨w, d⟩
    have hs : (w, d) ∈ signedSupportRegion p := hz.1
    have hnot : (w, d) ∉ curvedUpperArc p := hz.2
    have hw0 : 0 ≤ w := by
      have h := hs 0 (-1)
      simp [signedSupportFormula] at h
      linarith
    have hd0 : 0 ≤ d := by
      have h := hs (-1) 0
      simp [signedSupportFormula] at h
      linarith
    have hw1 : w ≤ 1 := by
      have h := hs 0 1
      have hf : signedSupportFormula 0 1 p = 1 := by
        simp [signedSupportFormula, show (0 : ℝ) ≤ p by linarith]
      rw [hf] at h
      linarith
    have hdc : d ≤ c_p p := by
      have h := hs 1 0
      have hf : signedSupportFormula 1 0 p = c_p p := by
        simp [signedSupportFormula]
      rw [hf] at h
      linarith
    by_cases hdz : d = 0
    · exact Or.inl ⟨hdz, hw0, hw1⟩
    right
    have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hdz)
    obtain ⟨r, hr1, hrR, hrd⟩ :=
      exists_rareRadius_of_bias_le_c_p hp hd0 hdc
    have hr1' : 1 < r := by
      rcases eq_or_lt_of_le hr1 with heq | hlt
      · rw [← heq] at hrd
        simp [rareBias] at hrd
        linarith
      · exact hlt
    have hwle : w ≤ rareEnergy p r := by
      rcases lt_or_eq_of_le hrR with hrlt | hre
      · exact energy_le_rareEnergy_of_signedSupportRegion hp hr1' hrlt
          hrd.symm hs
      · subst r
        rw [rareEnergy_criticalRadius_eq hp]
        rw [← hrd] at hs
        have hcritical : rareBias p (p / (p - 1)) = c_p p := by
          exact rareBias_criticalRadius_eq hp
        rw [hcritical] at hs
        exact energy_le_criticalEnergy_of_signedSupportRegion_maxBias hp hs
    have hwlt : w < rareEnergy p r := by
      apply lt_of_le_of_ne hwle
      intro heq
      apply hnot
      exact ⟨r, hr1', hrR, by ext <;> simp [heq, hrd]⟩
    exact ⟨r, hr1', hrR, hrd, hw0, hwlt⟩
  · intro z hz
    have harticle : z ∈ articleAttainablePairs.{0, 0} ℝ p 1 := by
      have hτ : 0 < (1 : ℝ) := by norm_num
      rw [articleAttainablePairs_eq_rareEnvelopeRegion (H := ℝ) hp hp2 hτ]
      exact hz
    have hs : z ∈ signedSupportRegion p := by
      have hτ : 0 < (1 : ℝ) := by norm_num
      have hclosure : z ∈ closedConvexHull ℝ
          (articleAttainablePairs.{0, 0} ℝ p 1) :=
        subset_closedConvexHull harticle
      rw [closedConvexHull_articleAttainablePairs_eq_signedSupportRegion
        (H := ℝ) hp hp2 hτ] at hclosure
      exact hclosure
    have hnot : z ∉ curvedUpperArc p := by
      intro harc
      exact Set.disjoint_left.mp
        (curvedUpperArc_disjoint_articleAttainablePairs
          (H := ℝ) hp hp2 (by norm_num : 0 < (1 : ℝ)))
          harc harticle
    exact ⟨hs, hnot⟩

/-- Theorem 4.1 in the geometric form: the attainable set is exactly the
closed convex hull minus the exposed curved upper arc. -/
theorem articleAttainablePairs_eq_closedConvexHull_diff_curvedUpperArc
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ =
      closedConvexHull ℝ (articleAttainablePairs.{u, v} H p τ) \ curvedUpperArc p := by
  rw [closedConvexHull_articleAttainablePairs_eq_signedSupportRegion hp hp2 hτ]
  rw [signedSupportRegion_diff_curvedUpperArc_eq_rareEnvelopeRegion hp hp2]
  exact articleAttainablePairs_eq_rareEnvelopeRegion hp hp2 hτ

/-- Theorem 4.1 with the excluded arc written in the energy coordinate
used in the article. -/
theorem articleAttainablePairs_eq_closedConvexHull_diff_explicitCurvedUpperArc
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ =
      closedConvexHull ℝ (articleAttainablePairs.{u, v} H p τ) \
        explicitCurvedUpperArc p := by
  rw [← curvedUpperArc_eq_explicitCurvedUpperArc hp]
  exact articleAttainablePairs_eq_closedConvexHull_diff_curvedUpperArc hp hp2 hτ

/-- The complete explicit article formula: the attainable set is the region
below the piecewise boundary `F_p`, except for its curved upper arc. -/
theorem articleAttainablePairs_eq_closedHullRegion_diff_explicitCurvedUpperArc
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ =
      closedHullRegion p \ explicitCurvedUpperArc p := by
  rw [← closedConvexHull_articleAttainablePairs_eq_closedHullRegion
    (H := H) hp hp2 hτ]
  exact articleAttainablePairs_eq_closedConvexHull_diff_explicitCurvedUpperArc hp hp2 hτ
