import H099.AttainableP1
import H099.SignedSupport

/-!
# Exact attainable-set theorem for `1 < p ≤ 2`

This module develops the two-atom witnesses used in the converse direction
of the article's exact attainable-set theorem.  The first result below
computes their normalized pair for an arbitrary real moment exponent.
-/

open MeasureTheory ProbabilityTheory
open unitInterval

noncomputable section

universe u v

variable {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The `p`th norm moment of the one-nonzero-atom Bernoulli law. -/
lemma p1SingleAtom_rpow_moment
    {a τ q p : ℝ} (ha : 1 ≤ a) (hτ : 0 < τ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) {e : H} (he : ‖e‖ = 1)
    (hp : 0 < p) :
    (∫ b, ‖p1SingleAtom a τ e b‖ ^ p ∂
      bernoulliMeasure (ULift.up true) (ULift.up false)
        (⟨q, hq, hq1⟩ : I)) = q * (a * τ) ^ p := by
  rw [integral_bernoulliMeasure,
    p1SingleAtom_norm_true (by linarith) hτ.le he,
    p1SingleAtom_norm_false]
  rw [Real.zero_rpow hp.ne']
  simp [smul_eq_mul]

/-- For any `1 < p`, a law with one clipped atom and one zero atom has the
following energy--bias pair.  In particular, the bias is independent of the
Bernoulli mass, while the energy ranges strictly below the rare-curve energy. -/
theorem oneAtom_biasEnergyPair
    [MeasurableSpace H] [Nontrivial H]
    {a τ q p : ℝ} (ha : 1 ≤ a) (hτ : 0 < τ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hp : 1 < p) :
    ((1 - q) / a ^ p, (a - 1) / a ^ p) ∈
      articleAttainablePairs.{u, v} H p τ := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let qI : I := ⟨q, hq.le, hq1⟩
  let μ : Measure (ULift.{u} Bool) :=
    bernoulliMeasure (ULift.up true) (ULift.up false) qI
  let X : ULift.{u} Bool → H := p1SingleAtom a τ e
  let law : RandomVectorLaw.{u, v} H p := {
    Ω := ULift.{u} Bool
    mΩ := inferInstance
    μ := μ
    probability := inferInstance
    X := X
    memLp := MemLp.of_discrete
    moment_pos := by
      rw [show μ = bernoulliMeasure (ULift.up true) (ULift.up false) qI by rfl,
        show X = p1SingleAtom a τ e by rfl,
        p1SingleAtom_rpow_moment ha hτ qI.property.1 qI.property.2 he
          (by linarith : 0 < p)]
      exact mul_pos hq (Real.rpow_pos_of_pos (by positivity) p)
  }
  have hmoment : 0 < ∫ b, ‖X b‖ ^ p ∂μ := law.moment_pos
  have hmoment_eq : (∫ b, ‖X b‖ ^ p ∂μ) = q * (a * τ) ^ p := by
    dsimp [μ, X, qI]
    exact p1SingleAtom_rpow_moment ha hτ hq.le hq1 he (by linarith : 0 < p)
  have hmean : (∫ b, X b ∂μ) = (q * a * τ) • e := by
    dsimp [μ, X, qI]
    exact p1SingleAtom_mean ha hτ hq.le hq1 he
  have hclipmean : (∫ b, radialClip τ (X b) ∂μ) = (q * τ) • e := by
    dsimp [μ, X, qI]
    exact p1SingleAtom_clipped_mean ha hτ hq.le hq1 he
  have hvar :
      (∫ b, ‖radialClip τ (X b) -
        ∫ z, radialClip τ (X z) ∂μ‖ ^ 2 ∂μ) = q * (1 - q) * τ ^ 2 := by
    dsimp [μ, X, qI]
    exact p1SingleAtom_centered_sq ha hτ hq.le hq1 he
  have hnormdiff : ‖(q * τ) • e - (q * a * τ) • e‖ = q * (a - 1) * τ := by
    have hvec : (q * τ) • e - (q * a * τ) • e = (q * (1 - a) * τ) • e := by
      rw [← sub_smul]
      congr 1
      ring
    have harg : q * (1 - a) * τ ≤ 0 := by
      calc
        q * (1 - a) * τ = (q * τ) * (1 - a) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg hq.le hτ.le) (sub_nonpos.mpr ha)
    rw [hvec, norm_smul, he, Real.norm_eq_abs, abs_of_nonpos harg]
    ring_nf
  have hden :
      τ ^ (1 - p) * (∫ b, ‖X b‖ ^ p ∂μ) =
        q * a ^ p * τ := by
    rw [hmoment_eq, Real.mul_rpow (by positivity : 0 ≤ a) hτ.le]
    have hpow : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    calc
      τ ^ (1 - p) * (q * (a ^ p * τ ^ p)) =
          q * a ^ p * (τ ^ (1 - p) * τ ^ p) := by ring
      _ = q * a ^ p * τ := by rw [hpow]
  have hden' : τ ^ (1 - p) * (q * (a * τ) ^ p) = q * a ^ p * τ := by
    simpa only [hmoment_eq] using hden
  have henergy :
      stochasticClippingRatio μ 0 1 p τ X = (1 - q) / a ^ p := by
    dsimp [stochasticClippingRatio]
    rw [hvar, hden]
    simp only [zero_mul]
    have hapow : 0 < a ^ p := Real.rpow_pos_of_pos (by linarith : 0 < a) p
    field_simp [ne_of_gt hq, ne_of_gt hτ, ne_of_gt hapow]
    ring
  have hbias :
      stochasticClippingRatio μ 1 0 p τ X = (a - 1) / a ^ p := by
    dsimp [stochasticClippingRatio]
    rw [hclipmean, hmean, hnormdiff, hmoment_eq, hden']
    simp only [one_mul]
    have hapow : 0 < a ^ p := Real.rpow_pos_of_pos (by linarith : 0 < a) p
    field_simp [ne_of_gt hq, ne_of_gt hτ, ne_of_gt hapow]
    ring
  apply Set.mem_range.mpr
  refine ⟨law, ?_⟩
  exact Prod.ext henergy hbias

/-- Every point strictly to the left of a point on the rare-shock boundary
is realized by a two-atom law.  This is the parametrized form of the
attainability construction in Theorem 4.1. -/
theorem rareBoundary_leftSegment_mem_attainable
    [MeasurableSpace H] [Nontrivial H]
    {r τ p v₀ : ℝ} (hp : 1 < p) (hτ : 0 < τ)
    (hr : 1 ≤ r) (hv : 0 ≤ v₀)
    (hvlt : v₀ < r ^ (-p)) :
    (v₀, rareBias p r) ∈ articleAttainablePairs.{u, v} H p τ := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hrpow : 0 < r ^ p := Real.rpow_pos_of_pos hrpos p
  have hpowneg : r ^ (-p) = 1 / r ^ p := by
    calc
      r ^ (-p) = (r ^ p)⁻¹ := Real.rpow_neg hrpos.le p
      _ = 1 / r ^ p := by rw [one_div]
  have hvlt' : v₀ * r ^ p < 1 := by
    rw [hpowneg] at hvlt
    exact (lt_div_iff₀ hrpow).mp hvlt
  let q : ℝ := 1 - v₀ * r ^ p
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hq1 : q ≤ 1 := by
    dsimp [q]
    nlinarith [mul_nonneg hv hrpow.le]
  have hpair := oneAtom_biasEnergyPair.{u, v} (H := H)
    (a := r) (τ := τ) (q := q) (p := p) hr hτ hq hq1 hp
  have hden : r ^ p ≠ 0 := ne_of_gt hrpow
  have henergy : (1 - q) / r ^ p = v₀ := by
    dsimp [q]
    field_simp [hden]
    ring
  have hbias : (r - 1) / r ^ p = rareBias p r := by
    rw [rareBias, hpowneg]
    field_simp [hden]
  rw [henergy, hbias] at hpair
  exact hpair

/-- No non-endpoint point of the curved upper boundary is attainable.  The
support direction is chosen tangent to the rare-shock curve, so attainment
would contradict strictness of the stochastic envelope. -/
theorem rareCurve_open_arc_disjoint_attainable
    [MeasurableSpace H] [Nontrivial H]
    {r τ p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hr1 : 1 < r) (hrupper : r < p / (p - 1)) :
    (rareEnergy p r, rareBias p r) ∉ articleAttainablePairs.{u, v} H p τ := by
  intro hmem
  rcases hmem with ⟨law, hpair⟩
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hden : 0 < p - (p - 1) * r := by
    apply (lt_div_iff₀ hpm).mp at hrupper
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
  have hsupport :
      α * rareBias p r + rareEnergy p r = K_p α 1 p := by
    have hcurve := rareCurve_support_eq_F (p := p) (α := α) (β := 1)
      (r := r) hr1.le
    rw [hF] at hcurve
    simpa [add_comm, mul_comm] using hcurve
  have hV :
      stochasticClippingRatio law.μ 0 1 p τ law.X = rareEnergy p r := by
    have := congrArg Prod.fst hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hD :
      stochasticClippingRatio law.μ 1 0 p τ law.X = rareBias p r := by
    have := congrArg Prod.snd hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hratio : stochasticClippingRatio law.μ α 1 p τ law.X = K_p α 1 p := by
    have hlin := stochasticClippingRatio_linear
      (μ := law.μ) (α := α) (β := 1) (p := p) (τ := τ) law.X
    calc
      stochasticClippingRatio law.μ α 1 p τ law.X =
          α * stochasticClippingRatio law.μ 1 0 p τ law.X +
            1 * stochasticClippingRatio law.μ 0 1 p τ law.X := hlin.symm
      _ = K_p α 1 p := by rw [hD, hV]; simpa using hsupport
  exact (ne_of_lt (stochasticClippingRatio_lt_K_p_second_regime_of_pos_energy
    law.μ hαpos.le (by norm_num) hp hp2 hreg hτ law.X law.memLp
    law.moment_pos)) hratio
