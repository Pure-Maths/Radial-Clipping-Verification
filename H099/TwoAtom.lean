import H099.AttainableExact
import H099.RareBoundaryInverse

/-!
# Real two-atom realization of attainable bias--energy pairs

The article's Corollary 4.4 follows from the explicit constructions in
Theorem 4.1.  This file records the real-valued two-outcome target set and
the constructors needed for the corollary.  The final classification step
for `1 < p ≤ 2` depends on the still unfinished converse of Theorem 4.1.
-/

open MeasureTheory ProbabilityTheory unitInterval

noncomputable section

universe u v

/-- Normalized energy--bias pairs produced by a real-valued random variable
on a two-point sample space.  The two values may coincide. -/
def realTwoAtomPairs (p τ : ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ (μ : Measure (ULift.{u} Bool)) (_ : IsProbabilityMeasure μ)
      (X : ULift.{u} Bool → ℝ),
      MemLp X (ENNReal.ofReal p) μ ∧
      0 < ∫ b, |X b| ^ p ∂μ ∧
      z = normalizedBiasEnergyPair μ p τ X}

/-- A real two-atom pair is an admissible pair in the scalar Hilbert space. -/
theorem realTwoAtomPairs_subset_scalarAttainable
    {p τ : ℝ} :
    realTwoAtomPairs.{u} p τ ⊆
      articleAttainablePairs.{u, 0} ℝ p τ := by
  intro z hz
  rcases hz with ⟨μ, hμ, X, hLp, hm, hz⟩
  let law : RandomVectorLaw.{u, 0} ℝ p := {
    Ω := ULift.{u} Bool
    mΩ := inferInstance
    μ := μ
    probability := hμ
    X := X
    memLp := hLp
    moment_pos := by simpa only [Real.norm_eq_abs] using hm
  }
  refine ⟨law, ?_⟩
  simpa only [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair,
    law] using hz.symm

/-- A Bernoulli law with one positive atom beyond the clipping threshold
and one zero atom realizes the same pair for every positive moment order. -/
theorem realTwoAtom_oneNonzero_pair
    {a τ q p : ℝ} (ha : 1 ≤ a) (hτ : 0 < τ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hp : 0 < p) :
    ((1 - q) / a ^ p, (a - 1) / a ^ p) ∈
      realTwoAtomPairs.{u} p τ := by
  have he : ‖(1 : ℝ)‖ = 1 := by norm_num
  let qI : I := ⟨q, hq.le, hq1⟩
  let μ : Measure (ULift.{u} Bool) :=
    bernoulliMeasure (ULift.up true) (ULift.up false) qI
  let X : ULift.{u} Bool → ℝ := p1SingleAtom a τ 1
  have hmoment_eq : (∫ b, |X b| ^ p ∂μ) = q * (a * τ) ^ p := by
    dsimp [μ, X, qI]
    simpa only [Real.norm_eq_abs] using
      p1SingleAtom_rpow_moment (H := ℝ) ha hτ hq.le hq1 he hp
  have hmoment : 0 < ∫ b, |X b| ^ p ∂μ := by
    rw [hmoment_eq]
    exact mul_pos hq (Real.rpow_pos_of_pos (by positivity) p)
  have hmean : (∫ b, X b ∂μ) = q * a * τ := by
    dsimp [μ, X, qI]
    simpa only [smul_eq_mul, mul_one] using
      p1SingleAtom_mean (H := ℝ) ha hτ hq.le hq1 he
  have hclipmean : (∫ b, radialClip τ (X b) ∂μ) = q * τ := by
    dsimp [μ, X, qI]
    simpa only [smul_eq_mul, mul_one] using
      p1SingleAtom_clipped_mean (H := ℝ) ha hτ hq.le hq1 he
  have hvar :
      (∫ b, ‖radialClip τ (X b) -
        ∫ z, radialClip τ (X z) ∂μ‖ ^ 2 ∂μ) = q * (1 - q) * τ ^ 2 := by
    dsimp [μ, X, qI]
    exact p1SingleAtom_centered_sq (H := ℝ) ha hτ hq.le hq1 he
  have hnormdiff : ‖(q * τ : ℝ) - q * a * τ‖ = q * (a - 1) * τ := by
    have harg : q * τ - q * a * τ ≤ 0 := by
      have := mul_nonneg (mul_nonneg hq.le hτ.le) (sub_nonneg.mpr ha)
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonpos harg]
    ring
  have hvarAbs :
      (∫ b, |radialClip τ (X b) -
        ∫ z, radialClip τ (X z) ∂μ| ^ 2 ∂μ) = q * (1 - q) * τ ^ 2 := by
    simpa only [Real.norm_eq_abs] using hvar
  have hden :
      τ ^ (1 - p) * (∫ b, ‖X b‖ ^ p ∂μ) = q * a ^ p * τ := by
    rw [show (∫ b, ‖X b‖ ^ p ∂μ) = q * (a * τ) ^ p by
      simpa only [Real.norm_eq_abs] using hmoment_eq,
      Real.mul_rpow (by positivity : 0 ≤ a) hτ.le]
    have hpow : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    calc
      τ ^ (1 - p) * (q * (a ^ p * τ ^ p)) =
          q * a ^ p * (τ ^ (1 - p) * τ ^ p) := by ring
      _ = q * a ^ p * τ := by rw [hpow]
  have hdenAbs : τ ^ (1 - p) * (q * (a * τ) ^ p) = q * a ^ p * τ := by
    have hden' : τ ^ (1 - p) * (∫ b, |X b| ^ p ∂μ) = q * a ^ p * τ := by
      simpa only [Real.norm_eq_abs] using hden
    rw [hmoment_eq] at hden'
    exact hden'
  have henergy :
      stochasticClippingRatio μ 0 1 p τ X = (1 - q) / a ^ p := by
    dsimp [stochasticClippingRatio]
    rw [hvarAbs, show (∫ b, |X b| ^ p ∂μ) =
      q * (a * τ) ^ p by exact hmoment_eq]
    simp only [zero_mul]
    have hapow : 0 < a ^ p := Real.rpow_pos_of_pos (by linarith : 0 < a) p
    rw [hdenAbs]
    field_simp [ne_of_gt hq, ne_of_gt hτ, ne_of_gt hapow]
    ring
  have hbias :
      stochasticClippingRatio μ 1 0 p τ X = (a - 1) / a ^ p := by
    dsimp [stochasticClippingRatio]
    rw [hclipmean, hmean, show |q * τ - q * a * τ| = q * (a - 1) * τ by
      simpa only [Real.norm_eq_abs] using hnormdiff, hmoment_eq]
    simp only [one_mul]
    have hapow : 0 < a ^ p := Real.rpow_pos_of_pos (by linarith : 0 < a) p
    rw [hdenAbs]
    field_simp [ne_of_gt hq, ne_of_gt hτ, ne_of_gt hapow]
    ring
  refine ⟨μ, inferInstance, X, MemLp.of_discrete, hmoment, ?_⟩
  exact (Prod.ext henergy hbias).symm

/-- Every point strictly left of a rare-shock boundary point is realized by a
real-valued two-atom variable. -/
theorem rareBoundary_leftSegment_mem_realTwoAtomPairs
    {r τ p v₀ : ℝ} (hp : 0 < p) (hτ : 0 < τ)
    (hr : 1 ≤ r) (hv : 0 ≤ v₀)
    (hvlt : v₀ < rareEnergy p r) :
    (v₀, rareBias p r) ∈ realTwoAtomPairs.{u} p τ := by
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hrpow : 0 < r ^ p := Real.rpow_pos_of_pos hrpos p
  have henergy : rareEnergy p r = 1 / r ^ p := by
    rw [rareEnergy, Real.rpow_neg hrpos.le]
    simp [one_div]
  have hvlt' : v₀ * r ^ p < 1 := by
    rw [henergy] at hvlt
    exact (lt_div_iff₀ hrpow).mp hvlt
  let q : ℝ := 1 - v₀ * r ^ p
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith [mul_nonneg hv hrpow.le]
  have hpair := realTwoAtom_oneNonzero_pair.{u}
    (a := r) (τ := τ) (q := q) (p := p) hr hτ hq hq1 hp
  have hden : r ^ p ≠ 0 := ne_of_gt hrpow
  have hfirst : (1 - q) / r ^ p = v₀ := by
    dsimp [q]
    field_simp [hden]
    ring
  have hsecond : (r - 1) / r ^ p = rareBias p r := by
    rw [rareBias, Real.rpow_neg hrpos.le]
    simp [div_eq_mul_inv]
  rw [hfirst, hsecond] at hpair
  exact hpair

/-- The strict interior of the `p = 1` triangle has real-valued two-atom
representatives (with atoms `0` and a nonnegative loss). -/
theorem p1_strict_interior_mem_realTwoAtomPairs
    {τ v₀ d₀ : ℝ} (hτ : 0 < τ)
    (hv : 0 ≤ v₀) (hd : 0 ≤ d₀) (hvd : v₀ + d₀ < 1) :
    (v₀, d₀) ∈ realTwoAtomPairs.{u} 1 τ := by
  have hden : 0 < 1 - d₀ := by linarith
  let a : ℝ := 1 / (1 - d₀)
  let q : ℝ := 1 - v₀ / (1 - d₀)
  have ha : 1 ≤ a := by
    dsimp [a]
    have hdenle : 1 - d₀ ≤ 1 := by linarith
    simpa [one_div] using (one_le_inv₀ hden).2 hdenle
  have hq : 0 < q := by
    dsimp [q]
    rw [show 1 - v₀ / (1 - d₀) = (1 - d₀ - v₀) / (1 - d₀) by
      field_simp]
    exact div_pos (by linarith) hden
  have hq1 : q ≤ 1 := by
    dsimp [q]
    have : 0 ≤ v₀ / (1 - d₀) := div_nonneg hv hden.le
    linarith
  have hpair := realTwoAtom_oneNonzero_pair.{u}
    (a := a) (τ := τ) (q := q) (p := 1) ha hτ hq hq1 (by norm_num)
  have hfirst : (1 - q) / a ^ (1 : ℝ) = v₀ := by
    dsimp [a, q]
    rw [Real.rpow_one]
    field_simp [ne_of_gt hden]
    ring
  have hsecond : (a - 1) / a ^ (1 : ℝ) = d₀ := by
    dsimp [a]
    rw [Real.rpow_one]
    field_simp [ne_of_gt hden]
    ring
  rw [hfirst, hsecond] at hpair
  exact hpair

/-- A real two-point law at the clipping radius, with Bernoulli mass `q`,
has zero clipping bias and normalized energy `4q(1-q)`. -/
theorem realTwoAtom_at_threshold_pair
    {τ p q : ℝ} (hτ : 0 < τ) (_hp : 0 < p)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (4 * q * (1 - q), 0) ∈ realTwoAtomPairs.{u} p τ := by
  let qI : I := ⟨q, hq, hq1⟩
  let μ : Measure (ULift.{u} Bool) :=
    bernoulliMeasure (ULift.up true) (ULift.up false) qI
  let X : ULift.{u} Bool → ℝ := fun b => if b.down then τ else -τ
  have hclip : ∀ b, radialClip τ (X b) = X b := by
    intro b
    cases b with
    | up b =>
      cases b <;> simp only [X, Bool.false_eq_true, ↓reduceIte]
      · exact radialClip_of_norm_le (by simp [Real.norm_eq_abs, abs_of_pos hτ])
      · exact radialClip_of_norm_le (by simp [Real.norm_eq_abs, abs_of_pos hτ])
  have hmoment_eq : (∫ b, |X b| ^ p ∂μ) = τ ^ p := by
    rw [integral_bernoulliMeasure]
    simp only [X, Bool.false_eq_true, ↓reduceIte, abs_neg,
      abs_of_pos hτ, smul_eq_mul]
    change q * τ ^ p + (1 - q) * τ ^ p = τ ^ p
    ring
  have hmoment : 0 < ∫ b, |X b| ^ p ∂μ := by
    rw [hmoment_eq]
    exact Real.rpow_pos_of_pos hτ p
  have hmean : (∫ b, X b ∂μ) = (2 * q - 1) * τ := by
    rw [integral_bernoulliMeasure]
    simp only [X, Bool.false_eq_true, ↓reduceIte, smul_eq_mul]
    change q * τ + (1 - q) * -τ = (2 * q - 1) * τ
    ring
  have hclipmean : (∫ b, radialClip τ (X b) ∂μ) = (2 * q - 1) * τ := by
    simp only [hclip, hmean]
  have hvar :
      (∫ b, |radialClip τ (X b) -
        ∫ z, radialClip τ (X z) ∂μ| ^ 2 ∂μ) =
        4 * q * (1 - q) * τ ^ 2 := by
    simp_rw [hclip]
    rw [hmean, integral_bernoulliMeasure]
    simp only [X, Bool.false_eq_true, ↓reduceIte, smul_eq_mul]
    change q * |τ - (2 * q - 1) * τ| ^ 2 +
      (1 - q) * |-τ - (2 * q - 1) * τ| ^ 2 =
        4 * q * (1 - q) * τ ^ 2
    have htrue : τ - (2 * q - 1) * τ = 2 * (1 - q) * τ := by ring
    have hfalse : -τ - (2 * q - 1) * τ = -(2 * q * τ) := by ring
    rw [htrue, hfalse]
    have htrue0 : 0 ≤ 2 * (1 - q) * τ := by positivity
    have hfalse0 : 0 ≤ 2 * q * τ := by positivity
    rw [abs_of_nonneg htrue0, abs_neg, abs_of_nonneg hfalse0]
    ring
  have hden : τ ^ (1 - p) * (∫ b, |X b| ^ p ∂μ) = τ := by
    rw [hmoment_eq, ← Real.rpow_add hτ]
    norm_num
  have henergy :
      stochasticClippingRatio μ 0 1 p τ X = 4 * q * (1 - q) := by
    dsimp [stochasticClippingRatio]
    rw [hvar, hmoment_eq]
    simp only [zero_mul]
    have hpow : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    rw [hpow]
    field_simp [hτ.ne']
    ring
  have hbias : stochasticClippingRatio μ 1 0 p τ X = 0 := by
    dsimp [stochasticClippingRatio]
    rw [hclipmean, hmean]
    simp
  refine ⟨μ, inferInstance, X, MemLp.of_discrete, hmoment, ?_⟩
  exact (Prod.ext henergy hbias).symm

/-- The complete lower edge `d = 0` is realized by two values `-τ,+τ`. -/
theorem realTwoAtom_bottom_edge
    {τ p v₀ : ℝ} (hτ : 0 < τ) (hp : 0 < p)
    (hv : 0 ≤ v₀) (hv1 : v₀ ≤ 1) :
    (v₀, 0) ∈ realTwoAtomPairs.{u} p τ := by
  let s : ℝ := Real.sqrt (1 - v₀)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact Real.sqrt_le_one.mpr (by linarith)
  have hs2 : s ^ 2 = 1 - v₀ := Real.sq_sqrt (by linarith)
  let q : ℝ := (1 + s) / 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hvalue : 4 * q * (1 - q) = v₀ := by
    dsimp [q]
    nlinarith [hs2]
  simpa only [hvalue] using
    (realTwoAtom_at_threshold_pair.{u} (p := p) hτ hp hq hq1)

/-- Every point on the sloping edge of the `p=1` triangle except `(0,1)`
is generated by a symmetric real two-atom law. -/
theorem p1_boundary_mem_realTwoAtomPairs
    {τ d₀ : ℝ} (hτ : 0 < τ) (hd : 0 ≤ d₀) (hdlt : d₀ < 1) :
    (1 - d₀, d₀) ∈ realTwoAtomPairs.{u} 1 τ := by
  have he : ‖(1 : ℝ)‖ = 1 := by norm_num
  have hden : 0 < 1 - d₀ := by linarith
  let a : ℝ := (1 + d₀) / (1 - d₀)
  have ha : 1 ≤ a := by
    dsimp [a]
    apply (le_div_iff₀ hden).2
    nlinarith
  have hplus : a + 1 = 2 / (1 - d₀) := by
    dsimp [a]
    field_simp [ne_of_gt hden]
    ring
  have hminus : a - 1 = 2 * d₀ / (1 - d₀) := by
    dsimp [a]
    field_simp [ne_of_gt hden]
    ring
  let μ : Measure (ULift.{u} Bool) :=
    bernoulliMeasure (ULift.up true) (ULift.up false) halfUnit
  let X : ULift.{u} Bool → ℝ := p1BoundaryAtom a τ 1
  have hmoment_eq : (∫ b, |X b| ^ (1 : ℝ) ∂μ) = ((a + 1) / 2) * τ := by
    dsimp [μ, X]
    simpa only [Real.norm_eq_abs] using
      p1BoundaryAtom_moment (H := ℝ) (a := a) (τ := τ)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) ha) hτ.le he
  have hmoment : 0 < ∫ b, |X b| ^ (1 : ℝ) ∂μ := by
    rw [hmoment_eq]
    positivity
  have hmean : (∫ b, X b ∂μ) = ((a - 1) / 2) * τ := by
    dsimp [μ, X]
    simpa only [smul_eq_mul, mul_one] using
      p1BoundaryAtom_mean (H := ℝ) (a := a) (τ := τ)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) ha) hτ.le he
  have hclipmean : (∫ b, radialClip τ (X b) ∂μ) = 0 := by
    dsimp [μ, X]
    exact p1BoundaryAtom_clipped_mean (H := ℝ) ha hτ he
  have hvar :
      (∫ b, |radialClip τ (X b) -
        ∫ z, radialClip τ (X z) ∂μ| ^ 2 ∂μ) = τ ^ 2 := by
    dsimp [μ, X]
    simpa only [Real.norm_eq_abs] using
      p1BoundaryAtom_centered_sq (H := ℝ) ha hτ he
  have hbias : stochasticClippingRatio μ 1 0 1 τ X = d₀ := by
    dsimp [stochasticClippingRatio]
    rw [hclipmean, hmean, hmoment_eq]
    norm_num
    rw [abs_of_nonneg (by positivity : 0 ≤ (a - 1) / 2),
      abs_of_pos hτ, hminus, hplus]
    field_simp [ne_of_gt hτ, ne_of_gt hden]
  have henergy : stochasticClippingRatio μ 0 1 1 τ X = 1 - d₀ := by
    dsimp [stochasticClippingRatio]
    rw [hvar, hmoment_eq]
    simp only [zero_mul, zero_add]
    norm_num
    rw [hplus]
    field_simp [ne_of_gt hτ, ne_of_gt hden]
  refine ⟨μ, inferInstance, X, MemLp.of_discrete, hmoment, ?_⟩
  exact (Prod.ext henergy hbias).symm

/-- Corollary 4.4 for `p = 1`: every pair attainable in any nontrivial
Hilbert space is also attained by a real random variable on `Bool`. -/
theorem p1_articleAttainablePairs_subset_realTwoAtomPairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {τ : ℝ} (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H 1 τ ⊆ realTwoAtomPairs.{u} 1 τ := by
  intro z hz
  have hz' := attainableBiasEnergyPairsP1_subset_triangle H hτ hz
  obtain ⟨hv, hd, hsum, hdlt⟩ := hz'
  by_cases hstrict : z.1 + z.2 < 1
  · exact p1_strict_interior_mem_realTwoAtomPairs hτ hv hd hstrict
  · have heq : z.1 + z.2 = 1 := le_antisymm hsum (le_of_not_gt hstrict)
    have hfirst : z.1 = 1 - z.2 := by linarith
    rw [show z = (1 - z.2, z.2) by
      apply Prod.ext
      · exact hfirst
      · rfl]
    exact p1_boundary_mem_realTwoAtomPairs hτ hd hdlt

/-- Both normalized coordinates of every actual pair are nonnegative. -/
theorem articleAttainablePair_nonneg
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {p τ : ℝ} (hτ : 0 < τ)
    {z : ℝ × ℝ} (hz : z ∈ articleAttainablePairs.{u, v} H p τ) :
    0 ≤ z.1 ∧ 0 ≤ z.2 := by
  rcases hz with ⟨law, rfl⟩
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  constructor
  · dsimp [RandomVectorLaw.biasEnergyPair, stochasticClippingRatio]
    positivity
  · dsimp [RandomVectorLaw.biasEnergyPair, stochasticClippingRatio]
    positivity

/-- Corollary 4.4 on the positive intermediate bias levels `0 < d < c_p`.
The radius-selection lemma is the geometric input from Theorem 4.1. -/
theorem articleAttainablePair_midBias_mem_realTwoAtomPairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ v₀ d : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hd : 0 < d) (hdc : d < c_p p)
    (hmem : (v₀, d) ∈ articleAttainablePairs.{u, v} H p τ) :
    (v₀, d) ∈ realTwoAtomPairs.{u} p τ := by
  obtain ⟨r, hr1, _hrR, hrd, hvlt⟩ :=
    exists_rareRadius_above_attainable_energy hp hp2 hτ hd hdc hmem
  have hv0 : 0 ≤ v₀ := (articleAttainablePair_nonneg hτ hmem).1
  rw [← hrd]
  exact rareBoundary_leftSegment_mem_realTwoAtomPairs
    (p := p) (τ := τ) (zero_lt_one.trans hp) hτ hr1.le hv0 hvlt

/-- Equality in the maximal clipping bias forces all nonzero observations
onto the unique maximizing sphere. -/
theorem maxBias_forces_radius
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hmoment : 0 < ∫ ω, ‖X ω‖ ^ p ∂μ)
    (heq : stochasticClippingRatio μ 1 0 p τ X = c_p p) :
    ∀ᵐ ω ∂μ, X ω = 0 ∨ ‖X ω‖ = (p / (p - 1)) * τ := by
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let D : ℝ := τ ^ (1 - p) * (∫ ω, ‖X ω‖ ^ p ∂μ)
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) hmoment
  have hK : K_p 1 0 p = c_p p := by
    simp [K_p, c_p]
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hY : Integrable Y μ := by
    dsimp [Y]
    exact integrable_radialClip hLp.1 hτ
  have hXp0 := hLp.integrable_norm_rpow'
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using hXp0
  have hres : Integrable (fun ω => ‖X ω - Y ω‖) μ := (hX.sub hY).norm
  have hbias :
      ‖(∫ ω, Y ω ∂μ) - ∫ ω, X ω ∂μ‖ ≤
        ∫ ω, ‖X ω - Y ω‖ ∂μ := by
    calc
      ‖(∫ ω, Y ω ∂μ) - ∫ ω, X ω ∂μ‖ =
          ‖∫ ω, Y ω - X ω ∂μ‖ := by rw [integral_sub hY hX]
      _ ≤ ∫ ω, ‖Y ω - X ω‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ ω, ‖X ω - Y ω‖ ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => norm_sub_rev _ _
  have hratio :
      ‖(∫ ω, Y ω ∂μ) - ∫ ω, X ω ∂μ‖ = K_p 1 0 p * D := by
    have heq' :
        (‖(∫ ω, Y ω ∂μ) - ∫ ω, X ω ∂μ‖ +
          (0 / τ) * (∫ ω, ‖Y ω - ∫ z, Y z ∂μ‖ ^ 2 ∂μ)) / D =
            K_p 1 0 p := by
      simpa only [stochasticClippingRatio, Y, D, hK, one_mul] using heq
    simpa only [zero_div, zero_mul, add_zero] using
      (div_eq_iff hD.ne').mp (by simpa only [zero_div, zero_mul, add_zero] using heq')
  have hbound :
      (∫ ω, ‖X ω - Y ω‖ ∂μ) ≤ K_p 1 0 p * D := by
    have hint := integrated_radialClip_envelope μ (α := 1) (β := 0)
      (by norm_num) (by norm_num) hp hp2 hτ X hLp.1 hXp
    simpa only [integral_const_mul, zero_div, zero_mul, add_zero,
      one_mul, D, mul_assoc] using hint
  have hintEq :
      (∫ ω, ‖X ω - Y ω‖ ∂μ) = K_p 1 0 p * D := by
    linarith
  let L : Ω → ℝ := fun ω => ‖X ω - Y ω‖
  let R : Ω → ℝ := fun ω =>
    (K_p 1 0 p * τ ^ (1 - p)) * ‖X ω‖ ^ p
  have hLint : Integrable L μ := hres
  have hRint : Integrable R μ := hXp.const_mul _
  have hLR : L ≤ᵐ[μ] R := by
    filter_upwards with ω
    dsimp [L, R, Y]
    simpa only [zero_div, zero_mul, add_zero, one_mul, mul_assoc] using
      (radialClip_envelope (α := 1) (β := 0)
        (by norm_num) (by norm_num) hp hp2 hτ (X ω))
  have hpointEq : L =ᵐ[μ] R := by
    apply (integral_eq_iff_of_ae_le hLint hRint hLR).mp
    rw [show (∫ ω, R ω ∂μ) =
      (K_p 1 0 p * τ ^ (1 - p)) * (∫ ω, ‖X ω‖ ^ p ∂μ) by
      dsimp [R]; rw [integral_const_mul]]
    simpa [L, D, mul_assoc] using hintEq
  filter_upwards [hpointEq] with ω hω
  by_cases hxω : X ω = 0
  · exact Or.inl hxω
  · right
    have hnorm := pointwise_eq_implies_norm_eq_rstar
      (α := 1) (β := 0) (p := p) (τ := τ)
      (by norm_num) (by norm_num) hp hp2 (by norm_num) hτ hxω (by
        dsimp [L, R, Y] at hω
        simpa only [zero_div, zero_mul, add_zero, one_mul, mul_assoc] using hω)
    simpa [r_star] using hnorm

/-- At the maximal bias level, the clipped mean is nonzero, so centering
strictly lowers the energy below the rare-shock endpoint. -/
theorem maxBias_energy_lt
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (hmoment : 0 < ∫ ω, ‖X ω‖ ^ p ∂μ)
    (heq : stochasticClippingRatio μ 1 0 p τ X = c_p p) :
    stochasticClippingRatio μ 0 1 p τ X <
      rareEnergy p (p / (p - 1)) := by
  let R : ℝ := p / (p - 1)
  let Y : Ω → H := fun ω => radialClip τ (X ω)
  let b : H := ∫ ω, Y ω ∂μ
  let m : H := ∫ ω, X ω ∂μ
  let M : ℝ := ∫ ω, ‖X ω‖ ^ p ∂μ
  let D : ℝ := τ ^ (1 - p) * M
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hR : 1 < R := by
    dsimp [R]
    exact (lt_div_iff₀ hpm).2 (by nlinarith)
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hD : 0 < D := by
    dsimp [D, M]
    exact mul_pos (Real.rpow_pos_of_pos hτ _) hmoment
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hY : Integrable Y μ := integrable_radialClip hLp.1 hτ
  have hYsq : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    integrable_sq_norm_radialClip hLp.1 hτ
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
      using hLp.integrable_norm_rpow'
  have hsphere : ∀ᵐ ω ∂μ, X ω = 0 ∨ ‖X ω‖ = R * τ := by
    simpa [R] using maxBias_forces_radius μ hp hp2 hτ X hLp hmoment heq
  have hclip : Y =ᵐ[μ] (fun ω => (R⁻¹ : ℝ) • X ω) := by
    filter_upwards [hsphere] with ω hω
    rcases hω with hx0 | hxnorm
    · simp [Y, hx0, radialClip_zero hτ.le]
    · have hlt : τ < ‖X ω‖ := by rw [hxnorm]; nlinarith
      dsimp [Y]
      rw [radialClip_of_lt_norm hlt, hxnorm]
      congr 1
      field_simp [hτ.ne', hRpos.ne']
  have hbformula : b = (R⁻¹ : ℝ) • m := by
    calc
      b = ∫ ω, (R⁻¹ : ℝ) • X ω ∂μ := integral_congr_ae hclip
      _ = (R⁻¹ : ℝ) • m := by rw [integral_smul]
  have hmformula : m = R • b := by
    rw [hbformula, smul_smul]
    simp [hRpos.ne']
  have hbne : b ≠ 0 := by
    intro hbzero
    have hmzero : m = 0 := by rw [hmformula, hbzero, smul_zero]
    have hbiaszero : stochasticClippingRatio μ 1 0 p τ X = 0 := by
      simp [stochasticClippingRatio, Y, b, m, hbzero, hmzero]
    rw [hbiaszero] at heq
    have hcpos : 0 < c_p p := by
      unfold c_p
      exact div_pos (Real.rpow_pos_of_pos hpm _) (Real.rpow_pos_of_pos
        (zero_lt_one.trans hp) _)
    linarith
  have hpoint :
      (fun ω => ‖Y ω‖ ^ 2) =ᵐ[μ]
        (fun ω => (τ ^ (2 - p) * R ^ (-p)) * ‖X ω‖ ^ p) := by
    filter_upwards [hsphere] with ω hω
    rcases hω with hx0 | hxnorm
    · simp [Y, hx0, radialClip_zero hτ.le,
        Real.zero_rpow (ne_of_gt (zero_lt_one.trans hp))]
    · have hτle : τ ≤ ‖X ω‖ := by rw [hxnorm]; nlinarith
      have hnormY : ‖Y ω‖ = τ := by
        rw [show Y ω = radialClip τ (X ω) by rfl,
          norm_radialClip hτ, min_eq_right hτle]
      rw [hnormY, hxnorm, Real.mul_rpow hRpos.le hτ.le,
        Real.rpow_neg hRpos.le]
      have hpowτ : τ ^ (2 - p) * τ ^ p = τ ^ (2 : ℝ) := by
        rw [← Real.rpow_add hτ]
        norm_num
      calc
        τ ^ 2 = (R ^ p)⁻¹ * R ^ p * τ ^ 2 := by
          field_simp [(Real.rpow_pos_of_pos hRpos p).ne']
        _ = τ ^ (2 - p) * (R ^ p)⁻¹ * (R ^ p * τ ^ p) := by
          calc
            (R ^ p)⁻¹ * R ^ p * τ ^ 2 =
                (R ^ p)⁻¹ * R ^ p * (τ ^ (2 - p) * τ ^ p) := by
                  rw [hpowτ]
                  norm_num
            _ = _ := by ring
  have hsecond :
      (∫ ω, ‖Y ω‖ ^ 2 ∂μ) =
        (τ ^ (2 - p) * R ^ (-p)) * M := by
    rw [show (∫ ω, ‖Y ω‖ ^ 2 ∂μ) =
      ∫ ω, (τ ^ (2 - p) * R ^ (-p)) * ‖X ω‖ ^ p ∂μ from
      integral_congr_ae hpoint, integral_const_mul]
  have hvar :
      (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ) =
        (∫ ω, ‖Y ω‖ ^ 2 ∂μ) - ‖b‖ ^ 2 :=
    integral_norm_sub_mean_sq μ Y hY hYsq
  have hpowτ : τ * D = τ ^ (2 - p) * M := by
    have hfactor : τ * τ ^ (1 - p) = τ ^ (2 - p) := by
      calc
        τ * τ ^ (1 - p) = τ ^ (1 : ℝ) * τ ^ (1 - p) := by simp
        _ = τ ^ ((1 : ℝ) + (1 - p)) := (Real.rpow_add hτ 1 (1 - p)).symm
        _ = τ ^ (2 - p) := by congr 1; ring
    dsimp [D]
    rw [← mul_assoc, hfactor]
  have henergy :
      stochasticClippingRatio μ 0 1 p τ X =
        R ^ (-p) - ‖b‖ ^ 2 / (τ * D) := by
    dsimp [stochasticClippingRatio]
    rw [show (∫ ω, ‖radialClip τ (X ω) -
        ∫ z, radialClip τ (X z) ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖Y ω - b‖ ^ 2 ∂μ) by rfl,
      hvar, hsecond]
    simp only [zero_mul, zero_add]
    have hτD : τ * D ≠ 0 := mul_ne_zero hτ.ne' hD.ne'
    change (1 / τ * (τ ^ (2 - p) * R ^ (-p) * M - ‖b‖ ^ 2)) / D =
      R ^ (-p) - ‖b‖ ^ 2 / (τ * D)
    have hnum : τ ^ (2 - p) * R ^ (-p) * M = τ * D * R ^ (-p) := by
      rw [hpowτ]
      ring
    rw [hnum]
    field_simp [hτ.ne', hD.ne']
  rw [henergy]
  change R ^ (-p) - ‖b‖ ^ 2 / (τ * D) < R ^ (-p)
  have hbpos : 0 < ‖b‖ ^ 2 := pow_pos (norm_pos_iff.mpr hbne) _
  have hdenpos : 0 < τ * D := mul_pos hτ hD
  exact sub_lt_self _ (div_pos hbpos hdenpos)

/-- Corollary 4.4 at the highest possible bias level `d = c_p`. -/
theorem articleAttainablePair_maxBias_mem_realTwoAtomPairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ v₀ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hmem : (v₀, c_p p) ∈ articleAttainablePairs.{u, v} H p τ) :
    (v₀, c_p p) ∈ realTwoAtomPairs.{u} p τ := by
  let R : ℝ := p / (p - 1)
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hRone : 1 ≤ R := by
    dsimp [R]
    exact (le_div_iff₀ hpm).2 (by linarith)
  have hRstar : r_star 1 0 p = R := by simp [r_star, R]
  have hRbias : rareBias p R = c_p p := by
    have hF : F 1 0 p R = c_p p := by
      calc
        F 1 0 p R = criticalValue 1 0 p := by
          rw [← hRstar]
          exact F_at_r_star (by norm_num) hp (by norm_num)
        _ = c_p p := by
          simpa using criticalValue_closed_form (α := 1) (β := 0)
            (p := p) (by norm_num) hp (by norm_num)
    have hcurve := rareCurve_support_eq_F (p := p) (α := 1) (β := 0)
      (r := R) hRone
    simpa using hcurve.trans hF
  rcases hmem with ⟨law, hpair⟩
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  have hD : stochasticClippingRatio law.μ 1 0 p τ law.X = c_p p := by
    have := congrArg Prod.snd hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hV : stochasticClippingRatio law.μ 0 1 p τ law.X = v₀ := by
    have := congrArg Prod.fst hpair
    simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
  have hvlt : v₀ < rareEnergy p R := by
    rw [← hV]
    exact maxBias_energy_lt law.μ hp hp2 hτ law.X law.memLp
      law.moment_pos hD
  have hv0 : 0 ≤ v₀ := by
    rw [← hV]
    dsimp [stochasticClippingRatio]
    positivity
  rw [← hRbias]
  exact rareBoundary_leftSegment_mem_realTwoAtomPairs
    (p := p) (τ := τ) hp0 hτ hRone hv0 hvlt

/-- Corollary 4.4 for `1 < p ≤ 2`: every pair attainable in an arbitrary
nontrivial Hilbert space is realized by a real random variable on `Bool`.
Thus it takes no more than two values. -/
theorem articleAttainablePairs_subset_realTwoAtomPairs
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ ⊆ realTwoAtomPairs.{u} p τ := by
  intro z hz
  have hnonneg := articleAttainablePair_nonneg hτ hz
  have hdle : z.2 ≤ c_p p := by
    rcases hz with ⟨law, hpair⟩
    letI : MeasurableSpace law.Ω := law.mΩ
    letI : IsProbabilityMeasure law.μ := law.probability
    have hD : stochasticClippingRatio law.μ 1 0 p τ law.X = z.2 := by
      have := congrArg Prod.snd hpair
      simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
    have hbound := stochasticClippingRatio_le_K_p_of_memLp
      law.μ (α := 1) (β := 0) (by norm_num) (by norm_num)
        hp hp2 hτ law.X law.memLp law.moment_pos
    rw [hD] at hbound
    have hK : K_p 1 0 p = c_p p := by simp [K_p, c_p]
    rw [hK] at hbound
    exact hbound
  rcases z with ⟨v₀, d⟩
  change 0 ≤ v₀ ∧ 0 ≤ d at hnonneg
  change d ≤ c_p p at hdle
  by_cases hd0 : d = 0
  · have hvle : v₀ ≤ 1 := by
      rcases hz with ⟨law, hpair⟩
      letI : MeasurableSpace law.Ω := law.mΩ
      letI : IsProbabilityMeasure law.μ := law.probability
      have hV : stochasticClippingRatio law.μ 0 1 p τ law.X = v₀ := by
        have := congrArg Prod.fst hpair
        simpa [RandomVectorLaw.biasEnergyPair, normalizedBiasEnergyPair] using this
      have hbound := stochasticClippingRatio_le_K_p_of_memLp
        law.μ (α := 0) (β := 1) (by norm_num) (by norm_num)
          hp hp2 hτ law.X law.memLp law.moment_pos
      rw [hV] at hbound
      have hK : K_p 0 1 p = 1 := by
        unfold K_p
        rw [if_pos (by linarith : (0 : ℝ) ≤ p * 1)]
      rw [hK] at hbound
      exact hbound
    rw [hd0]
    exact realTwoAtom_bottom_edge hτ (zero_lt_one.trans hp) hnonneg.1 hvle
  have hdpos : 0 < d := lt_of_le_of_ne hnonneg.2 (Ne.symm hd0)
  by_cases hdmax : d = c_p p
  · rw [hdmax] at hz ⊢
    exact articleAttainablePair_maxBias_mem_realTwoAtomPairs hp hp2 hτ hz
  have hdlt : d < c_p p := lt_of_le_of_ne hdle hdmax
  exact articleAttainablePair_midBias_mem_realTwoAtomPairs hp hp2 hτ hdpos hdlt hz

/-- Corollary 4.4 in its full article range `1 ≤ p ≤ 2`: every attainable
energy--bias pair has a real-valued realization with at most two atoms. -/
theorem articleAttainablePairs_realTwoAtom_realization
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    articleAttainablePairs.{u, v} H p τ ⊆ realTwoAtomPairs.{u} p τ := by
  rcases eq_or_lt_of_le hp with heq | hplt
  · subst p
    exact p1_articleAttainablePairs_subset_realTwoAtomPairs hτ
  · exact articleAttainablePairs_subset_realTwoAtomPairs hplt hp2 hτ
