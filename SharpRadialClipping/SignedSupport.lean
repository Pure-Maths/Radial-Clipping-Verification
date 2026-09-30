import SharpRadialClipping.Geometry
import SharpRadialClipping.RandomLaw
import SharpRadialClipping.Attainable
import SharpRadialClipping.Deterministic

/-!
# Signed support for `1 < p ≤ 2`

This file defines the article's attainable set using arbitrary admissible
Hilbert-valued laws and proves the full four-branch signed support formula.
The upper bound applies to every admissible law; endpoint laws and the
rare-two-point approximation establish sharpness in each coefficient regime.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open unitInterval

universe u v

/-- The four-branch expression asserted for the signed support in the article. -/
def signedSupportFormula (α β p : ℝ) : ℝ :=
  if β < 0 then
    if α ≤ 0 then 0 else α * c_p p
  else if α ≤ p * β then β
  else c_p p * α ^ p / (α - β) ^ (p - 1)

/--
Pointwise signed upper bound from the nonnegative envelope and coordinate
bounds. This is only an upper bound: it makes no assertion that any branch is
the supremum over the article's attainable set.
-/
theorem signed_linear_form_le_formula_of_envelope
    {α β p v d : ℝ}
    (hp : 1 < p)
    (hv0 : 0 ≤ v) (hd0 : 0 ≤ d) (hv1 : v ≤ 1)
    (hdc : d ≤ c_p p)
    (henv : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * d + b * v ≤ K_p a b p) :
    α * d + β * v ≤ signedSupportFormula α β p := by
  by_cases hβ : β < 0
  · by_cases hα : α ≤ 0
    · have hαd : α * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hα hd0
      have hβv : β * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ.le hv0
      simpa [signedSupportFormula, hβ, hα] using add_nonpos hαd hβv
    · have hαpos : 0 < α := lt_of_not_ge hα
      have hαd : α * d ≤ α * c_p p := mul_le_mul_of_nonneg_left hdc hαpos.le
      have hβv : β * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ.le hv0
      simpa [signedSupportFormula, hβ, hα] using add_le_add hαd hβv
  · have hβ0 : 0 ≤ β := le_of_not_gt hβ
    by_cases hreg : α ≤ p * β
    · by_cases hα : 0 ≤ α
      · have hbound := henv α β hα hβ0
        simpa [signedSupportFormula, hβ, hreg, K_p] using hbound
      · have hαneg : α < 0 := lt_of_not_ge hα
        have hαd : α * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hαneg.le hd0
        have hβv : β * v ≤ β := by
          calc
            β * v ≤ β * 1 := mul_le_mul_of_nonneg_left hv1 hβ0
            _ = β := by ring
        have hsum : α * d + β * v ≤ β := by linarith
        simpa [signedSupportFormula, hβ, hreg] using hsum
    · have hreg' : p * β < α := lt_of_not_ge hreg
      have hαpos : 0 < α := by nlinarith [hp]
      have hbound := henv α β hαpos.le hβ0
      simpa [signedSupportFormula, hβ, hreg, K_p] using hbound

/--
For points in the closed unit simplex, every signed linear functional is
bounded by the largest of its values at the three vertices.
-/
theorem simplex_linear_form_le_vertex_max
    {α β v d : ℝ} (hv0 : 0 ≤ v) (hd0 : 0 ≤ d) (hvd : v + d ≤ 1) :
    α * d + β * v ≤ max 0 (max α β) := by
  let M : ℝ := max 0 (max α β)
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact le_max_left 0 _
  have hMa : α ≤ M := by
    dsimp [M]
    exact le_trans (le_max_left α β) (le_max_right 0 (max α β))
  have hMb : β ≤ M := by
    dsimp [M]
    exact le_trans (le_max_right α β) (le_max_right 0 (max α β))
  have hterms : α * d + β * v ≤ M * d + M * v := by
    have h1 := mul_le_mul_of_nonneg_right hMa hd0
    have h2 := mul_le_mul_of_nonneg_right hMb hv0
    linarith
  have hlast : M * d + M * v ≤ M := by
    calc
      M * d + M * v = M * (d + v) := by ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left (by linarith) hM0
      _ = M := by ring
  simpa [M] using hterms.trans hlast

/--
The article's attainable set for a fixed nontrivial Hilbert space, with
arbitrary admissible laws represented by `RandomVectorLaw`. Coordinates are
ordered as `(energy, bias)`, matching the article's `(v,d)` convention.
-/
def articleAttainablePairs (H : Type v) [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (p τ : ℝ) : Set (ℝ × ℝ) :=
  Set.range (fun law : RandomVectorLaw.{u, v} H p => law.biasEnergyPair τ)

/-- The stochastic ratio is linear in the two weights, with the article's
coordinate order `(energy, bias)`. -/
lemma stochasticClippingRatio_linear
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {α β p τ : ℝ} (X : Ω → H) :
    α * stochasticClippingRatio μ 1 0 p τ X +
        β * stochasticClippingRatio μ 0 1 p τ X =
      stochasticClippingRatio μ α β p τ X := by
  dsimp [stochasticClippingRatio]
  field_simp
  ring

/-- In the nonlinear nonnegative regime, actual laws approach the claimed
support value from below. -/
theorem articleAttainablePair_epsilon_optimal_second_regime
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β ε : ℝ} (hp : 1 < p) (hτ : 0 < τ)
    (hβ : 0 ≤ β) (hreg : p * β < α) (hε : 0 < ε) :
    ∃ z ∈ articleAttainablePairs.{u, v} H p τ,
      K_p α β p - ε < α * z.2 + β * z.1 := by
  obtain ⟨q, hq0, hqupper, X, hcenter, hmoment, hnear⟩ :=
    exists_rare_twoPoint_epsilon_optimal_second_regime
      (H := H) hβ hp hreg hτ hε
  let μ : Measure Bool := rareBernoulli q
  let law0 : RandomVectorLaw.{0, v} H p :=
    { Ω := Bool
      mΩ := inferInstance
      μ := μ
      probability := inferInstance
      X := X
      memLp := MemLp.of_discrete
      moment_pos := hmoment }
  let law : RandomVectorLaw.{u, v} H p := law0.liftBool
  let e : Bool ≃ᵐ ULift.{u, 0} Bool := (MeasurableEquiv.ulift).symm
  refine ⟨law.biasEnergyPair τ, ⟨law, rfl⟩, ?_⟩
  change K_p α β p - ε <
    α * stochasticClippingRatio (μ.map e) 1 0 p τ
        (fun y => X (e.symm y)) +
      β * stochasticClippingRatio (μ.map e) 0 1 p τ
        (fun y => X (e.symm y))
  rw [stochasticClippingRatio_map_equiv e μ X,
    stochasticClippingRatio_map_equiv e μ X]
  calc
    K_p α β p - ε < stochasticClippingRatio μ α β p τ X := hnear
    _ = α * stochasticClippingRatio μ 1 0 p τ X +
        β * stochasticClippingRatio μ 0 1 p τ X :=
      (stochasticClippingRatio_linear μ X).symm

/-- The endpoint `(energy,bias) = (1,0)` is realized in the full attainable
set by a symmetric two-point law on `±τe`. -/
theorem articleEndpointPair_one_zero
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hτ : 0 < τ) :
    (1, 0) ∈ articleAttainablePairs.{u, v} H p τ := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let X : Bool → H := symmetricTwoPoint τ e
  have hmoment : 0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli := by
    dsimp [X]
    rw [integral_norm_symmetricTwoPoint_rpow hτ he]
    exact Real.rpow_pos_of_pos hτ p
  let law0 : RandomVectorLaw.{0, v} H p :=
    { Ω := Bool
      mΩ := inferInstance
      μ := symmetricBernoulli
      probability := inferInstance
      X := X
      memLp := MemLp.of_discrete
      moment_pos := hmoment }
  let law : RandomVectorLaw.{u, v} H p := law0.liftBool
  have hpair : law.biasEnergyPair τ = (1, 0) := by
    change (stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 0 1 p τ
          (fun y => X (((MeasurableEquiv.ulift).symm).symm y)),
        stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 1 0 p τ
          (fun y => X (((MeasurableEquiv.ulift).symm).symm y))) = (1, 0)
    rw [stochasticClippingRatio_map_equiv, stochasticClippingRatio_map_equiv]
    have h := normalizedBiasEnergyPair_symmetric_eq (p := p) hτ he
    simpa [normalizedBiasEnergyPair] using h
  rw [← hpair]
  exact ⟨law, rfl⟩

/-- In the endpoint support regime `β ≥ 0`, `α ≤ pβ`, the support value `β`
**is attained** by the symmetric endpoint law. -/
theorem articleAttainablePair_attains_endpoint_regime
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β : ℝ} (_hp : 1 < p) (hτ : 0 < τ)
    (hβ : 0 ≤ β) (hreg : α ≤ p * β) :
    ∃ z ∈ articleAttainablePairs.{u, v} H p τ,
      α * z.2 + β * z.1 = signedSupportFormula α β p := by
  refine ⟨(1, 0), articleEndpointPair_one_zero hτ, ?_⟩
  simp [signedSupportFormula, hβ, hreg]

/-- The origin of the attainable set is realized by a deterministic vector
whose norm is exactly the clipping threshold. -/
theorem articleOrigin_mem
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hτ : 0 < τ) :
    (0, 0) ∈ articleAttainablePairs.{u, v} H p τ := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let X : Bool → H := fun _ => τ • e
  have hnorm : ‖τ • e‖ = τ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, he]
    simp
  have hmoment : 0 < ∫ b, ‖X b‖ ^ p ∂symmetricBernoulli := by
    rw [symmetricBernoulli, integral_bernoulliMeasure]
    simp [X, hnorm, halfUnit]
    positivity
  let law0 : RandomVectorLaw.{0, v} H p :=
    { Ω := Bool
      mΩ := inferInstance
      μ := symmetricBernoulli
      probability := inferInstance
      X := X
      memLp := MemLp.of_discrete
      moment_pos := hmoment }
  let law : RandomVectorLaw.{u, v} H p := law0.liftBool
  have hpair : law.biasEnergyPair τ = (0, 0) := by
    change (stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 0 1 p τ
          (fun y => X (((MeasurableEquiv.ulift).symm).symm y)),
        stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 1 0 p τ
          (fun y => X (((MeasurableEquiv.ulift).symm).symm y))) = (0, 0)
    rw [stochasticClippingRatio_map_equiv, stochasticClippingRatio_map_equiv]
    apply Prod.ext
    · dsimp [stochasticClippingRatio]
      have hclip : ∀ b, radialClip τ (X b) = X b := by
        intro b
        apply radialClip_of_norm_le
        simp [X, hnorm, hτ.le]
      rw [integral_congr_ae (Filter.Eventually.of_forall hclip)]
      have hmean : (∫ b, X b ∂symmetricBernoulli) = τ • e := by
        rw [symmetricBernoulli, integral_bernoulliMeasure]
        simp [X, halfUnit]
      rw [hmean]
      have hzero :
          (∫ b, ‖radialClip τ (X b) - τ • e‖ ^ 2 ∂symmetricBernoulli) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with b
        rw [hclip b]
        simp [X]
      rw [hzero]
      simp [hτ.ne', hmoment.ne',
        (Real.rpow_pos_of_pos hτ (1 - p)).ne']
    · dsimp [stochasticClippingRatio]
      have hclip : ∀ b, radialClip τ (X b) = X b := by
        intro b
        apply radialClip_of_norm_le
        simp [X, hnorm, hτ.le]
      rw [integral_congr_ae (Filter.Eventually.of_forall hclip)]
      have hmean : (∫ b, X b ∂symmetricBernoulli) = τ • e := by
        rw [symmetricBernoulli, integral_bernoulliMeasure]
        simp [X, halfUnit]
      rw [hmean]
      simp [X, hnorm, hτ]
  rw [← hpair]
  exact ⟨law, rfl⟩

/-- A deterministic observation at the scalar maximizing radius realizes the
pure-bias endpoint `(energy,bias) = (0,cₚ)`. -/
theorem articleBiasAxisPair_mem
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ : ℝ} (hp : 1 < p) (hτ : 0 < τ) :
    (0, c_p p) ∈ articleAttainablePairs.{u, v} H p τ := by
  obtain ⟨e, he⟩ := exists_norm_eq_one (E := H)
  let r : ℝ := r_star 1 0 p
  have hr : 0 < r := by
    dsimp [r, r_star]
    positivity
  have hr1 : 1 < r := by
    dsimp [r, r_star]
    simp only [sub_zero, mul_one, one_mul]
    rw [lt_div_iff₀ (sub_pos.mpr hp)]
    nlinarith
  have hscalar : F 1 0 p r = c_p p := by
    have hreg : p * 0 < (1 : ℝ) := by simp
    calc
      F 1 0 p r = criticalValue 1 0 p := by
        simpa [r] using
          (F_at_r_star (α := 1) (β := 0) (by norm_num) hp hreg)
      _ = c_p p := by
        rw [criticalValue_closed_form (α := 1) (β := 0) (by norm_num) hp hreg]
        simp [c_p]
  let x : H := (τ * r) • e
  let y : H := τ • e
  have hτr : 0 < τ * r := mul_pos hτ hr
  have hxnorm : ‖x‖ = τ * r := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_pos hτr]
  have hclip : radialClip τ x = y := by
    have hlt : τ < ‖x‖ := by rw [hxnorm]; nlinarith
    rw [radialClip_of_lt_norm hlt, hxnorm]
    dsimp [x, y]
    rw [smul_smul]
    congr 1
    field_simp
  have hresid : ‖y - x‖ = τ * (r - 1) := by
    have hvec : y - x = (-(τ * (r - 1))) • e := by
      dsimp [x, y]
      module
    rw [hvec, norm_smul, Real.norm_eq_abs, he, abs_neg,
      abs_of_pos (mul_pos hτ (sub_pos.mpr hr1)), mul_one]
  have hmomentEq :
      (∫ b, ‖(fun _ : Bool => x) b‖ ^ p ∂symmetricBernoulli) =
        (τ * r) ^ p := by
    rw [symmetricBernoulli, integral_bernoulliMeasure]
    simp only [halfUnit, hxnorm]
    ring
  have hmoment : 0 < ∫ b, ‖(fun _ : Bool => x) b‖ ^ p ∂symmetricBernoulli := by
    rw [hmomentEq]
    exact Real.rpow_pos_of_pos hτr p
  let law0 : RandomVectorLaw.{0, v} H p :=
    { Ω := Bool
      mΩ := inferInstance
      μ := symmetricBernoulli
      probability := inferInstance
      X := fun _ => x
      memLp := MemLp.of_discrete
      moment_pos := hmoment }
  let law : RandomVectorLaw.{u, v} H p := law0.liftBool
  have hpair : law.biasEnergyPair τ = (0, c_p p) := by
    let e : Bool ≃ᵐ ULift.{u, 0} Bool := (MeasurableEquiv.ulift).symm
    change (stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 0 1 p τ
          (fun _ => x),
        stochasticClippingRatio (symmetricBernoulli.map
        ((MeasurableEquiv.ulift).symm)) 1 0 p τ
          (fun _ => x)) = (0, c_p p)
    rw [stochasticClippingRatio_map_equiv e symmetricBernoulli (fun _ => x),
      stochasticClippingRatio_map_equiv e symmetricBernoulli (fun _ => x)]
    have hmeanX : (∫ b, (fun _ : Bool => x) b ∂symmetricBernoulli) = x := by
      rw [symmetricBernoulli, integral_bernoulliMeasure]
      simp [halfUnit]
    have hmeanY :
        (∫ b, radialClip τ ((fun _ : Bool => x) b) ∂symmetricBernoulli) = y := by
      calc
        _ = ∫ _ : Bool, y ∂symmetricBernoulli := by
          apply integral_congr_ae
          filter_upwards with b
          exact hclip
        _ = y := by
          rw [symmetricBernoulli, integral_bernoulliMeasure]
          simp [halfUnit]
    have hvariance :
        (∫ b, ‖radialClip τ ((fun _ : Bool => x) b) - y‖ ^ 2
          ∂symmetricBernoulli) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with b
      rw [hclip]
      simp
    have hmomentEq :
        (∫ b, ‖(fun _ : Bool => x) b‖ ^ p ∂symmetricBernoulli) =
          (τ * r) ^ p := by
      exact hmomentEq
    have hpowτ : τ ^ (1 - p) * τ ^ p = τ := by
      rw [← Real.rpow_add hτ]
      norm_num
    have hden : τ ^ (1 - p) * (τ * r) ^ p = τ * r ^ p := by
      rw [Real.mul_rpow hτ.le hr.le]
      calc
        τ ^ (1 - p) * (τ ^ p * r ^ p) =
            (τ ^ (1 - p) * τ ^ p) * r ^ p := by ring
        _ = τ * r ^ p := by rw [hpowτ]
    have hratio : (τ * (r - 1)) / (τ * r ^ p) = c_p p := by
      calc
        (τ * (r - 1)) / (τ * r ^ p) = (r - 1) / r ^ p := by
          field_simp [hτ.ne', (Real.rpow_pos_of_pos hr p).ne']
        _ = F 1 0 p r := by
          symm
          simp [F, max_eq_left (sub_nonneg.mpr hr1.le),
            min_eq_right hr1.le]
        _ = c_p p := hscalar
    apply Prod.ext
    · dsimp [stochasticClippingRatio]
      rw [hmeanY, hvariance, hmomentEq, hden]
      simp [hτ.ne', hτr.ne']
    · dsimp [stochasticClippingRatio]
      rw [hmeanY, hmeanX, hresid, hmomentEq, hden]
      simpa [hτ.ne', hτr.ne'] using hratio
  rw [← hpair]
  exact ⟨law, rfl⟩

/-- In the signed branch `β < 0 < α`, the pure-bias endpoint realizes the
support value `α cₚ`. -/
theorem articleAttainablePair_attains_negativeBeta_positiveAlpha
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β : ℝ} (hp : 1 < p) (hτ : 0 < τ)
    (hβ : β < 0) (hα : 0 < α) :
    ∃ z ∈ articleAttainablePairs.{u, v} H p τ,
      α * z.2 + β * z.1 = signedSupportFormula α β p := by
  refine ⟨(0, c_p p), articleBiasAxisPair_mem hp hτ, ?_⟩
  simp [signedSupportFormula, hβ, not_le_of_gt hα]

/-- Values of one signed linear functional on the attainable bias--energy
set. -/
def articleSignedValues (H : Type v) [MeasurableSpace H]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (p τ α β : ℝ) : Set ℝ :=
  {s | ∃ z ∈ articleAttainablePairs.{u, v} H p τ,
    s = α * z.2 + β * z.1}

/-- The signed support formula is approached from below in every coefficient
regime (and attained in the three linear regimes). -/
theorem articleSignedValues_approach
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β ε : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hε : 0 < ε) :
    ∃ s ∈ articleSignedValues H p τ α β,
      signedSupportFormula α β p - ε < s := by
  by_cases hβ : β < 0
  · by_cases hα : α ≤ 0
    · refine ⟨0, ?_, ?_⟩
      · refine ⟨(0, 0), articleOrigin_mem hτ, ?_⟩
        simp
      · simp [signedSupportFormula, hβ, hα]
        exact hε
    · have hαpos : 0 < α := lt_of_not_ge hα
      obtain ⟨z, hz, hval⟩ :=
        articleAttainablePair_attains_negativeBeta_positiveAlpha (H := H)
          hp hτ hβ hαpos
      refine ⟨α * z.2 + β * z.1, ⟨z, hz, rfl⟩, ?_⟩
      rw [hval]
      linarith
  · have hβ0 : 0 ≤ β := le_of_not_gt hβ
    by_cases hreg : α ≤ p * β
    · obtain ⟨z, hz, hval⟩ :=
        articleAttainablePair_attains_endpoint_regime (H := H) hp hτ hβ0 hreg
      refine ⟨α * z.2 + β * z.1, ⟨z, hz, rfl⟩, ?_⟩
      rw [hval]
      linarith
    · have hreg' : p * β < α := lt_of_not_ge hreg
      obtain ⟨z, hz, hnear⟩ :=
        articleAttainablePair_epsilon_optimal_second_regime (H := H)
          hp hτ hβ0 hreg' hε
      have hform : signedSupportFormula α β p = K_p α β p := by
        simp [signedSupportFormula, hβ, hreg, K_p]
      refine ⟨α * z.2 + β * z.1, ⟨z, hz, rfl⟩, ?_⟩
      rw [hform]
      exact hnear

/-- For two negative coefficients the signed support is zero, attained at the
origin. -/
theorem articleAttainablePair_attains_negative_quadrant
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β : ℝ} (_hp : 1 < p) (hτ : 0 < τ)
    (hβ : β < 0) (hα : α ≤ 0) :
    ∃ z ∈ articleAttainablePairs.{u, v} H p τ,
      α * z.2 + β * z.1 = signedSupportFormula α β p := by
  refine ⟨(0, 0), articleOrigin_mem hτ, ?_⟩
  simp [signedSupportFormula, hβ, hα]

/-- Every pair from the article's all-law attainable set satisfies the
four-branch signed support upper bound. -/
theorem articleAttainablePair_le_signedSupportFormula
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {p τ α β : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    {z : ℝ × ℝ} (hz : z ∈ articleAttainablePairs.{u, v} H p τ) :
    α * z.2 + β * z.1 ≤ signedSupportFormula α β p := by
  rcases hz with ⟨law, rfl⟩
  letI : MeasurableSpace law.Ω := law.mΩ
  letI : IsProbabilityMeasure law.μ := law.probability
  let v : ℝ := stochasticClippingRatio law.μ 0 1 p τ law.X
  let d : ℝ := stochasticClippingRatio law.μ 1 0 p τ law.X
  have hden : 0 < τ ^ (1 - p) * (∫ ω, ‖law.X ω‖ ^ p ∂law.μ) := by
    exact mul_pos (Real.rpow_pos_of_pos hτ (1 - p)) law.moment_pos
  have hcoord (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      a * d + b * v ≤ K_p a b p := by
    have hlin : a * d + b * v = stochasticClippingRatio law.μ a b p τ law.X := by
      dsimp [d, v, stochasticClippingRatio]
      field_simp [hden.ne']
      ring
    rw [hlin]
    exact stochasticClippingRatio_le_K_p_of_memLp
      law.μ ha hb hp hp2 hτ law.X law.memLp law.moment_pos
  have hv0 : 0 ≤ v := by
    dsimp [v, stochasticClippingRatio]
    apply div_nonneg
    · apply add_nonneg
      · positivity
      · positivity
    · positivity
  have hd0 : 0 ≤ d := by
    dsimp [d, stochasticClippingRatio]
    apply div_nonneg
    · apply add_nonneg
      · positivity
      · positivity
    · positivity
  have hv1 : v ≤ 1 := by
    have h := hcoord 0 1 (by norm_num) (by norm_num)
    have hp0 : 0 ≤ p := by linarith
    dsimp [v] at h ⊢
    simp [K_p, hp0] at h
    simpa using h
  have hdc : d ≤ c_p p := by
    have h := hcoord 1 0 (by norm_num) (by norm_num)
    have hK : K_p 1 0 p = c_p p := by
      rw [K_p]
      simp [c_p]
    dsimp [d] at h ⊢
    rw [hK] at h
    simpa using h
  have henv : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a * d + b * v ≤ K_p a b p :=
    fun a b ha hb => hcoord a b ha hb
  exact signed_linear_form_le_formula_of_envelope hp hv0 hd0 hv1 hdc henv

/-- The supremum of the signed functional over all admissible laws is the
four-branch support expression in the article. -/
theorem articleSignedValues_isLUB
    {H : Type v} [MeasurableSpace H] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    {p τ α β : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ) :
    IsLUB (articleSignedValues H p τ α β) (signedSupportFormula α β p) := by
  refine ⟨?_, ?_⟩
  · intro s hs
    rcases hs with ⟨z, hz, rfl⟩
    exact articleAttainablePair_le_signedSupportFormula hp hp2 hτ hz
  · intro b hb
    by_contra hnot
    have hgap : 0 < signedSupportFormula α β p - b :=
      sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨s, hs, hnear⟩ :=
      articleSignedValues_approach (H := H) hp hp2 hτ (half_pos hgap)
    have hb' : s ≤ b := hb hs
    linarith
