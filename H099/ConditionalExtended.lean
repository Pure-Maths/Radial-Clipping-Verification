import H099.ConditionalL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-!
# The full conditional H099 envelope without a global `L²` assumption

The Bochner conditional expectation in mathlib is totalized to zero on
non-integrable functions.  Consequently the conditional variance in the full
random-threshold theorem is represented canonically by the extended
nonnegative conditional expectation `condLExp`.  The theorem below proves
that this extended value is finite almost everywhere and then exports the
paper-facing real-valued statement through `ENNReal.toReal`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {Ω H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Extended conditional second central moment.  This remains meaningful when
the square is not globally integrable. -/
def condVarENN
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (Y : Ω → H) : Ω → ℝ≥0∞ :=
  μ⁻[(fun z =>
    ENNReal.ofReal
      (‖Y z - μ[Y | m] z‖ ^ 2)) | m]

/-- Real representative of `condVarENN`.  Statements using this definition
should also provide an a.e. proof that `condVarENN` is finite. -/
def condVarReal
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (Y : Ω → H) : Ω → ℝ :=
  fun ω => (condVarENN (m := m) μ Y ω).toReal

omit [CompleteSpace H] in
lemma measurable_condVarENN
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (Y : Ω → H) :
    Measurable[m] (condVarENN (m := m) μ Y) :=
  measurable_condLExp m μ _

/-- Extended-valued form of the full random-threshold contract. -/
def FullConditionalENNStatement
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (α β p : ℝ) (τ : Ω → ℝ) (X : Ω → H) : Prop :=
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  let mX : Ω → H := μ[X | m]
  let b : Ω → H := μ[Y | m]
  (fun ω =>
      ENNReal.ofReal (α * ‖b ω - mX ω‖)
        + ENNReal.ofReal (β / τ ω) *
            condVarENN (m := m) μ Y ω)
    ≤ᵐ[μ]
      (fun ω =>
        ENNReal.ofReal
            (K_p α β p * (τ ω) ^ (1 - p))
          * μ⁻[(fun z =>
              ENNReal.ofReal (‖X z‖ ^ p)) | m] ω)

/-- Paper-facing real-valued form of the full random-threshold contract. -/
def FullConditionalRealStatement
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    (α β p : ℝ) (τ : Ω → ℝ) (X : Ω → H) : Prop :=
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  let mX : Ω → H := μ[X | m]
  let b : Ω → H := μ[Y | m]
  (fun ω =>
      α * ‖b ω - mX ω‖
        + (β / τ ω) * condVarReal (m := m) μ Y ω)
    ≤ᵐ[μ]
      (fun ω =>
        (K_p α β p * (τ ω) ^ (1 - p))
          * μ[(fun z => ‖X z‖ ^ p) | m] ω)

/-- Conditional Lebesgue expectation commutes with restriction to a set in
the conditioning sigma-algebra. -/
lemma condLExp_restrict_ae_eq_restrict
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set Ω} (hs : MeasurableSet[m] s) (f : Ω → ℝ≥0∞) :
    (μ.restrict s)⁻[f | m] =ᵐ[μ.restrict s] μ⁻[f | m] := by
  haveI : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    infer_instance
  refine (ae_eq_condLExp hm (μ.restrict s) f
    (measurable_condLExp m μ f) ?_).symm
  intro t ht
  calc
    (∫⁻ ω in t, μ⁻[f | m] ω ∂μ.restrict s)
        = ∫⁻ ω in s ∩ t, μ⁻[f | m] ω ∂μ := by
            rw [Measure.restrict_restrict (hm _ ht), Set.inter_comm]
    _ = ∫⁻ ω in s ∩ t, f ω ∂μ :=
      setLIntegral_condLExp hm μ f (hs.inter ht)
    _ = ∫⁻ ω in t, f ω ∂μ.restrict s := by
            rw [Measure.restrict_restrict (hm _ ht), Set.inter_comm]

/-- On a conditioning-measurable localization where `f` is integrable, the
global extended conditional expectation agrees after `toReal` with the
ordinary conditional expectation for the restricted measure. -/
lemma toReal_condLExp_eq_condExp_on_restrict
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set Ω} (hs : MeasurableSet[m] s) {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f (μ.restrict s))
    (hfin : ∫⁻ ω, f ω ∂μ.restrict s ≠ ∞) :
    (fun ω => (μ⁻[f | m] ω).toReal)
      =ᵐ[μ.restrict s]
        (μ.restrict s)[(fun ω => (f ω).toReal) | m] := by
  haveI : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    infer_instance
  have hrestrict :=
    condLExp_restrict_ae_eq_restrict (μ := μ) hm hs f
  have hbridge :=
    toReal_condLExp (μ := μ.restrict s) m hf hfin
  filter_upwards [hrestrict, hbridge] with ω hrestrictω hbridgeω
  rw [← hrestrictω]
  exact hbridgeω

omit [CompleteSpace H] in
lemma condVarReal_eq_condExp_on_restrict
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set Ω} (hs : MeasurableSet[m] s) (Y : Ω → H)
    (henergy :
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict s)) :
    condVarReal (m := m) μ Y
      =ᵐ[μ.restrict s]
        (μ.restrict s)[
          (fun z => ‖Y z - μ[Y | m] z‖ ^ 2) | m] := by
  let e : Ω → ℝ :=
    fun z => ‖Y z - μ[Y | m] z‖ ^ 2
  let f : Ω → ℝ≥0∞ := fun z => ENNReal.ofReal (e z)
  have hf : AEMeasurable f (μ.restrict s) :=
    henergy.1.aemeasurable.ennreal_ofReal
  have hfin : ∫⁻ z, f z ∂μ.restrict s ≠ ∞ := by
    have hfeq : f = fun z => ‖e z‖ₑ := by
      funext z
      simp [f, e, Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [hfeq]
    exact henergy.2.ne
  have hbridge :=
    toReal_condLExp_eq_condExp_on_restrict
      (μ := μ) hm hs hf hfin
  change
    (fun ω =>
      (μ⁻[(fun z =>
        ENNReal.ofReal
          (‖Y z - μ[Y | m] z‖ ^ 2)) | m] ω).toReal)
      =ᵐ[μ.restrict s]
        (μ.restrict s)[
          (fun z => ‖Y z - μ[Y | m] z‖ ^ 2) | m]
  simpa [f, e,
    ENNReal.toReal_ofReal (sq_nonneg _)] using hbridge

omit [CompleteSpace H] in
lemma condVarENN_ne_top_on_restrict
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {s : Set Ω} (hs : MeasurableSet[m] s) (Y : Ω → H)
    (henergy :
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict s)) :
    ∀ᵐ ω ∂μ.restrict s, condVarENN (m := m) μ Y ω ≠ ∞ := by
  let e : Ω → ℝ :=
    fun z => ‖Y z - μ[Y | m] z‖ ^ 2
  let f : Ω → ℝ≥0∞ := fun z => ENNReal.ofReal (e z)
  have hfin : ∫⁻ z, f z ∂μ.restrict s ≠ ∞ := by
    have hfeq : f = fun z => ‖e z‖ₑ := by
      funext z
      simp [f, e, Real.enorm_eq_ofReal (sq_nonneg _)]
    rw [hfeq]
    exact henergy.2.ne
  haveI : SigmaFinite ((μ.restrict s).trim hm) := by
    rw [← restrict_trim hm _ hs]
    infer_instance
  have hlocal :
      ∀ᵐ ω ∂μ.restrict s,
        (μ.restrict s)⁻[f | m] ω ≠ ∞ :=
    condLExp_ne_top hfin
  have hrestrict :=
    condLExp_restrict_ae_eq_restrict (μ := μ) hm hs f
  filter_upwards [hlocal, hrestrict] with ω hlocalω hrestrictω
  change μ⁻[f | m] ω ≠ ∞
  rw [← hrestrictω]
  exact hlocalω

omit [CompleteSpace H] in
lemma condVarENN_ne_top_of_ae_cover
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (sets : ℕ → Set Ω) (hsets : ∀ n, MeasurableSet[m] (sets n))
    (hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n)
    (Y : Ω → H)
    (henergy : ∀ n,
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict (sets n))) :
    ∀ᵐ ω ∂μ, condVarENN (m := m) μ Y ω ≠ ∞ := by
  have hlocal : ∀ n,
      ∀ᵐ ω ∂μ.restrict (sets n),
        condVarENN (m := m) μ Y ω ≠ ∞ :=
    fun n =>
      condVarENN_ne_top_on_restrict
        (μ := μ) hm (hsets n) Y (henergy n)
  have hunion :
      ∀ᵐ ω ∂μ.restrict (⋃ n, sets n),
        condVarENN (m := m) μ Y ω ≠ ∞ :=
    (ae_restrict_iUnion_iff sets _).2 hlocal
  have himp :
      ∀ᵐ ω ∂μ,
        ω ∈ ⋃ n, sets n →
          condVarENN (m := m) μ Y ω ≠ ∞ :=
    ae_imp_of_ae_restrict hunion
  filter_upwards [hcover, himp] with ω hω himpω
  exact himpω hω

lemma ae_of_ae_restrict_iUnion
    {mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (sets : ℕ → Set Ω) {P : Ω → Prop}
    (hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n)
    (hlocal : ∀ n, ∀ᵐ ω ∂μ.restrict (sets n), P ω) :
    ∀ᵐ ω ∂μ, P ω := by
  have hunion : ∀ᵐ ω ∂μ.restrict (⋃ n, sets n), P ω :=
    (ae_restrict_iUnion_iff sets P).2 hlocal
  have himp : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n → P ω :=
    ae_imp_of_ae_restrict hunion
  filter_upwards [hcover, himp] with ω hω himpω
  exact himpω hω

omit [CompleteSpace H] in
/-- A local ordinary-`condExp` inequality on a countable conditioning-
measurable cover produces the canonical global `condLExp.toReal` statement
and proves that the extended variance is finite almost everywhere. -/
theorem fullConditionalReal_of_local
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    {α β p : ℝ} (τ : Ω → ℝ) (X Y : Ω → H)
    (sets : ℕ → Set Ω) (hsets : ∀ n, MeasurableSet[m] (sets n))
    (hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n)
    (henergy : ∀ n,
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict (sets n)))
    (hlocal : ∀ n,
      (fun ω =>
          α * ‖μ[Y | m] ω - μ[X | m] ω‖
            + (β / τ ω) *
                (μ.restrict (sets n))[
                  (fun z => ‖Y z - μ[Y | m] z‖ ^ 2) | m] ω)
        ≤ᵐ[μ.restrict (sets n)]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p))
              * μ[(fun z => ‖X z‖ ^ p) | m] ω)) :
    (∀ᵐ ω ∂μ, condVarENN (m := m) μ Y ω ≠ ∞)
      ∧
      ((fun ω =>
          α * ‖μ[Y | m] ω - μ[X | m] ω‖
            + (β / τ ω) * condVarReal (m := m) μ Y ω)
        ≤ᵐ[μ]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p))
              * μ[(fun z => ‖X z‖ ^ p) | m] ω)) := by
  constructor
  · exact
      condVarENN_ne_top_of_ae_cover
        (μ := μ) hm sets hsets hcover Y henergy
  · apply ae_of_ae_restrict_iUnion sets hcover
    intro n
    have hbridge :=
      condVarReal_eq_condExp_on_restrict
        (μ := μ) hm (hsets n) Y (henergy n)
    filter_upwards [hbridge, hlocal n] with ω hbridgeω hlocalω
    rw [hbridgeω]
    exact hlocalω

/-- Extended-valued conditional Hilbert variance inequality.  Unlike
`condExp_hilbert_variance_identity`, this only assumes `Y ∈ L¹`; neither side
needs to be globally finite. -/
theorem condLExp_hilbert_variance_le
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)]
    (Y : Ω → H) (hY : Integrable Y μ) :
    μ⁻[(fun ω => ENNReal.ofReal
          (‖Y ω - μ[Y | m] ω‖ ^ 2)) | m]
      ≤ᵐ[μ]
        μ⁻[(fun ω => ENNReal.ofReal (‖Y ω‖ ^ 2)) | m] := by
  apply ae_le_of_ae_le_trim
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (μ := μ.trim hm)
    (g := μ⁻[(fun ω => ENNReal.ofReal (‖Y ω‖ ^ 2)) | m])
    (measurable_condLExp m μ
      (fun ω => ENNReal.ofReal (‖Y ω - μ[Y | m] ω‖ ^ 2)))
  intro s hs hμs
  rw [setLIntegral_condLExp_trim hm μ _ hs,
    setLIntegral_condLExp_trim hm μ _ hs]
  by_cases htop :
      ∫⁻ ω in s, ENNReal.ofReal (‖Y ω‖ ^ 2) ∂μ = ∞
  · rw [htop]
    exact le_top
  let ν : Measure[mΩ] Ω := μ.restrict s
  have hμs' : μ s < ∞ := by
    rwa [← trim_measurableSet_eq hm hs]
  letI : IsFiniteMeasure ν :=
    ⟨by simpa [ν] using hμs'⟩
  have hYν : Integrable Y ν := hY.restrict
  have hYsqν : Integrable (fun ω => ‖Y ω‖ ^ 2) ν := by
    refine ⟨hY.aestronglyMeasurable.restrict.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_of_nonneg (sq_nonneg _)]
    change
      ∫⁻ ω in s, ENNReal.ofReal (‖Y ω‖ ^ 2) ∂μ < ∞
    exact lt_top_iff_ne_top.mpr htop
  have hY2ν : MemLp Y 2 ν :=
    (memLp_two_iff_integrable_sq_norm hYν.1).2 hYsqν
  have hrestr :
      ν[Y | m] =ᵐ[ν] μ[Y | m] :=
    condExp_restrict_ae_eq_restrict hm hs hY
  have hlocalVar :=
    condExp_hilbert_variance_identity (μ := ν) hm Y hY2ν
  have hlocalVarLe :
      ν[(fun ω => ‖Y ω - ν[Y | m] ω‖ ^ 2) | m]
        ≤ᵐ[ν] ν[(fun ω => ‖Y ω‖ ^ 2) | m] := by
    filter_upwards [hlocalVar] with ω hω
    rw [hω]
    exact sub_le_self _ (sq_nonneg _)
  have hb2ν : MemLp (ν[Y | m]) 2 ν :=
    MemLp.condExp one_le_two hY2ν
  have hresν :
      Integrable (fun ω => ‖Y ω - ν[Y | m] ω‖ ^ 2) ν := by
    exact
      ((memLp_two_iff_integrable_sq_norm
          (hY2ν.aestronglyMeasurable.sub hb2ν.aestronglyMeasurable)).1
        (hY2ν.sub hb2ν))
  have hleftCE :=
    condLExp_ofReal m hresν
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hrightCE :=
    condLExp_ofReal m hYsqν
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hcondLExpLe :
      ν⁻[(fun ω => ENNReal.ofReal
            (‖Y ω - ν[Y | m] ω‖ ^ 2)) | m]
        ≤ᵐ[ν]
          ν⁻[(fun ω => ENNReal.ofReal (‖Y ω‖ ^ 2)) | m] := by
    filter_upwards [hleftCE, hrightCE, hlocalVarLe]
      with ω hleftω hrightω hleω
    rw [hleftω, hrightω]
    exact ENNReal.ofReal_le_ofReal hleω
  have hlinLocal :
      ∫⁻ ω, ENNReal.ofReal (‖Y ω - ν[Y | m] ω‖ ^ 2) ∂ν
        ≤ ∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 2) ∂ν := by
    calc
      _ = ∫⁻ ω,
          ν⁻[(fun z => ENNReal.ofReal
            (‖Y z - ν[Y | m] z‖ ^ 2)) | m] ω ∂ν :=
        (lintegral_condLExp hm ν _).symm
      _ ≤ ∫⁻ ω,
          ν⁻[(fun z => ENNReal.ofReal (‖Y z‖ ^ 2)) | m] ω ∂ν :=
        lintegral_mono_ae hcondLExpLe
      _ = _ := lintegral_condLExp hm ν _
  have hleftCongr :
      (fun ω => ENNReal.ofReal (‖Y ω - ν[Y | m] ω‖ ^ 2))
        =ᵐ[ν]
      (fun ω => ENNReal.ofReal (‖Y ω - μ[Y | m] ω‖ ^ 2)) := by
    filter_upwards [hrestr] with ω hω
    rw [hω]
  rw [lintegral_congr_ae hleftCongr] at hlinLocal
  exact hlinLocal

/-- The threshold band on which both `τ` and `τ⁻¹` are uniformly bounded. -/
def thresholdBand (τ : Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | 1 / ((n : ℝ) + 1) ≤ τ ω ∧ τ ω ≤ (n : ℝ) + 1}

lemma measurableSet_thresholdBand
    {m : MeasurableSpace Ω} {τ : Ω → ℝ}
    (hτ : StronglyMeasurable[m] τ) (n : ℕ) :
    MeasurableSet[m] (thresholdBand τ n) := by
  exact
    (stronglyMeasurable_const.measurableSet_le hτ).inter
      (hτ.measurableSet_le stronglyMeasurable_const)

lemma thresholdBand_mono (τ : Ω → ℝ) :
    Monotone (thresholdBand τ) := by
  intro n k hnk ω hω
  have hcast : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hnk 1
  have hnpos : 0 < (n : ℝ) + 1 := by positivity
  exact
    ⟨(one_div_le_one_div_of_le hnpos hcast).trans hω.1,
      hω.2.trans hcast⟩

lemma iUnion_thresholdBand (τ : Ω → ℝ) :
    (⋃ n : ℕ, thresholdBand τ n) = {ω | 0 < τ ω} := by
  ext ω
  constructor
  · intro hω
    obtain ⟨n, hω⟩ := Set.mem_iUnion.1 hω
    exact (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
  · intro hτω
    obtain ⟨n, hn⟩ :=
      exists_nat_gt (max (τ ω) (1 / τ ω))
    have hu : τ ω < (n : ℝ) :=
      (le_max_left _ _).trans_lt hn
    have hi : 1 / τ ω < (n : ℝ) :=
      (le_max_right _ _).trans_lt hn
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    constructor
    · have hnpos : 0 < (n : ℝ) + 1 := by positivity
      apply (div_le_iff₀ hnpos).2
      have hmul : 1 < (n : ℝ) * τ ω :=
        (div_lt_iff₀ hτω).1 hi
      nlinarith
    · linarith

lemma ae_iUnion_thresholdBand
    {m : MeasurableSpace Ω} {μ : Measure[m] Ω}
    {τ : Ω → ℝ} (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω) :
    ∀ᵐ ω ∂μ, ω ∈ ⋃ n : ℕ, thresholdBand τ n := by
  filter_upwards [hτpos] with ω hω
  rw [iUnion_thresholdBand]
  exact hω

omit [CompleteSpace H] in
lemma memLp_two_variable_radialClip_restrict_thresholdBand
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    {X : Ω → H} (hX : AEStronglyMeasurable X μ) (n : ℕ) :
    MemLp (fun ω => radialClip (τ ω) (X ω)) 2
      (μ.restrict (thresholdBand τ n)) := by
  let A := thresholdBand τ n
  have hA : MeasurableSet[mΩ] A :=
    hm _ (measurableSet_thresholdBand hτ n)
  have hYmeas :
      AEStronglyMeasurable (fun ω => radialClip (τ ω) (X ω))
        (μ.restrict A) :=
    (aestronglyMeasurable_variable_radialClip hm hX hτ).mono_measure
      Measure.restrict_le_self
  refine (memLp_const (((n : ℝ) + 1) : ℝ)).mono' hYmeas ?_
  filter_upwards [ae_restrict_mem hA] with ω hω
  have hτpos : 0 < τ ω :=
    (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
  rw [norm_radialClip hτpos]
  exact (min_le_right _ _).trans hω.2

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma integrable_pMoment_restrict_thresholdBand
    {mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    {p : ℝ} (hp : 0 < p) {X : Ω → H}
    (hLp : MemLp X (ENNReal.ofReal p) μ)
    (τ : Ω → ℝ) (n : ℕ) :
    Integrable (fun ω => ‖X ω‖ ^ p)
      (μ.restrict (thresholdBand τ n)) := by
  have hLpA := hLp.restrict (thresholdBand τ n)
  have hpow := hLpA.integrable_norm_rpow
    (by simpa using hp)
    (by simp)
  simpa [ENNReal.toReal_ofReal hp.le] using hpow

omit [CompleteSpace H] in
lemma integrable_weightedY_restrict_thresholdBand
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    {X : Ω → H} (hX : AEStronglyMeasurable X μ)
    (β : ℝ) (n : ℕ) :
    Integrable
      (fun ω => (β / τ ω) *
        ‖radialClip (τ ω) (X ω)‖ ^ 2)
      (μ.restrict (thresholdBand τ n)) := by
  let A := thresholdBand τ n
  have hA : MeasurableSet[mΩ] A :=
    hm _ (measurableSet_thresholdBand hτ n)
  have hY2 : MemLp (fun ω => radialClip (τ ω) (X ω)) 2
      (μ.restrict A) :=
    memLp_two_variable_radialClip_restrict_thresholdBand
      hm hτ hX n
  have hYsq :
      Integrable
        (fun ω => ‖radialClip (τ ω) (X ω)‖ ^ 2)
        (μ.restrict A) :=
    hY2.integrable_norm_pow (by norm_num)
  have hβstrong : StronglyMeasurable[mΩ] (fun ω => β / τ ω) :=
    (stronglyMeasurable_const.div hτ).mono hm
  have hβmeas :
      AEStronglyMeasurable (fun ω => β / τ ω) (μ.restrict A) :=
    hβstrong.aestronglyMeasurable
  have hβbound :
      ∀ᵐ ω ∂μ.restrict A,
        ‖β / τ ω‖ ≤ |β| * ((n : ℝ) + 1) := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    have hNpos : 0 < (n : ℝ) + 1 := by positivity
    have hτpos : 0 < τ ω :=
      (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
    have hinv : 1 / τ ω ≤ (n : ℝ) + 1 := by
      apply (div_le_iff₀ hτpos).2
      have hmul : 1 ≤ τ ω * ((n : ℝ) + 1) :=
        (div_le_iff₀ hNpos).1 hω.1
      nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hτpos, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div] using hinv) (abs_nonneg β)
  exact hYsq.bdd_mul hβmeas hβbound

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma integrable_weightedX_restrict_thresholdBand
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    (hm : m ≤ mΩ)
    {p : ℝ} (hp : 1 < p)
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    {X : Ω → H} (hLp : MemLp X (ENNReal.ofReal p) μ)
    (K : ℝ) (n : ℕ) :
    Integrable
      (fun ω => (K * (τ ω) ^ (1 - p)) * ‖X ω‖ ^ p)
      (μ.restrict (thresholdBand τ n)) := by
  let A := thresholdBand τ n
  have hA : MeasurableSet[mΩ] A :=
    hm _ (measurableSet_thresholdBand hτ n)
  have hτposA : ∀ᵐ ω ∂μ.restrict A, 0 < τ ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    exact (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
  have hpowmeas :
      AEStronglyMeasurable (fun ω => (τ ω) ^ (1 - p))
        (μ.restrict A) :=
    aestronglyMeasurable_rpow_of_stronglyMeasurable_pos
      (hτ.mono hm) hτposA (1 - p)
  have hKmeas :
      AEStronglyMeasurable (fun ω => K * (τ ω) ^ (1 - p))
        (μ.restrict A) :=
    hpowmeas.const_mul K
  have hKbound :
      ∀ᵐ ω ∂μ.restrict A,
        ‖K * (τ ω) ^ (1 - p)‖
          ≤ |K| * (1 / ((n : ℝ) + 1)) ^ (1 - p) := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    have hlowpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hτpos : 0 < τ ω := hlowpos.trans_le hω.1
    have hrpow :
        (τ ω) ^ (1 - p)
          ≤ (1 / ((n : ℝ) + 1)) ^ (1 - p) :=
      Real.rpow_le_rpow_of_nonpos hlowpos hω.1 (by linarith)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hτpos.le _)]
    exact mul_le_mul_of_nonneg_left hrpow (abs_nonneg K)
  have hXp :
      Integrable (fun ω => ‖X ω‖ ^ p) (μ.restrict A) :=
    integrable_pMoment_restrict_thresholdBand (zero_lt_one.trans hp)
      hLp τ n
  exact hXp.bdd_mul hKmeas hKbound

omit [CompleteSpace H] in
lemma integrable_variable_radialClip_of_memLp
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {p : ℝ} (hp : 1 < p)
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    {X : Ω → H} (hLp : MemLp X (ENNReal.ofReal p) μ) :
    Integrable (fun ω => radialClip (τ ω) (X ω)) μ := by
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hYmeas :
      AEStronglyMeasurable (fun ω => radialClip (τ ω) (X ω)) μ :=
    aestronglyMeasurable_variable_radialClip hm hLp.1 hτ
  refine Integrable.mono hX hYmeas ?_
  filter_upwards [hτpos] with ω hτω
  rw [norm_radialClip hτω]
  exact min_le_left _ _

lemma condExp_variable_radialClip_restrict_thresholdBand
    {m mΩ : MeasurableSpace Ω} {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {p : ℝ} (hp : 1 < p)
    {τ : Ω → ℝ} (hτ : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    {X : Ω → H} (hLp : MemLp X (ENNReal.ofReal p) μ)
    (n : ℕ) :
    (μ.restrict (thresholdBand τ n))[
        (fun ω => radialClip (τ ω) (X ω)) | m]
      =ᵐ[μ.restrict (thresholdBand τ n)]
        μ[(fun ω => radialClip (τ ω) (X ω)) | m] := by
  exact condExp_restrict_ae_eq_restrict hm
    (measurableSet_thresholdBand hτ n)
    (integrable_variable_radialClip_of_memLp
      hm hp hτ hτpos hLp)

/-- Every threshold band satisfies all hypotheses of the finite-measure
conditional theorem. -/
theorem conditional_radialClip_envelope_on_thresholdBand
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (τ : Ω → ℝ) (hτ : StronglyMeasurable[m] τ)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ)
    (n : ℕ) :
    let A := thresholdBand τ n
    let μA := μ.restrict A
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    let mX : Ω → H := μA[X | m]
    let b : Ω → H := μA[Y | m]
    (fun ω =>
        α * ‖b ω - mX ω‖
          + (β / τ ω) *
              μA[(fun z => ‖Y z - b z‖ ^ 2) | m] ω)
      ≤ᵐ[μA]
        (fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) *
            μA[(fun z => ‖X z‖ ^ p) | m] ω) := by
  dsimp only
  let A := thresholdBand τ n
  have hA : MeasurableSet[mΩ] A :=
    hm _ (measurableSet_thresholdBand hτ n)
  have hτposA : ∀ᵐ ω ∂μ.restrict A, 0 < τ ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω
    exact (by positivity : 0 < 1 / ((n : ℝ) + 1)).trans_le hω.1
  have hβscaleA :
      AEStronglyMeasurable[m] (fun ω => β / τ ω) (μ.restrict A) :=
    (stronglyMeasurable_const.div hτ).aestronglyMeasurable
  have hpowA :
      AEStronglyMeasurable[m] (fun ω => (τ ω) ^ (1 - p))
        (μ.restrict A) :=
    aestronglyMeasurable_rpow_of_stronglyMeasurable_pos
      hτ hτposA (1 - p)
  have hKscaleA :
      AEStronglyMeasurable[m]
        (fun ω => K_p α β p * (τ ω) ^ (1 - p))
        (μ.restrict A) :=
    hpowA.const_mul (K_p α β p)
  have hLpA :
      MemLp X (ENNReal.ofReal p) (μ.restrict A) :=
    hLp.restrict A
  have hY2A :
      MemLp (fun ω => radialClip (τ ω) (X ω)) 2
        (μ.restrict A) :=
    memLp_two_variable_radialClip_restrict_thresholdBand
      hm hτ hLp.1 n
  have hweightedYA :
      Integrable
        (fun ω => (β / τ ω) *
          ‖radialClip (τ ω) (X ω)‖ ^ 2)
        (μ.restrict A) :=
    integrable_weightedY_restrict_thresholdBand
      hm hτ hLp.1 β n
  have hweightedXA :
      Integrable
        (fun ω =>
          (K_p α β p * (τ ω) ^ (1 - p)) * ‖X ω‖ ^ p)
        (μ.restrict A) :=
    integrable_weightedX_restrict_thresholdBand
      hm hp hτ hLp (K_p α β p) n
  exact
    conditional_radialClip_envelope_variable_L2
      (μ.restrict A) hm hα hβ hp hp2 τ hτposA X hLpA
      hβscaleA hKscaleA hY2A hweightedYA hweightedXA

/-- Full random-threshold conditional H099 contract, with the potentially
non-globally-integrable conditional variance represented canonically by
`condLExp` and converted back to `ℝ` after proving a.e. finiteness. -/
theorem conditional_radialClip_envelope_variable_full
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (τ : Ω → ℝ) (hτmeas : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ) :
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    (∀ᵐ ω ∂μ, condVarENN (m := m) μ Y ω ≠ ∞)
      ∧
      ((fun ω =>
          α * ‖μ[Y | m] ω - μ[X | m] ω‖
            + (β / τ ω) * condVarReal (m := m) μ Y ω)
        ≤ᵐ[μ]
          (fun ω =>
            (K_p α β p * (τ ω) ^ (1 - p))
              * μ[(fun z => ‖X z‖ ^ p) | m] ω)) := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  have hX : Integrable X μ :=
    hLp.integrable (ENNReal.one_le_ofReal.mpr hp.le)
  have hYmeas : AEStronglyMeasurable Y μ := by
    exact aestronglyMeasurable_variable_radialClip hm hLp.1 hτmeas
  have hY : Integrable Y μ := by
    apply hX.mono hYmeas
    filter_upwards [hτpos] with ω hτω
    dsimp [Y]
    rw [norm_radialClip hτω]
    exact min_le_left _ _
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hLp.integrable_norm_rpow'
  let sets : ℕ → Set Ω := thresholdBand τ
  have hsets : ∀ n, MeasurableSet[m] (sets n) :=
    fun n => measurableSet_thresholdBand hτmeas n
  have hcover : ∀ᵐ ω ∂μ, ω ∈ ⋃ n, sets n := by
    simpa [sets] using ae_iUnion_thresholdBand hτpos
  have henergy : ∀ n,
      Integrable
        (fun z => ‖Y z - μ[Y | m] z‖ ^ 2)
        (μ.restrict (sets n)) := by
    intro n
    let A := sets n
    have hY2A : MemLp Y 2 (μ.restrict A) := by
      simpa [Y, A, sets] using
        memLp_two_variable_radialClip_restrict_thresholdBand
          (μ := μ) hm hτmeas hLp.1 n
    have hb2A :
        MemLp ((μ.restrict A)[Y | m]) 2 (μ.restrict A) :=
      MemLp.condExp one_le_two hY2A
    have hrestrict :
        (μ.restrict A)[Y | m] =ᵐ[μ.restrict A] μ[Y | m] :=
      condExp_restrict_ae_eq_restrict hm (hsets n) hY
    have hb2global : MemLp (μ[Y | m]) 2 (μ.restrict A) :=
      MemLp.ae_eq hrestrict hb2A
    exact (hY2A.sub hb2global).integrable_norm_pow'
  apply fullConditionalReal_of_local
    (μ := μ) hm τ X Y sets hsets hcover henergy
  intro n
  let A := sets n
  have hband :=
    conditional_radialClip_envelope_on_thresholdBand
      μ hm hα hβ hp hp2 τ hτmeas X hLp n
  have hXrestrict :
      (μ.restrict A)[X | m] =ᵐ[μ.restrict A] μ[X | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hX
  have hYrestrict :
      (μ.restrict A)[Y | m] =ᵐ[μ.restrict A] μ[Y | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hY
  have hXprestrict :
      (μ.restrict A)[(fun z => ‖X z‖ ^ p) | m]
        =ᵐ[μ.restrict A]
          μ[(fun z => ‖X z‖ ^ p) | m] :=
    condExp_restrict_ae_eq_restrict hm (hsets n) hXp
  have hcenter :
      (μ.restrict A)[
          (fun z =>
            ‖Y z - (μ.restrict A)[Y | m] z‖ ^ 2) | m]
        =ᵐ[μ.restrict A]
          (μ.restrict A)[
            (fun z => ‖Y z - μ[Y | m] z‖ ^ 2) | m] := by
    apply condExp_congr_ae
    filter_upwards [hYrestrict] with z hz
    rw [hz]
  filter_upwards [hband, hXrestrict, hYrestrict, hXprestrict, hcenter] with
    ω hbandω hXω hYω hXpω hcenterω
  simp only [A, sets, Y] at hXω hYω hXpω hcenterω ⊢
  rw [hXω, hYω, hXpω, hcenterω] at hbandω
  simpa only using hbandω

/-- Extended-valued theorem together with the a.e.-finiteness certificate and
its paper-facing real `toReal` corollary. -/
theorem conditional_radialClip_envelope_variable_full_extended
    {m mΩ : MeasurableSpace Ω} (μ : Measure[mΩ] Ω)
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    [SigmaFinite (μ.trim hm)]
    {α β p : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hp : 1 < p) (hp2 : p ≤ 2)
    (τ : Ω → ℝ) (hτmeas : StronglyMeasurable[m] τ)
    (hτpos : ∀ᵐ ω ∂μ, 0 < τ ω)
    (X : Ω → H) (hLp : MemLp X (ENNReal.ofReal p) μ) :
    let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
    FullConditionalENNStatement (m := m) μ α β p τ X
      ∧ (∀ᵐ ω ∂μ, condVarENN (m := m) μ Y ω ≠ ∞)
      ∧ FullConditionalRealStatement (m := m) μ α β p τ X := by
  dsimp only
  let Y : Ω → H := fun ω => radialClip (τ ω) (X ω)
  have hfull :=
    conditional_radialClip_envelope_variable_full
      μ hm hα hβ hp hp2 τ hτmeas hτpos X hLp
  dsimp only at hfull
  rcases hfull with ⟨hfin, hreal⟩
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  have hXp : Integrable (fun ω => ‖X ω‖ ^ p) μ := by
    simpa [ENNReal.toReal_ofReal hp0] using hLp.integrable_norm_rpow'
  have hpow_nonneg : 0 ≤ᵐ[μ] (fun ω => ‖X ω‖ ^ p) :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hbridge :=
    condLExp_ofReal m hXp hpow_nonneg
  have hcond_nonneg :
      0 ≤ᵐ[μ] μ[(fun ω => ‖X ω‖ ^ p) | m] :=
    condExp_nonneg hpow_nonneg
  have henn :
      (fun ω =>
          ENNReal.ofReal
              (α * ‖μ[Y | m] ω - μ[X | m] ω‖)
            + ENNReal.ofReal (β / τ ω) *
                condVarENN (m := m) μ Y ω)
        ≤ᵐ[μ]
          (fun ω =>
            ENNReal.ofReal
                (K_p α β p * (τ ω) ^ (1 - p))
              * μ⁻[(fun z =>
                  ENNReal.ofReal (‖X z‖ ^ p)) | m] ω) := by
    filter_upwards [hfin, hreal, hbridge, hcond_nonneg, hτpos] with
      ω hfinω hrealω hbridgeω hcondω hτω
    let V : ℝ≥0∞ := condVarENN (m := m) μ Y ω
    have hαterm :
        0 ≤ α * ‖μ[Y | m] ω - μ[X | m] ω‖ :=
      mul_nonneg hα (norm_nonneg _)
    have hβτ : 0 ≤ β / τ ω := div_nonneg hβ hτω.le
    have hβV : 0 ≤ (β / τ ω) * V.toReal :=
      mul_nonneg hβτ ENNReal.toReal_nonneg
    have hV : ENNReal.ofReal V.toReal = V :=
      ENNReal.ofReal_toReal hfinω
    calc
      ENNReal.ofReal
            (α * ‖μ[Y | m] ω - μ[X | m] ω‖)
          + ENNReal.ofReal (β / τ ω) * V
          = ENNReal.ofReal
              (α * ‖μ[Y | m] ω - μ[X | m] ω‖
                + (β / τ ω) * V.toReal) := by
              rw [ENNReal.ofReal_add hαterm hβV,
                ENNReal.ofReal_mul hβτ, hV]
      _ ≤ ENNReal.ofReal
              ((K_p α β p * (τ ω) ^ (1 - p))
                * μ[(fun z => ‖X z‖ ^ p) | m] ω) :=
            ENNReal.ofReal_le_ofReal hrealω
      _ = ENNReal.ofReal
              (K_p α β p * (τ ω) ^ (1 - p))
            * μ⁻[(fun z =>
                ENNReal.ofReal (‖X z‖ ^ p)) | m] ω := by
              rw [ENNReal.ofReal_mul' hcondω, hbridgeω]
  exact ⟨henn, hfin, hreal⟩
