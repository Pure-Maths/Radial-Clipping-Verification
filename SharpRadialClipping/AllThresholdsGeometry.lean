import SharpRadialClipping.AllThresholds
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-radius geometric construction for simultaneous clipping

The first step is to place a triangle from an arbitrary real Hilbert space in
the fixed three-dimensional target while retaining all side lengths.
-/

open MeasureTheory

noncomputable section

/-- The two vectors defining the first residual-path triangle have a
distance-preserving placement in three-dimensional Euclidean space. -/
theorem exists_three_space_triangle
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H) :
    ∃ A' B' : EuclideanSpace ℝ (Fin 3),
      ‖A'‖ = ‖A‖ ∧ ‖B'‖ = ‖B‖ ∧ ‖A' - B'‖ = ‖A - B‖ := by
  classical
  let a : ℝ := if h : A = 0 then 0 else inner ℝ A B / ‖A‖
  let b : ℝ := Real.sqrt (‖B‖ ^ 2 - a ^ 2)
  let A' : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 ‖A‖
  let B' : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single 0 a + EuclideanSpace.single 1 b
  have haabs : |a| ≤ ‖B‖ := by
    by_cases hA : A = 0
    · simp [a, hA]
    · have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA
      simp only [a, dif_neg hA, abs_div, abs_of_nonneg (norm_nonneg A)]
      apply (div_le_iff₀ hAn).2
      simpa [mul_comm] using abs_real_inner_le_norm A B
  have hrad : 0 ≤ ‖B‖ ^ 2 - a ^ 2 := by
    nlinarith [abs_nonneg a, norm_nonneg B, sq_abs a]
  have hb : b ^ 2 = ‖B‖ ^ 2 - a ^ 2 := Real.sq_sqrt hrad
  have hAnorm : ‖A'‖ = ‖A‖ := by
    have hsq : ‖A'‖ ^ 2 = ‖A‖ ^ 2 := by
      simp [A']
    nlinarith [norm_nonneg A', norm_nonneg A]
  have hBnorm : ‖B'‖ = ‖B‖ := by
    have hsq : ‖B'‖ ^ 2 = a ^ 2 + b ^ 2 := by
      simp [B', EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    nlinarith [norm_nonneg B', norm_nonneg B]
  have hinner : inner ℝ A' B' = inner ℝ A B := by
    change inner ℝ (EuclideanSpace.single 0 ‖A‖)
      (EuclideanSpace.single 0 a + EuclideanSpace.single 1 b) = inner ℝ A B
    rw [EuclideanSpace.inner_single_left]
    by_cases hA : A = 0
    · simp [a, hA]
    · simpa [a, hA] using
        (mul_div_cancel₀ (inner ℝ A B) (norm_ne_zero_iff.mpr hA))
  refine ⟨A', B', hAnorm, hBnorm, ?_⟩
  have hsq : ‖A' - B'‖ ^ 2 = ‖A - B‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, hAnorm, hBnorm, hinner]
  nlinarith [norm_nonneg (A' - B'), norm_nonneg (A - B)]

/-- The initial placement is a linear isometry on the span of the two
specified vectors.  Thus every point of a two-radius residual path is
matched, not just its vertices. -/
theorem exists_three_space_two_vector_path
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : H) :
    ∃ A' B' : EuclideanSpace ℝ (Fin 3),
      ∀ s t : ℝ, ‖s • A' + t • B'‖ = ‖s • A + t • B‖ := by
  obtain ⟨A', B', hA, hB, hAB⟩ := exists_three_space_triangle A B
  have hinner : inner ℝ A' B' = inner ℝ A B := by
    have h := inner_eq_of_three_distances A B 0 A' B' 0
      (by simpa using hA.symm) (by simpa using hB.symm) hAB.symm
    simpa using h.symm
  refine ⟨A', B', ?_⟩
  intro s t
  have hsquares : ‖s • A' + t • B'‖ ^ 2 =
      ‖s • A + t • B‖ ^ 2 := by
    rw [norm_add_sq_real, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, real_inner_smul_left,
      real_inner_smul_right, mul_pow, sq_abs, hA, hB, hinner]
  nlinarith [norm_nonneg (s • A' + t • B'),
    norm_nonneg (s • A + t • B)]
