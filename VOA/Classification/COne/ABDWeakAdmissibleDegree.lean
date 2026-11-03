import VOA.Classification.COne.ABDWeakAdmissibleCyclic

/-!
# The degree-preserving normal-form residual

The existing Buhl filtration records sums of generator weights, not mode degree.
`WeakDegreeNormalForm` records the true stronger spanning assertion needed to
apply the finite normal-word count to arbitrary powers of `L(0)`.

The implication from this residual to weak conformal local finiteness is proved
here. The residual itself is not proved. This distinction prevents using an
admissible-level projection before constructing the admissible grading.
-/

namespace VOA.Classification.COne.ABDWeakAdmissible

open VOA.Huang.BuhlSpanning VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A homogeneous VOA state together with its weight and mode. -/
structure HomogeneousLetter (W : VertexOperatorAlgebra 𝒱) where
  state : 𝒱
  weight : ℤ
  modeIndex : ℤ
  homogeneous : state ∈ W.grading weight

/-- Action of an arbitrary homogeneous mode word, head outermost. -/
noncomputable def homogeneousWord (A : WeakModule W M) :
    List (HomogeneousLetter W) → Module.End ℂ M
  | [] => LinearMap.id
  | a :: l => mode (A.YM a.state) a.modeIndex ∘ₗ homogeneousWord A l

/-- Total mode degree, independent of Buhl's weight filtration. -/
def homogeneousDegree : List (HomogeneousLetter W) → ℤ
  | [] => 0
  | a :: l => a.weight - a.modeIndex - 1 + homogeneousDegree l

/-- Span of all homogeneous words of a specified total mode degree on a seed. -/
noncomputable def homogeneousDegreeSpan (A : WeakModule W M) (x : M) (d : ℤ) :
    Submodule ℂ M :=
  Submodule.span ℂ ((fun l => homogeneousWord A l x) ''
    {l : List (HomogeneousLetter W) | homogeneousDegree l = d})

/-- The empty word puts the seed in degree zero. -/
theorem seed_mem_homogeneousDegreeSpan (A : WeakModule W M) (x : M) :
    x ∈ homogeneousDegreeSpan A x 0 :=
  Submodule.subset_span ⟨[], rfl, rfl⟩

/-- Conformal action preserves each homogeneous-word degree span, on any weak module. -/
theorem L0_mem_homogeneousDegreeSpan (A : WeakModule W M) (x : M) (d : ℤ)
    {y : M} (hy : y ∈ homogeneousDegreeSpan A x d) :
    L0 A y ∈ homogeneousDegreeSpan A x d := by
  let ω : HomogeneousLetter W := ⟨W.conformalVector, 2, 1, W.conformal_mem⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨ω :: l, ?_, rfl⟩
    change 2 - 1 - 1 + homogeneousDegree l = d
    simpa using hl
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-- True Buhl refinement: normalize arbitrary homogeneous words without changing
mode degree. This is a named residual, not a theorem proved in this file. -/
def WeakDegreeNormalForm (W : VertexOperatorAlgebra 𝒱) : Prop :=
  C2Cofinite W → ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M)
    (x : M), ∃ (D : GenData W) (Q Bm : ℕ), ∀ d : ℤ,
      homogeneousDegreeSpan A x d ≤ normalDegreeSpan D A x Q Bm d

/-- Degree-preserving normalization makes every homogeneous-word degree span finite. -/
theorem finiteDimensional_homogeneousDegreeSpan_of_normalForm
    (hnorm : WeakDegreeNormalForm W) (hC2 : C2Cofinite W)
    (A : WeakModule W M) (x : M) (d : ℤ) :
    FiniteDimensional ℂ (homogeneousDegreeSpan A x d) := by
  obtain ⟨D, Q, Bm, hle⟩ := hnorm hC2 A x
  letI := finiteDimensional_normalDegreeSpan D A x Q Bm d
  exact FiniteDimensional.of_injective (Submodule.inclusion (hle d))
    (Submodule.inclusion_injective (hle d))

/-- The exact missing normal-form refinement implies local finiteness for all weak modules. -/
theorem weakL0LocallyFinite_of_degreeNormalForm (hnorm : WeakDegreeNormalForm W) :
    WeakL0LocallyFinite W := by
  intro hC2 M _ _ A x
  exact ⟨homogeneousDegreeSpan A x 0,
    finiteDimensional_homogeneousDegreeSpan_of_normalForm hnorm hC2 A x 0,
    seed_mem_homogeneousDegreeSpan A x, fun _ hy => L0_mem_homogeneousDegreeSpan A x 0 hy⟩

/-- ABD with two explicit true residuals: degree-preserving normalization and
uniform lower bounds for the weak conformal spectrum. -/
theorem abdWeakIsAdmissible_of_degreeNormalForm_boundedBelow
    (hnorm : WeakDegreeNormalForm W) (hbound : WeakSpectrumBoundedBelow W) :
    ABDWeakIsAdmissible W :=
  abdWeakIsAdmissible_of_localFinite_boundedBelow
    (weakL0LocallyFinite_of_degreeNormalForm hnorm) hbound

/-- The associativity consumer with the Buhl and spectral residuals exposed. -/
theorem associativityInput_of_degreeNormalForm_boundedBelow
    (hV : StronglyRational W) (hnorm : WeakDegreeNormalForm W)
    (hbound : WeakSpectrumBoundedBelow W) (hFin : DLMFinitelyManyIrredAdmissible W) :
    VOA.Huang.AssocTarget.AssociativityInput W :=
  associativityInput_of_spectral_inputs hV
    (weakL0LocallyFinite_of_degreeNormalForm hnorm) hbound hFin

end VOA.Classification.COne.ABDWeakAdmissible
