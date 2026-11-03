import VOA.Classification.COne.ABDWeakAdmissibleEigenCyclic
import VOA.Classification.COne.ABDWeakAdmissibleCyclicRestriction
import VOA.Classification.COne.ABDWeakAdmissibleZhuBottom

/-!
# ABD Proposition 5.7 from degree-preserving Buhl normalization and Zhu's algebra

For the spectral bound, a generalized eigenvalue supplies an actual eigenvector.
Its cyclic weak submodule is ordinary and supported in one integral coset.
Its least occupied weight carries the existing Zhu action, so it lies in the
finite Zhu conformal spectrum. This proves a bound uniform over all weak modules.
-/
namespace VOA.Classification.COne.ABDWeakAdmissible
open PlusRational VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱}

/-- All weak generalized conformal weights are natural-number shifts of one finite set. -/
theorem exists_finite_weak_conformal_spectrum (hC2 : C2Cofinite W) :
    ∃ s : Finset ℂ, ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule W M) (α : ℂ), (L0 A).maxGenEigenspace α ≠ ⊥ →
      ∃ μ ∈ s, ∃ n : ℕ, α = μ + n := by
  obtain ⟨s, hs⟩ := exists_finite_ordinary_coset_spectrum (W := W) hC2
  refine ⟨s, ?_⟩
  intro M _ _ A α hα
  obtain ⟨x, hx0, hx⟩ := exists_eigenvector_of_maxGenEigenspace_ne_bot A α hα
  let P := ofR A (cyclic A x)
  let B := WeakModule.submodule A P
  let z : P.carrier := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hz : L0 B z = α • z := Subtype.ext hx
  have hcyc : cyclic B z = ⊤ := cyclic_restriction_eq_top A x
  obtain ⟨O, hO, hzO, hcos⟩ := eigen_cyclic_isOrdinary hC2 B z α hz hcyc
  have hne : O.weight α ≠ ⊥ := by
    intro h
    rw [h] at hzO
    exact hx0 (congrArg Subtype.val (show z = 0 from hzO))
  exact hs O α hne hcos

/-- C₂-cofiniteness supplies a real bound uniform over all weak modules. -/
theorem exists_uniform_weak_spectrum_lower_bound (hC2 : C2Cofinite W) :
    ∃ b : ℝ, ∀ {M : Type u} [AddCommGroup M] [Module ℂ M]
      (A : WeakModule W M) (α : ℂ), (L0 A).maxGenEigenspace α ≠ ⊥ → b ≤ α.re := by
  obtain ⟨s, hs⟩ := exists_finite_weak_conformal_spectrum (W := W) hC2
  obtain ⟨b, hb⟩ := (s.finite_toSet.image Complex.re).bddBelow
  refine ⟨b, ?_⟩
  intro M _ _ A α hα
  obtain ⟨μ, hμ, n, rfl⟩ := hs A α hα
  have h := hb ⟨μ, hμ, rfl⟩
  simp only [Complex.add_re, Complex.natCast_re]
  exact h.trans (le_add_of_nonneg_right (Nat.cast_nonneg n))

/-- The global weak-spectrum residual, unconditionally. -/
theorem weakSpectrumBoundedBelow : WeakSpectrumBoundedBelow W := by
  intro hC2 M _ _ A
  obtain ⟨b, hb⟩ := exists_uniform_weak_spectrum_lower_bound (W := W) hC2
  exact ⟨b, hb A⟩

/-- ABD Proposition 5.7: every weak module of a C₂-cofinite VOA is admissible,
with exactly its original weak action. -/
theorem abdWeakIsAdmissible : ABDWeakIsAdmissible W :=
  abdWeakIsAdmissible_of_degreeNormalForm_boundedBelow
    weakDegreeNormalForm weakSpectrumBoundedBelow

/-- The associativity consumer needs no ABD residual hypothesis. -/
theorem associativityInput_of_c2_spectral_theorems
    (hV : StronglyRational W) (hFin : DLMFinitelyManyIrredAdmissible W) :
    VOA.Huang.AssocTarget.AssociativityInput W :=
  associativityInput_of_degreeNormalForm_boundedBelow hV
    weakDegreeNormalForm weakSpectrumBoundedBelow hFin

end VOA.Classification.COne.ABDWeakAdmissible
