import VOA.Classification.COne.PlusSplittingSpectrum

/-!
# Removing the homogeneous-generator restriction from conformal local finiteness

The locally finite vectors of an operator form a subspace. Since all admissible
levels lie in that subspace by the homogeneous cyclic C₂ result, the whole
admissible module does. Consequently arbitrary mode submodules, including
nonhomogeneous cyclic modules, admit generalized conformal-weight decompositions.
This does not prove that they are graded for the original admissible levels.
-/

namespace VOA.Classification.COne.PlusSplitting

set_option maxSynthPendingDepth 3

/-- The vectors contained in some finite-dimensional invariant subspace. -/
def locallyFiniteVectors {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : Module.End ℂ X) : Submodule ℂ X where
  carrier := {x | ∃ S : Submodule ℂ X,
    FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, f y ∈ S}
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, by
    intro y hy
    have : y = 0 := hy
    simp [this]⟩
  add_mem' := by
    rintro x y ⟨S, hSfin, hx, hS⟩ ⟨T, hTfin, hy, hT⟩
    letI := hSfin
    letI := hTfin
    refine ⟨S ⊔ T, inferInstance,
      Submodule.add_mem _ (Submodule.mem_sup_left hx) (Submodule.mem_sup_right hy), ?_⟩
    intro z hz
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hS s hs))
      (Submodule.mem_sup_right (hT t ht))
  smul_mem' := by
    rintro r x ⟨S, hfin, hx, hS⟩
    exact ⟨S, hfin, S.smul_mem r hx, hS⟩

open PlusRational C2WindowDetects

universe u

/-- Conformal local finiteness on the entire admissible module; the vector
need not be homogeneous and its cyclic module need not be level-graded. -/
theorem admissible_L0_locally_finite
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : AdmissibleModule W M) (x : M) :
    ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, mode (N.YM W.conformalVector) 1 y ∈ S := by
  let f := mode (N.YM W.conformalVector) 1
  have htop : (⊤ : Submodule ℂ M) ≤ locallyFiniteVectors f := by
    rw [← N.lev_iSup_eq_top]
    apply iSup_le
    intro k y hy
    let C := cyclic N.toWeakModule y
    let π : C →ₗ[ℂ] M := C.subtype.restrictScalars ℂ
    obtain ⟨S, hfin, hyS, hS⟩ := cyclicL0_locally_finite W hC2 N k y hy
      ⟨y, Submodule.mem_span_singleton_self y⟩
    letI := hfin
    refine ⟨S.map π, inferInstance, ⟨_, hyS, rfl⟩, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    exact ⟨cyclicL0 N y w, hS w hw, rfl⟩
  exact htop (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ M))

/-- Every arbitrary mode submodule of a C₂-cofinite admissible module is
graded for generalized conformal weights. There is no finite-dimensionality
assumption on the admissible module or on its levels. -/
theorem admissible_submodule_eq_iSup_inf_maxGenEigenspace
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : AdmissibleModule W M) (P : Submodule (modeAlg N.toWeakModule) M) :
    P.restrictScalars ℂ = ⨆ μ : ℂ,
      P.restrictScalars ℂ ⊓ (mode (N.YM W.conformalVector) 1).maxGenEigenspace μ := by
  apply eq_iSup_inf_maxGenEigenspace_of_locally_finite _ (admissible_L0_locally_finite W hC2 N)
  intro y hy
  exact P.smul_mem
    (⟨mode (N.YM W.conformalVector) 1,
      Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩ : modeAlg N.toWeakModule) hy

end VOA.Classification.COne.PlusSplitting
