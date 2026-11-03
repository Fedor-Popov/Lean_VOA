import VOA.Classification.COne.PlusSplittingLift
import VOA.Classification.COne.C2WindowDetectsReduction
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Generalized-weight decomposition of arbitrary invariant submodules

Local finiteness of an operator gives a generalized-eigenspace decomposition
of every invariant subspace, even in infinite dimension. Applied to `L(0)`
on a homogeneous cyclic admissible module, this concerns arbitrary mode
submodules. It makes no assertion about admissible-level gradedness.

This is one step towards the nonintegral-weight extension argument in Abe,
https://arxiv.org/html/math/0311210, Proposition 2.4. Grouping generalized
weights modulo integers, proving mode stability of those blocks, and locating
the simple factors' lowest weights remain necessary for that argument.
-/

namespace VOA.Classification.COne.PlusSplitting

set_option maxSynthPendingDepth 3

/-- Infinite-dimensional local finiteness suffices for generalized-weight
decomposition of every invariant subspace. -/
theorem eq_iSup_inf_maxGenEigenspace_of_locally_finite
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : Module.End ℂ X)
    (hloc : ∀ x : X, ∃ S : Submodule ℂ X,
      FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, f y ∈ S)
    (P : Submodule ℂ X) (hP : ∀ y ∈ P, f y ∈ P) :
    P = ⨆ μ : ℂ, P ⊓ f.maxGenEigenspace μ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨S, hfin, hxS, hS⟩ := hloc x
    letI := hfin
    let T := S ⊓ P
    have hT : ∀ y ∈ T, f y ∈ T := fun y hy => ⟨hS y hy.1, hP y hy.2⟩
    have hdecomp : T = ⨆ μ : ℂ, T ⊓ f.maxGenEigenspace μ := by
      have he := Module.End.iSup_maxGenEigenspace_eq_top (f.restrict hT)
      have he' := congrArg (Submodule.map T.subtype) he
      simpa only [Submodule.map_iSup, ← Submodule.inf_genEigenspace,
        Submodule.map_top, Submodule.range_subtype] using he'.symm
    have hle : T ≤ ⨆ μ : ℂ, P ⊓ f.maxGenEigenspace μ := by
      rw [hdecomp]
      exact iSup_mono fun μ => inf_le_inf inf_le_right le_rfl
    exact hle ⟨hxS, hx⟩
  · exact iSup_le fun μ => inf_le_left

/-- Local finiteness passes through a surjective intertwining map. In
particular it passes to quotients by arbitrary invariant subspaces. -/
theorem locally_finite_of_surjective_intertwiner
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (f : Module.End ℂ X) (g : Module.End ℂ Y) (π : X →ₗ[ℂ] Y)
    (hπ : Function.Surjective π) (hcomm : ∀ x, π (f x) = g (π x))
    (hloc : ∀ x : X, ∃ S : Submodule ℂ X,
      FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, f y ∈ S) :
    ∀ y : Y, ∃ T : Submodule ℂ Y,
      FiniteDimensional ℂ T ∧ y ∈ T ∧ ∀ z ∈ T, g z ∈ T := by
  intro y
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨S, hfin, hx, hS⟩ := hloc x
  letI := hfin
  refine ⟨S.map π, inferInstance, Submodule.mem_map_of_mem hx, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  rw [← hcomm]
  exact Submodule.mem_map_of_mem (hS w hw)

/-- Local finiteness also passes to invariant subspaces, via injective
intertwining maps. Together with the surjective version this handles
subquotients without imposing a grading on their defining subspaces. -/
theorem locally_finite_of_injective_intertwiner
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (f : Module.End ℂ X) (g : Module.End ℂ Y) (ι : X →ₗ[ℂ] Y)
    (hι : Function.Injective ι) (hcomm : ∀ x, ι (f x) = g (ι x))
    (hloc : ∀ y : Y, ∃ S : Submodule ℂ Y,
      FiniteDimensional ℂ S ∧ y ∈ S ∧ ∀ z ∈ S, g z ∈ S) :
    ∀ x : X, ∃ T : Submodule ℂ X,
      FiniteDimensional ℂ T ∧ x ∈ T ∧ ∀ z ∈ T, f z ∈ T := by
  intro x
  obtain ⟨S, hfin, hx, hS⟩ := hloc (ι x)
  letI := hfin
  haveI : FiniteDimensional ℂ ι.ker := by
    rw [LinearMap.ker_eq_bot.mpr hι]
    infer_instance
  refine ⟨S.comap ι, inferInstance, hx, ?_⟩
  intro z hz
  change ι (f z) ∈ S
  rw [hcomm]
  exact hS (ι z) hz

/-- Generalized-weight decomposition survives passage to a quotient. There
is no assumption that the quotient submodule is admissible-level graded. -/
theorem quotient_eq_iSup_inf_maxGenEigenspace
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : Module.End ℂ X)
    (hloc : ∀ x : X, ∃ S : Submodule ℂ X,
      FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ y ∈ S, f y ∈ S)
    (P : Submodule ℂ X) (hP : ∀ y ∈ P, f y ∈ P)
    (Q : Submodule ℂ (X ⧸ P))
    (hQ : ∀ y ∈ Q, P.mapQ P f hP y ∈ Q) :
    Q = ⨆ μ : ℂ, Q ⊓ Module.End.maxGenEigenspace (P.mapQ P f hP) μ := by
  apply eq_iSup_inf_maxGenEigenspace_of_locally_finite _ _ Q hQ
  exact locally_finite_of_surjective_intertwiner f (P.mapQ P f hP) P.mkQ
    P.mkQ_surjective (fun x => rfl) hloc

open PlusRational C2WindowDetects

universe u

/-- Arbitrary mode submodules of a homogeneous cyclic C₂-cofinite admissible
module decompose into generalized conformal weights, not admissible levels. -/
theorem cyclic_submodule_eq_iSup_inf_maxGenEigenspace
    {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) (hC2 : C2Cofinite W)
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : AdmissibleModule W M) (k : ℤ) (x : M) (hx : x ∈ N.lev k)
    (P : Submodule (modeAlg N.toWeakModule) (cyclic N.toWeakModule x)) :
    P.restrictScalars ℂ = ⨆ μ : ℂ,
      P.restrictScalars ℂ ⊓ (cyclicL0 N x).maxGenEigenspace μ := by
  apply eq_iSup_inf_maxGenEigenspace_of_locally_finite _
    (cyclicL0_locally_finite W hC2 N k x hx)
  intro y hy
  exact P.smul_mem
    (⟨mode (N.YM W.conformalVector) 1,
      Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩ : modeAlg N.toWeakModule) hy

end VOA.Classification.COne.PlusSplitting
