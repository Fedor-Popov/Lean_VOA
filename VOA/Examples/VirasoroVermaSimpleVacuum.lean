/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaQuotientDimensions
import VOA.Examples.VirasoroVermaVacuumForm
import VOA.Examples.VirasoroQuotientForm

/-!
# The simple highest-weight-zero Verma quotient is the simple vacuum module

The actual projection M(c,0) -> V(c,0) -> L(c,0) has kernel exactly the
Verma contravariant radical. The quotient equivalence therefore identifies
the actual irreducible Verma construction with the package's simple Virasoro
VOA, preserving all modes and normalized pairings. No Kac input is used.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule VirSimple VertexOperatorAlgebra

/-- Project an actual weight-zero Verma state through the universal vacuum
module to the existing simple Virasoro VOA. -/
noncomputable def simpleVacuumProjection (c : ℂ) :
    Verma c 0 →ₗ[ℂ] (VirUniv c ⧸ maxIdealVir c) :=
  (maxIdealVir c).mkQ.comp (vacuumProjection c)

/-- Every simple vacuum state has an actual Verma representative. -/
theorem simpleVacuumProjection_surjective (c : ℂ) :
    Function.Surjective (simpleVacuumProjection c) :=
  (maxIdealVir c).mkQ_surjective.comp (vacuumProjection_surjective c)

/-- The Verma form is the normalized simple vacuum form pulled back along
the actual composed projection. Both quotient comparisons are proved. -/
theorem vermaContravariant_simpleVacuum (c : ℂ) (u v : Verma c 0) :
    vermaContravariant c 0 u v=
      (VirQuotForm.Bsimp c).form (simpleVacuumProjection c u) (simpleVacuumProjection c v) := by
  rw [vermaContravariant_vacuum]
  exact (VirQuotForm.canB_quot_mkQ c _ _).symm

/-- The composed projection kills exactly the Verma radical. Nondegeneracy
of the existing simple vacuum form proves the converse, using surjectivity
to test every vector in the simple quotient. -/
theorem simpleVacuumProjection_ker (c : ℂ) :
    LinearMap.ker (simpleVacuumProjection c)=vermaRadical c 0 := by
  ext v
  constructor
  · intro hv
    apply LinearMap.ext
    intro w
    rw [vermaContravariant_simpleVacuum,LinearMap.mem_ker.mp hv]
    simp
  · intro hv
    have hh : simpleVacuumProjection c v ∈ InvariantForm.leftRadical (VirQuotForm.Bsimp c) := by
      rw [InvariantForm.mem_leftRadical]
      apply LinearMap.ext
      intro x
      obtain ⟨w,rfl⟩ := simpleVacuumProjection_surjective c x
      rw [← vermaContravariant_simpleVacuum]
      exact LinearMap.congr_fun hv w
    rw [VirQuotForm.Bsimp_leftRadical] at hh
    exact hh

/-- The actual simple weight-zero Verma quotient and simple Virasoro VOA
are canonically linearly equivalent, through the proved kernel equality. -/
noncomputable def vermaSimpleVacuumEquiv (c : ℂ) :
    VermaSimple c 0 ≃ₗ[ℂ] (VirUniv c ⧸ maxIdealVir c) :=
  (Submodule.quotEquivOfEq _ _ (simpleVacuumProjection_ker c).symm).trans
    ((simpleVacuumProjection c).quotKerEquivOfSurjective (simpleVacuumProjection_surjective c))

/-- On each actual representative the quotient equivalence is precisely
the composed projection, with no arbitrary scalar normalization. -/
theorem vermaSimpleVacuumEquiv_mkQ (c : ℂ) (v : Verma c 0) :
    vermaSimpleVacuumEquiv c ((vermaRadical c 0).mkQ v)=simpleVacuumProjection c v := rfl

/-- The actual simple vacuum projection intertwines every Virasoro mode. -/
theorem simpleVacuumProjection_mode (c : ℂ) (m : ℤ) (v : Verma c 0) :
    simpleVacuumProjection c (vermaMode c 0 m v)=
      (virasoroSimple c).L m (simpleVacuumProjection c v) := by
  change (maxIdealVir c).mkQ (vacuumProjection c (vermaMode c 0 m v))=_
  rw [vacuumProjection_mode]
  simpa only [virasoroVOA_L_eq_Lop] using VirQuotForm.mkQ_L c m (vacuumProjection c v)

/-- The equivalence is one of actual mode representations, not only of
vector spaces. Thus the simple highest-weight-zero representation is the
same object used by the existing VOA deformation and rigidity theorems. -/
theorem vermaSimpleVacuumEquiv_mode (c : ℂ) (m : ℤ) (v : VermaSimple c 0) :
    vermaSimpleVacuumEquiv c (vermaSimpleMode c 0 m v)=
      (virasoroSimple c).L m (vermaSimpleVacuumEquiv c v) := by
  obtain ⟨w,rfl⟩ := (vermaRadical c 0).mkQ_surjective v
  rw [vermaSimpleMode_mkQ,vermaSimpleVacuumEquiv_mkQ,vermaSimpleVacuumEquiv_mkQ,
    simpleVacuumProjection_mode]

end VOA.InverseDS.VirasoroVerma
