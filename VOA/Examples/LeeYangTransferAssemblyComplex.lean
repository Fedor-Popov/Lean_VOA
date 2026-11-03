import VOA.Examples.LeeYangTransferAssemblySimple
import VOA.Examples.GradedUnitaryCohomologyTransfer

/-!
# The actual finite relative complex used by the transfer

The carrier is the intersection of the concrete relative BRST carrier with a
conformal weight space. The differential and cycle inclusion are restrictions
of the existing concrete differential and inclusion. Relative boundaries map
to zero in absolute cohomology, which is enough for the coset injectivity proof.
-/
namespace VOA.LeeYangTransferAssembly
open Sl2CosetConcrete Sl2SemiInfinite LeeYangCosetTransfer
open scoped TensorProduct
set_option maxHeartbeats 800000
noncomputable section

abbrev BRSTSpace := MatterSpace ⊗[ℂ] Sl2GhostSpace

/-- The actual relative BRST complex at conformal weight `n`. -/
def relativeWeight (n : ℤ) : Submodule ℂ BRSTSpace :=
  relativeCarrier leeYangMatterAction.toAffineSl2Action ⊓ brstSVA.grading (n : ℂ)

instance relativeWeight_finite (n : ℤ) : FiniteDimensional ℂ (relativeWeight n) := by
  letI := brstSVA.finrank (n : ℂ)
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show relativeWeight n ≤ brstSVA.grading (n : ℂ) from inf_le_right))
    (fun x y h => Subtype.ext (congrArg (fun z : brstSVA.grading (n : ℂ) => (z : BRSTSpace)) h))

/-- Restriction of the already constructed BRST residue. -/
def relativeDifferential (n : ℤ) : relativeWeight n →ₗ[ℂ] relativeWeight n :=
  leeYangBRSTComplex.Q.restrict (fun x hx =>
    ⟨semiInfiniteQ_mem_relativeCarrier leeYangMatterAction matterParityCompatible
      matterGhostTensorGrading hx.1, leeYangBRSTComplex.Q_wt _ x hx.2⟩)

@[simp] theorem relativeDifferential_coe (n : ℤ) (x : relativeWeight n) :
    (relativeDifferential n x : BRSTSpace) = leeYangBRSTComplex.Q x := rfl

theorem relativeDifferential_sq (n : ℤ) :
    (relativeDifferential n).comp (relativeDifferential n) = 0 := by
  ext x
  exact leeYangBRSTComplex.Q_apply_Q x

/-- Inclusion of the finite relative cycles into the actual absolute cycles. -/
def weightCyclesToAbsolute (n : ℤ) :
    LinearMap.ker (relativeDifferential n) →ₗ[ℂ] leeYangBRSTComplex.kerQ :=
  ((relativeWeight n).subtype.comp (LinearMap.ker (relativeDifferential n)).subtype).codRestrict _
    (fun x => congrArg Subtype.val x.property)

/-- A finite relative boundary has zero absolute cohomology class. -/
theorem weightBoundary_toAbsolute (n : ℤ)
    (x : LinearMap.ker (relativeDifferential n))
    (hx : x ∈ boundariesInCycles (K := relativeWeight n) (relativeDifferential n)) :
    leeYangBRSTComplex.prj (weightCyclesToAbsolute n x) = 0 := by
  apply leeYangBRSTComplex.prj_eq_zero.mpr
  obtain ⟨y, hy⟩ := hx
  exact ⟨y.val, congrArg Subtype.val hy⟩

end
end VOA.LeeYangTransferAssembly
