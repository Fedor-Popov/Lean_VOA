import VOA.DeligneAudit.DeligneFusionCVRectFamily
import VOA.DeligneAudit.DeligneFusionCVRectList

/-! # Permutation transport of the actual canonical rectangular family -/

namespace VOA.DeligneAudit.A2.CVRectFamilyPerm

open VOA.DeligneAudit.A2.CVRectFamily
open VOA.DeligneAudit.A2.CVRectZero
open VOA.DeligneAudit.A2.CVRectList

variable {two two' one one' : List ℕ}

theorem familyOrder_perm (ht : two.Perm two') (ho : one.Perm one') :
    familyOrder two one = familyOrder two' one' := by
  funext a b
  exact congrArg₂ (· + ·) (excess_perm ht _) (excess_perm ho _)

/-- Reordering capacities changes neither the actual coefficient ideal
nor the finite-variable lengths. -/
theorem finiteDimensional_perm (ht : two.Perm two') (ho : one.Perm one')
    [FiniteDimensional ℂ (Family two one)] : FiniteDimensional ℂ (Family two' one') := by
  have hf := (inferInstance : FiniteDimensional ℂ (Family two one))
  unfold Family Model ideal at hf ⊢
  rw [ht.length_eq.symm, ho.length_eq.symm, familyOrder_perm ht.symm ho.symm]
  exact hf

theorem finrank_perm (ht : two.Perm two') (ho : one.Perm one') :
    Module.finrank ℂ (Family two one) = Module.finrank ℂ (Family two' one') := by
  unfold Family Model ideal
  rw [ht.length_eq, ho.length_eq, familyOrder_perm ht ho]

end VOA.DeligneAudit.A2.CVRectFamilyPerm

#print axioms VOA.DeligneAudit.A2.CVRectFamilyPerm.finiteDimensional_perm
#print axioms VOA.DeligneAudit.A2.CVRectFamilyPerm.finrank_perm
