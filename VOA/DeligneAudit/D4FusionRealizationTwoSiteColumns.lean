/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoAction
import VOA.DeligneAudit.D4FusionRealizationTwoFlatCoordinates
import VOA.DeligneAudit.D4FusionRealizationTwoMatrixBridge

/-! The light integer columns act on the actual coadjoint-plus-line site.
Only the already checked bracket and coordinate facts are used. -/
namespace VOA.DeligneAudit.D4Two

open Certificate

noncomputable section

theorem siteAction_zero_single (c : Fin 28) (j : SiteIndex 28) :
    siteAction (D1SiteG.zeroOp (DeligneSector.Sparse.fC 28 DeligneSector.D4.br) c)
      (Pi.single j 1) =
    fun i => (coeff (rawColumn c (siteFlat 28 j)) (siteFlat 28 i) : ℂ) := by
  funext i
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          rw [siteAction_zero_inl]
          change _ = (coeff (rawColumn c j) i : ℂ)
          rw [rawColumn_complex]
          simp [Pi.single_apply]
      | inr j =>
          cases j
          rw [siteAction_zero_inl]
          change _ = (coeff (rawColumn c 28) i : ℂ)
          have hz := rawColumn_coeff c i 28 c.isLt (by omega) (by omega)
          simp only [Nat.lt_irrefl, and_false, if_false] at hz
          rw [hz, Int.cast_zero]
          simp
  | inr i =>
      cases i
      rw [siteAction_zero_inr]
      change 0 = (coeff (rawColumn c (siteFlat 28 j)) 28 : ℂ)
      have hz := rawColumn_coeff c 28 (siteFlat 28 j) c.isLt
        (by omega) (siteFlat 28 j).isLt
      simp only [Nat.lt_irrefl, false_and, if_false] at hz
      rw [hz, Int.cast_zero]

theorem siteAction_one_single (c : Fin 28) (j i : SiteIndex 28) :
    siteAction (D1SiteG.oneOp c) (Pi.single j 1) i =
      if i = Sum.inr () ∧ j = Sum.inl c then 1 else 0 := by
  cases i with
  | inl i => simp
  | inr i => cases i; simp [Pi.single_apply, eq_comm]

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.siteAction_zero_single
