/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoAction
import VOA.DeligneAudit.D4FusionRealizationTwoFlatCoordinates

/-! Tensor coordinate actions on genuine standard basis vectors. -/
namespace VOA.DeligneAudit.D4Two

noncomputable section
variable {n : ℕ}

theorem leftAction_single (A : Module.End ℂ (SiteVector n)) (i j i' j' : SiteIndex n) :
    leftAction A (Pi.single (i, j) 1) (i', j') =
      if j' = j then A (Pi.single i 1) i' else 0 := by
  change A (fun a => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (a, j')) i' = _
  by_cases hj : j' = j
  · have hs : (fun a => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (a, j')) = Pi.single i 1 := by
      funext a
      simp [Pi.single_apply, Prod.mk.injEq, hj]
    rw [hs, if_pos hj]
  · have hs : (fun a => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (a, j')) = 0 := by
      funext a
      simp [Pi.single_apply, Prod.mk.injEq, Ne.symm hj]
    rw [hs, map_zero, if_neg hj]
    rfl

theorem rightAction_single (A : Module.End ℂ (SiteVector n)) (i j i' j' : SiteIndex n) :
    rightAction A (Pi.single (i, j) 1) (i', j') =
      if i' = i then A (Pi.single j 1) j' else 0 := by
  change A (fun b => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (i', b)) j' = _
  by_cases hi : i' = i
  · have hs : (fun b => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (i', b)) = Pi.single j 1 := by
      funext b
      simp [Pi.single_apply, Prod.mk.injEq, hi]
    rw [hs, if_pos hi]
  · have hs : (fun b => (Pi.single (i, j) (1 : ℂ) : PairIndex n → ℂ) (i', b)) = 0 := by
      funext b
      simp [Pi.single_apply, Prod.mk.injEq, Ne.symm hi]
    rw [hs, map_zero, if_neg hi]
    rfl

theorem flatCoordinates_symm_single (n : ℕ) (p : PairIndex n) :
    coordinates n ((flatCoordinates n).symm (Pi.single (pairFlat n p) 1)) =
      Pi.single p 1 := by
  funext q
  have h := flatCoordinates_at_pair n
    ((flatCoordinates n).symm (Pi.single (pairFlat n p) 1)) q
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [Pi.single_apply, Equiv.apply_eq_iff_eq] using h.symm

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.flatCoordinates_symm_single
