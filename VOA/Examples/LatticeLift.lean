/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeFields

/-!
# The `rTensor`-lift `B → LatModule` and the boson-current self-locality

For the lattice `A₁` VOA on `LatModule = B ⊗ ℂ{ℤ}` (`B = FockN 1`, the level-2 boson) the
reconstruction needs every two *generating* fields to be mutually local — including the boson
current with itself.  This file supplies the missing 6th generator-pair locality
`Local alphaLat alphaLat`, together with the reusable lift machinery `liftF`/`liftF₂` that carries
boson fields `FormalDist (End B)` to lattice fields `FormalDist (End LatModule)` (acting on the
`B` tensor factor).  The lift commutes with `bracketDist`/`mulBySubPow` and with the
lattice-momentum operator `zGradeOp`, so `Local alphaLat alphaLat` lifts cleanly from the
Heisenberg `currentN_self_local` (bound `2`).  All `pbw`-free / axiom-clean.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-! ## The `rTensor`-lift of fields from the boson factor `B` to `LatModule = B ⊗ ℂ{ℤ}` -/

/-- Lift a one-variable boson field to `LatModule` (act on the `B` tensor factor). -/
noncomputable def liftF (f : FormalDist (End ℂ B)) : FormalDist (End ℂ LatModule) :=
  fun j => LinearMap.rTensor LatGrp (f j)

/-- Lift a two-variable boson distribution to `LatModule`. -/
noncomputable def liftF₂ (F : FormalDist₂ (End ℂ B)) : FormalDist₂ (End ℂ LatModule) :=
  fun m n => LinearMap.rTensor LatGrp (F m n)

theorem liftF₂_zero : liftF₂ (0 : FormalDist₂ (End ℂ B)) = 0 := by
  funext m n
  change LinearMap.rTensor LatGrp (0 : End ℂ B) = 0
  rw [LinearMap.rTensor_zero]

/-- `rTensor` is multiplicative on `End` (it is `· ⊗ id`, an algebra map). -/
theorem rTensor_mul (f g : End ℂ B) :
    LinearMap.rTensor LatGrp (f * g)
      = LinearMap.rTensor LatGrp f * LinearMap.rTensor LatGrp g := by
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.rTensor_comp]

/-- The bracket distribution of two lifts is the lift of the bracket distribution. -/
theorem bracketDist_liftF (f g : FormalDist (End ℂ B)) :
    bracketDist (liftF f) (liftF g) = liftF₂ (bracketDist f g) := by
  funext m n
  rw [bracketDist_apply]
  change LinearMap.rTensor LatGrp (f m) * LinearMap.rTensor LatGrp (g n)
      - LinearMap.rTensor LatGrp (g n) * LinearMap.rTensor LatGrp (f m)
    = LinearMap.rTensor LatGrp ((bracketDist f g) m n)
  rw [bracketDist_apply, ← rTensor_mul, ← rTensor_mul]
  rw [← LinearMap.rTensor_sub]

/-- `mulBySub` commutes with the two-variable lift. -/
theorem mulBySub_liftF₂ (F : FormalDist₂ (End ℂ B)) :
    mulBySub (liftF₂ F) = liftF₂ (mulBySub F) := by
  funext m n
  rw [mulBySub_apply]
  change LinearMap.rTensor LatGrp (F (m - 1) n) - LinearMap.rTensor LatGrp (F m (n - 1))
      = LinearMap.rTensor LatGrp ((mulBySub F) m n)
  rw [mulBySub_apply]
  rw [← LinearMap.rTensor_sub]

/-- `mulBySubPow N` commutes with the two-variable lift. -/
theorem mulBySubPow_liftF₂ (N : ℕ) (F : FormalDist₂ (End ℂ B)) :
    mulBySubPow N (liftF₂ F) = liftF₂ (mulBySubPow N F) := by
  induction N generalizing F with
  | zero => rw [mulBySubPow_zero, mulBySubPow_zero]; rfl
  | succ n ih =>
      have h1 : mulBySubPow (n + 1) (liftF₂ F) = mulBySub (mulBySubPow n (liftF₂ F)) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      have h2 : mulBySubPow (n + 1) F = mulBySub (mulBySubPow n F) := by
        rw [mulBySubPow_succ, LinearMap.comp_apply]
      rw [h1, ih, mulBySub_liftF₂, h2]

/-- **Locality lifts**: if two boson fields are mutually local on `B`, their lifts are mutually
local on `LatModule` (same bound). -/
theorem Local_liftF {f g : FormalDist (End ℂ B)} (h : Local f g) :
    Local (liftF f) (liftF g) := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, by rw [bracketDist_liftF, mulBySubPow_liftF₂, hN, liftF₂_zero]⟩

/-! ## `zGradeOp` commutes with the lifted boson currents, and `Local alphaLat alphaLat` -/

/-- The lattice-momentum operator `zGradeOp = lTensor B zGradeL` commutes with every lifted boson
endomorphism `rTensor LatGrp f` (they act on different tensor factors). -/
theorem zGradeOp_comm_rTensor (f : End ℂ B) :
    zGradeOp * (LinearMap.rTensor LatGrp f) = (LinearMap.rTensor LatGrp f) * zGradeOp := by
  simp only [zGradeOp, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

/-- The `alphaLat`-bracket equals the lifted boson `alphaField`-bracket: the `α₀ = zGradeOp`
zero-mode correction commutes with the lifted currents, so it drops out of the commutator. -/
theorem bracketDist_alphaLat :
    bracketDist alphaLat alphaLat = bracketDist (liftF alphaField) (liftF alphaField) := by
  have key : ∀ (Am An cm cn : End ℂ LatModule),
      cn * Am = Am * cn → cm * An = An * cm → cm * cn = cn * cm →
      (Am + cm) * (An + cn) - (An + cn) * (Am + cm) = Am * An - An * Am := by
    intro Am An cm cn h1 h2 h3
    simp only [mul_add, add_mul]
    rw [h1, h2, h3]
    abel
  funext m n
  rw [bracketDist_apply, bracketDist_apply]
  change (LinearMap.rTensor LatGrp (alphaField m) + (if m = -1 then zGradeOp else 0))
        * (LinearMap.rTensor LatGrp (alphaField n) + (if n = -1 then zGradeOp else 0))
      - (LinearMap.rTensor LatGrp (alphaField n) + (if n = -1 then zGradeOp else 0))
        * (LinearMap.rTensor LatGrp (alphaField m) + (if m = -1 then zGradeOp else 0))
    = LinearMap.rTensor LatGrp (alphaField m) * LinearMap.rTensor LatGrp (alphaField n)
      - LinearMap.rTensor LatGrp (alphaField n) * LinearMap.rTensor LatGrp (alphaField m)
  refine key _ _ _ _ ?_ ?_ ?_
  · by_cases hn : n = -1
    · rw [if_pos hn, zGradeOp_comm_rTensor]
    · rw [if_neg hn, zero_mul, mul_zero]
  · by_cases hm : m = -1
    · rw [if_pos hm, zGradeOp_comm_rTensor]
    · rw [if_neg hm, zero_mul, mul_zero]
  · by_cases hm : m = -1 <;> by_cases hn : n = -1
    · rw [if_pos hm, if_pos hn]
    · rw [if_pos hm, if_neg hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_pos hn, mul_zero, zero_mul]
    · rw [if_neg hm, if_neg hn, mul_zero]

/-- **The boson-current self-locality on `LatModule`** (`Local alphaLat alphaLat`, bound `2`): the
missing 6th generator-pair `VA4` datum, lifted from the Heisenberg `currentN_self_local`. -/
theorem latticeA1_alpha_local : Local alphaLat alphaLat := by
  refine ⟨2, ?_⟩
  rw [bracketDist_alphaLat, bracketDist_liftF, mulBySubPow_liftF₂]
  rw [show mulBySubPow 2 (bracketDist alphaField alphaField) = 0 from
      HeisenbergN.currentN_self_local 1 2 0 0, liftF₂_zero]

end VOA.LatExp
