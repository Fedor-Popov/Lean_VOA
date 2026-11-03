/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeLift

/-!
# The lattice Sugawara translation operator `T = L₋₁`

The reconstruction needs a translation operator `T` with `T |0⟩ = 0` (and the generators
`T`-covariant).  We take the level-2 boson Sugawara `T(z) = (1/4):α(z)α(z):` built from the
*lattice* current `alphaLat` — whose zero mode `alphaLat(-1) = zGradeOp` is the lattice momentum,
so the Sugawara `:αα:` automatically carries the momentum coupling.  This file proves
`IsField alphaLat` (so `:αα:` is defined), defines `sugField`/`Ltrans = mode (sugField) 0`, and
proves `Ltrans latVacuum = 0` (the normal-ordered constant term kills the vacuum).  All
`pbw`-free / axiom-clean.
-/

open VOA VOA.LatExp VOA.LatticeVOA
open Module (End)
open scoped TensorProduct BigOperators

namespace VOA.LatExp

/-- The `rTensor`-lift of a boson field is a field (lower-truncation lifts through the tensor). -/
theorem IsField_liftF {f : FormalDist (End ℂ B)} (hf : IsField f) : IsField (liftF f) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => (liftF f n).map_zero⟩
  | tmul p g =>
      obtain ⟨Bp, hBp⟩ := hf p
      refine ⟨Bp, fun n hn => ?_⟩
      change LinearMap.rTensor LatGrp (f n) (p ⊗ₜ[ℂ] g) = 0
      rw [LinearMap.rTensor_tmul, hBp n hn, TensorProduct.zero_tmul]
  | add x y hx hy =>
      obtain ⟨Bx, hBx⟩ := hx
      obtain ⟨By, hBy⟩ := hy
      refine ⟨min Bx By, fun n hn => ?_⟩
      rw [map_add (liftF f n) x y, hBx n (lt_of_lt_of_le hn (min_le_left _ _)),
        hBy n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]

/-- **The lattice boson current is a field** (`IsField alphaLat`): the lifted `alphaField` is a
field, and the `α₀ = zGradeOp` correction sits only at index `-1`. -/
theorem alphaLat_isField : IsField alphaLat := by
  intro x
  obtain ⟨B, hB⟩ := IsField_liftF (f := alphaField) (HeisenbergN.currentN_isField 1 2 0) x
  refine ⟨min B (-1), fun n hn => ?_⟩
  change LinearMap.rTensor LatGrp (alphaField n) x + (if n = -1 then zGradeOp else 0) x = 0
  rw [if_neg (by omega : ¬ n = -1), LinearMap.zero_apply, add_zero]
  exact hB n (lt_of_lt_of_le hn (min_le_left _ _))

/-! ## The lattice Sugawara field, translation operator, and `T |0⟩ = 0` -/

/-- The lattice Sugawara field `T(z) = (1/4) :α(z)α(z):` (level-2 boson, `c = 1`). -/
noncomputable def sugField : FormalDist (End ℂ LatModule) :=
  (1 / 4 : ℂ) • nprod alphaLat_isField alphaLat_isField

theorem sugField_isField : IsField sugField := by
  intro x
  obtain ⟨B, hB⟩ := IsField.nprod alphaLat_isField alphaLat_isField x
  refine ⟨B, fun n hn => ?_⟩
  change (1 / 4 : ℂ) • (nprod alphaLat_isField alphaLat_isField n) x = 0
  rw [hB n hn, smul_zero]

/-- The lattice translation operator `T = L₋₁ = mode (sugField) 0` (the constant term of `T(z)`). -/
noncomputable def Ltrans : End ℂ LatModule := mode sugField 0

theorem Ltrans_eq : Ltrans = sugField (-1) := by
  rw [Ltrans, mode_apply]; norm_num

/-- `alphaLat` annihilates the vacuum below degree `0`: `alphaLat q |0⟩ = 0` for `q < 0`. -/
theorem alphaLat_vacuum_neg {q : ℤ} (hq : q < 0) : alphaLat q latVacuum = 0 := by
  have hb : LinearMap.rTensor LatGrp (alphaField q) latVacuum = 0 := by
    change LinearMap.rTensor LatGrp (alphaField q) ((1 : HeisenbergN.FockN 1) ⊗ₜ[ℂ] eVec 0) = 0
    rw [LinearMap.rTensor_tmul, alphaField_apply,
      show α (-q - 1) (1 : HeisenbergN.FockN 1) = (0 : HeisenbergN.FockN 1) from
        α_vacuum_nonneg (by omega : (0 : ℤ) ≤ -q - 1),
      TensorProduct.zero_tmul]
  change LinearMap.rTensor LatGrp (alphaField q) latVacuum
      + (if q = -1 then zGradeOp else 0) latVacuum = 0
  rw [hb, zero_add]
  by_cases hq1 : q = -1
  · rw [if_pos hq1, zGradeOp_vacuum]
  · rw [if_neg hq1]; rfl

/-- **`T |0⟩ = 0`** (`Ltrans latVacuum = 0`): the normal-ordered Sugawara constant term kills the
vacuum (degree `-1 < 0`). -/
theorem Ltrans_vacuum : Ltrans latVacuum = 0 := by
  rw [Ltrans_eq, sugField]
  change (1 / 4 : ℂ) • (nprod alphaLat_isField alphaLat_isField (-1)) latVacuum = 0
  rw [nprod_vacuum_neg_gen alphaLat_isField alphaLat_isField latVacuum
    (fun q hq => alphaLat_vacuum_neg hq) (fun q hq => alphaLat_vacuum_neg hq) (by norm_num),
    smul_zero]

end VOA.LatExp
