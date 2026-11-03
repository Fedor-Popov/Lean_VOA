/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralJacobi
import VOA.Moonshine.LatticeTwistedGrading

/-! # Charge-parametric grading for even lattices
Adapted from `LatticeTwistedGrading` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice.{0}) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)

theorem YTLFld_zero_eq (e : ℤ) :
    YTLFld L hEven C 0 e
      = rTFld (Tm := Space L hEven C) (FT (rank L) e (vacuumN _)) := by
  apply fld_ext_mode
  intro n x
  rw [mode_YTLFld, mode_rTFld, FT_val, mode_resc, YTL_zero, YT_vacuum]
  push_cast
  split_ifs <;> simp [Module.End.one_eq_id, LinearMap.rTensor_id]

include hPos in
theorem FL_charge_zero (p : FockN (rank L)) (e : ℤ) :
    FL L hEven C e (p ⊗ₜ[ℂ] eGen L 0)
      = rTFld (Tm := Space L hEven C) (FT (rank L) e p) := by
  induction p using MvPolynomial.induction_on generalizing e with
  | C a =>
      rw [MvPolynomial.C_eq_smul_one, ← TensorProduct.smul_tmul', map_smul, FT_smul, rTFld_smul,
        ← echg_eq, FL_echg L hEven C hPos, YTLFld_zero_eq]
      rfl
  | add p q hp hq => rw [TensorProduct.add_tmul, map_add, hp, hq, FT_add, rTFld_add]
  | mul_X p c hp =>
      have h1 := FL_mul_X L hEven C hPos (e - 1) c p (eGen L 0)
      have h2 := FT_mul_X (rank L) (e - 1) c p
      rw [sub_add_cancel] at h1 h2
      have hloc : Local (FgenFld (rank L) c.2).1 (FT (rank L) (e - 1) p).1 := by
        rw [← FT_one_X]
        exact FT_local (rank L) 1 (e - 1) _ p
      rw [mul_comm, h1, h2, hp, FgT, rTFld_star _ hloc]

include hPos in
theorem YML_omega_two :
    YML L hEven C (omegaLatGen L) 2
      = (L0T (rank L)).rTensor (Space L hEven C) := by
  rw [YML_apply, omegaLatGen, mkEα_apply, FL_charge_zero L hEven C hPos, mode_rTFld, FT_val,
    mode_resc]
  rw [show ((2 : ℕ) : ℤ) * 0 + 2 = 2 by norm_num]
  exact congrArg (fun f => LinearMap.rTensor _ f) (YT_omega_two (rank L))

end Lattice

end VOA.Moonshine.LatticeTwistedGeneral
