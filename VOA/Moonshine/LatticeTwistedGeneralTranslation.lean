/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralProduct
import VOA.Moonshine.LatticeTwistedTranslation

/-! # Charge-parametric translation for even lattices
Adapted from `LatticeTwistedTranslation` using only `TwistedCharge` relations.
The existing generic oscillator and lattice-state results are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial
open Module (End)
open scoped BigOperators TensorProduct

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)

theorem mode_FgT (b : Fin (rank L)) (m : ℤ) :
    mode (FgT (Tm := Space L hEven C) b).1 m
      = (modeT (rank L) b (2 * m + 1)).rTensor _ := by
  rw [FgT_val, FgenT, mode_resc]
  push_cast
  rfl

theorem mode_YTLFld (α : L.carrier) (e m : ℤ) :
    mode (YTLFld L hEven C α e).1 m = YTL L hEven C α (2 * m + e) := by
  change mode (resc (YTL L hEven C α) 2 e) m = _
  rw [mode_resc]
  push_cast
  rfl

theorem YTL_tmul (α : L.carrier) (k : ℤ) (y : FockT (rank L))
    (t : Space L hEven C) :
    YTL L hEven C α k (y ⊗ₜ[ℂ] t)
      = ((2 : ℂ) ^ (-(L.form α α))) • (DD (chargeCoord L α) (-k - 2 + L.form α α) y
          ⊗ₜ[ℂ] eT L hEven C α t) :=
  YTg_tmul _ _ _ _ _ _ _

include hPos in
theorem YTLFld_translation (α : L.carrier) (e : ℤ) :
    Dα ((e : ℂ) / 2) (YTLFld L hEven C α e)
      = ∑ b, chargeCoord L α b • star (1 / 2) (FgT b) (-1) (YTLFld L hEven C α (e - 1)) := by
  -- the twisted product with the generator
  have hstar : ∀ b, star (1 / 2) (FgT b) (-1) (YTLFld L hEven C α (e - 1))
      = Fld.prod (-1) (FgT b) (YTLFld L hEven C α (e - 1))
        + (-(1 / 2 : ℂ) * chargeCoord L α b) • fzmul (-1) (YTLFld L hEven C α e) := by
    intro b
    rw [star_eq_sum_range _ _ _ _ 2 (fun i hi => by
      rw [← FgenTFld_eq_FgT]; exact prod_FgenTFld_YTLFld_pos L hEven C b α _ (by omega)),
      Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, add_zero, cbinom_zero, one_smul, neg_zero, fzmul_zero_shift,
      Nat.cast_one]
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, ← FgenTFld_eq_FgT, prod_FgenTFld_YTLFld_zero,
      FgenTFld_eq_FgT, show e - 1 + 1 = e by ring, fzmul_smul, smul_smul,
      show cbinom (-(1 / 2)) 1 = -(1 / 2) by simp [cbinom]]
  simp only [hstar, smul_add, Finset.sum_add_distrib]
  apply fld_ext_mode
  intro p x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | tmul y t =>
      obtain ⟨Q, hQ⟩ := EpC_eventually_zero (chargeCoord L α) y
      obtain ⟨V, hV⟩ := exists_pderiv_bound y
      obtain ⟨a, ha⟩ : ∃ a : ℤ, a = L.form α α - 2 * p - e := ⟨_, rfl⟩
      obtain ⟨P, hP⟩ : ∃ P : ℕ, P = V + (a + Q).toNat + 1 := ⟨_, rfl⟩
      have hP1 : ∀ n : ℕ, P ≤ n → DD (chargeCoord L α) (a - (2 * n + 1)) y = 0 := fun n hn =>
        DD_eq_zero_of_le _ y hQ (by omega)
      have hP2 : ∀ n : ℕ, P ≤ n → oscT (chargeCoord L α) (2 * n + 1) y = 0 := fun n hn => by
        rw [oscT_annihilation]
        rw [Finset.sum_eq_zero fun i _ => by rw [hV (n, i) (by simp; omega), smul_zero], smul_zero]
      have hE := DD_euler (chargeCoord L α) a y P hP1 hP2
      -- the left side
      have hL : mode (Dα ((e : ℂ) / 2) (YTLFld L hEven C α e)).1 p (y ⊗ₜ[ℂ] t)
          = (-(p : ℂ) - (e : ℂ) / 2) • ((2 : ℂ) ^ (-(L.form α α)) •
              (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven C α t)) := by
        rw [Dα, mode_fld_sub, mode_fld_smul, mode_fld_deriv, fzmul_val, mode_zmul,
          show p + -1 = p - 1 by ring, mode_YTLFld, YTL_tmul,
          show -(2 * (p - 1) + e) - 2 + L.form α α = a by rw [ha]; ring, sub_smul]
      -- the normal-ordered part
      have hterm : ∀ (b : Fin (rank L)) (n : ℕ),
          mode (FgT b).1 (-1 - n) (mode (YTLFld L hEven C α (e - 1)).1 (p + n) (y ⊗ₜ[ℂ] t))
            + mode (YTLFld L hEven C α (e - 1)).1 (p - 1 - n) (mode (FgT b).1 n (y ⊗ₜ[ℂ] t))
          = (2 : ℂ) ^ (-(L.form α α)) • ((modeT (rank L) b (-(2 * n + 1))
              (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven C α t) := by
        intro b n
        rw [mode_YTLFld, YTL_tmul, mode_FgT L hEven C, mode_FgT L hEven C, map_smul,
          LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, mode_YTLFld, YTL_tmul,
          show -(2 * (p + n) + (e - 1)) - 2 + L.form α α = a - (2 * n + 1) by rw [ha]; ring,
          show -(2 * (p - 1 - n) + (e - 1)) - 2 + L.form α α = a + (2 * n + 1) by rw [ha]; ring,
          show 2 * (-1 - (n : ℤ)) + 1 = -(2 * n + 1) by ring, ← smul_add,
          ← TensorProduct.add_tmul]
      have hN : ∀ b, mode (Fld.prod (-1) (FgT b) (YTLFld L hEven C α (e - 1))).1 p (y ⊗ₜ[ℂ] t)
          = ∑ n ∈ Finset.range P, (2 : ℂ) ^ (-(L.form α α)) • ((modeT (rank L) b (-(2 * n + 1))
              (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven C α t) := by
        intro b
        rw [mode_prod_neg_one, finsum_eq_sum_of_support_subset _ (s := Finset.range P) (by
          intro n hn
          rw [Function.mem_support] at hn
          by_contra hc
          rw [Finset.coe_range, Set.mem_Iio, not_lt] at hc
          apply hn
          rw [hterm, hP1 n hc, map_zero, zero_add, modeT_annihilation,
            hV (n, b) (by simp; omega), smul_zero, map_zero, TensorProduct.zero_tmul, smul_zero])]
        exact Finset.sum_congr rfl fun n _ => hterm b n
      rw [hL, mode_fld_add, mode_fld_sum, mode_fld_sum]
      simp only [mode_fld_smul, hN, fzmul_val, mode_zmul,
        show p + -1 = p - 1 by ring, mode_YTLFld, YTL_tmul,
        show -(2 * (p - 1) + e) - 2 + L.form α α = a by rw [ha]; ring]
      -- the oscillator sums
      have hosc : ∀ (K : ℤ) (z : FockT (rank L)),
          ∑ b, chargeCoord L α b • modeT (rank L) b K z = oscT (chargeCoord L α) K z := by
        intro K z
        rw [oscT, LinearMap.sum_apply]
        rfl
      have h1n : ∀ n : ℕ, ∑ b, chargeCoord L α b • ((2 : ℂ) ^ (-(L.form α α)) •
            ((modeT (rank L) b (-(2 * n + 1)) (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven C α t))
          = (2 : ℂ) ^ (-(L.form α α)) • ((vVarT (chargeCoord L α) n
              * DD (chargeCoord L α) (a - (2 * n + 1)) y
                + DD (chargeCoord L α) (a + (2 * n + 1)) (oscT (chargeCoord L α) (2 * n + 1) y))
                  ⊗ₜ[ℂ] eT L hEven C α t) := by
        intro n
        have hgen : ∀ (F : Fin (rank L) → FockT (rank L)),
            ∑ b, chargeCoord L α b • ((2 : ℂ) ^ (-(L.form α α)) • (F b ⊗ₜ[ℂ] eT L hEven C α t))
              = (2 : ℂ) ^ (-(L.form α α)) • ((∑ b, chargeCoord L α b • F b)
                  ⊗ₜ[ℂ] eT L hEven C α t) := by
          intro F
          rw [TensorProduct.sum_tmul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_comm,
            ← TensorProduct.smul_tmul']
        rw [hgen]
        congr 2
        rw [← oscT_creation, ← hosc, ← hosc, map_sum]
        simp only [smul_add, Finset.sum_add_distrib, map_smul]
      have h1 : ∑ b, chargeCoord L α b • ∑ n ∈ Finset.range P, (2 : ℂ) ^ (-(L.form α α)) •
            ((modeT (rank L) b (-(2 * n + 1)) (DD (chargeCoord L α) (a - (2 * n + 1)) y)
              + DD (chargeCoord L α) (a + (2 * n + 1)) (modeT (rank L) b (2 * n + 1) y))
                ⊗ₜ[ℂ] eT L hEven C α t)
          = (2 : ℂ) ^ (-(L.form α α)) • (((a : ℂ) / 2) • DD (chargeCoord L α) a y
              ⊗ₜ[ℂ] eT L hEven C α t) := by
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm, Finset.sum_congr rfl fun n _ => h1n n, ← Finset.smul_sum,
          ← TensorProduct.sum_tmul]
        congr 2
        rw [Finset.sum_add_distrib]
        have := congrArg (fun z => (1 / 2 : ℂ) • z) hE
        simp only [smul_add, Finset.smul_sum, smul_smul] at this
        rw [show (1 / 2 : ℂ) * (a : ℂ) = (a : ℂ) / 2 by ring] at this
        rw [this]
        norm_num
      have h2 : ∑ b, chargeCoord L α b • (-(1 / 2 : ℂ) * chargeCoord L α b) •
            (2 : ℂ) ^ (-(L.form α α)) • (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven C α t)
          = (-(1 / 2 : ℂ) * (L.form α α : ℂ)) • (2 : ℂ) ^ (-(L.form α α)) •
              (DD (chargeCoord L α) a y ⊗ₜ[ℂ] eT L hEven C α t) := by
        simp only [smul_smul, ← Finset.sum_smul]
        congr 1
        rw [← sum_chargeCoord L hPos α α, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [h1, h2, ha]
      push_cast
      module

include hPos in
theorem FL_T_echg (e : ℤ) (α : L.carrier) :
    FL L hEven C e ((latticeVOAGen L hEven hPos).toPreVertexAlgebra.T (echg L α))
      = Dα ((e : ℂ) / 2) (FL L hEven C e (echg L α)) := by
  rw [T_echg, map_sum, FL_echg L hEven C hPos, YTLFld_translation L hEven C hPos]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, show e = e - 1 + 1 by ring,
    show (-1 : ℤ) = -((0 : ℕ) : ℤ) - 1 by norm_num, FL_smul_hgen_neg L hEven C hPos,
    FL_echg L hEven C hPos, show e - 1 + 1 - 1 = e - 1 by ring]

end Lattice

end VOA.Moonshine.LatticeTwistedGeneral
