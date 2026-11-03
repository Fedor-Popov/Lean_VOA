/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteOmega
import VOA.Examples.Sl2CosetConcreteVertex
import VOA.Examples.Sl2CosetConcreteTensorConformal
import VOA.Examples.Sl2CosetConcreteCohomology

/-! # Conformal structure on the actual diagonal coset -/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite Sl2Coset
open Module (End)
open scoped TensorProduct

noncomputable section

/-- Subtracting a commuting Virasoro summand subtracts its central charge. -/
theorem virasoro_difference_of_commute {M : Type*} [AddCommGroup M] [Module ℂ M]
    (L D : ℤ → End ℂ M) (c d : ℂ)
    (hL : ∀ m n : ℤ, ⁅L m, L n⁆ = ((m : ℂ) - n) • L (m + n) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * c) • (1 : End ℂ M) else 0)
    (hD : ∀ m n : ℤ, ⁅D m, D n⁆ = ((m : ℂ) - n) • D (m + n) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * d) • (1 : End ℂ M) else 0)
    (hc : ∀ m n : ℤ, D m * (L n - D n) = (L n - D n) * D m) (m n : ℤ) :
    ⁅L m - D m, L n - D n⁆ = ((m : ℂ) - n) • (L (m + n) - D (m + n)) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (c - d)) •
        (1 : End ℂ M) else 0 := by
  have hbr : ⁅L m - D m, L n - D n⁆ = ⁅L m, L n⁆ - ⁅D m, D n⁆ := by
    calc
      _ = ⁅L m, L n⁆ - ⁅D m, D n⁆ -
          (D m * (L n - D n) - (L n - D n) * D m) +
          (D n * (L m - D m) - (L m - D m) * D n) := by
        simp only [LieRing.of_associative_ring_bracket]
        noncomm_ring
      _ = _ := by rw [hc m n, hc n m, sub_self, sub_self, sub_zero, add_zero]
  rw [hbr, hL, hD]
  by_cases hmn : m + n = 0
  · simp only [if_pos hmn, smul_sub, mul_sub, sub_smul]
    abel
  · simp only [if_neg hmn, add_zero, smul_sub]

/-- The first simple factor has central charge minus six. -/
theorem aCentralCharge : AVOA.centralCharge = -6 := by
  change (AffineSl2GeneralRigidity.universal ALevel aNoncritical).centralCharge = _
  rw [AffineVOA.Inst.closed_centralCharge, aLevel_eq]
  norm_num

/-- The level-one simple factor has central charge one. -/
theorem bCentralCharge : BVOA.centralCharge = 1 := by
  change (AffineSl2GeneralRigidity.universal 1 bNoncritical).centralCharge = _
  rw [AffineVOA.Inst.closed_centralCharge]
  norm_num

/-- Subtracting diagonal charge minus three fifths gives the Lee–Yang charge. -/
theorem cosetCentralCharge :
    AVOA.centralCharge + BVOA.centralCharge -
      3 * ((-4 / 3 : ℂ) + 1) / (((-4 / 3 : ℂ) + 1) + 2) = -22 / 5 := by
  rw [aCentralCharge, bCentralCharge]
  norm_num

/-- The actual conformal difference satisfies Virasoro at the Lee–Yang charge. -/
theorem cosetOmega_virasoro (m n : ℤ) :
    ⁅mode (abSVA.Y cosetOmega) (m + 1), mode (abSVA.Y cosetOmega) (n + 1)⁆ =
      ((m : ℂ) - n) • mode (abSVA.Y cosetOmega) (m + n + 1) +
      if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * (-22 / 5)) •
        (1 : End ℂ (ASpace ⊗[ℂ] BSpace)) else 0 := by
  let L : ℤ → End ℂ (ASpace ⊗[ℂ] BSpace) :=
    fun n => mode (abSVA.Y ambientConformal) (n + 1)
  let D : ℤ → End ℂ (ASpace ⊗[ℂ] BSpace) :=
    fun n => mode (abSVA.Y diagonalSugawara) (n + 1)
  have hL := tensorConformal_virasoro AVOA BVOA
  have hD := sugawara_virasoro diagonalAction.toAffineSl2Action
    diagonalAction.translation (by norm_num : (-4 / 3 : ℂ) + 1 + 2 ≠ 0)
  have hC : ∀ m n, D m * (L n - D n) = (L n - D n) * D m := by
    intro m n
    have hc := sugawara_mode_coset_mode_commute diagonalAction.toAffineSl2Action
      diagonalAction.translation cosetOmega_mem (m + 1) (n + 1)
    simpa only [cosetOmega, map_sub, mode_sub] using hc
  have h := virasoro_difference_of_commute L D
    (AVOA.centralCharge + BVOA.centralCharge)
    (3 * ((-4 / 3 : ℂ) + 1) / (((-4 / 3 : ℂ) + 1) + 2)) hL hD hC m n
  rw [cosetCentralCharge] at h
  simpa only [L, D, cosetOmega, map_sub, mode_sub] using h

/-- Weight two of the conformal state in the integer-graded coset vertex algebra. -/
theorem cosetOmegaState_weight : cosetOmegaState ∈ cosetVertexAlgebra.grading 2 := by
  change cosetOmega ∈ abSVA.grading ((2 : ℤ) : ℂ)
  norm_num only [Int.cast_ofNat]
  exact cosetOmega_weight

/-- The actual conformal VOA on the diagonal-current commutant. -/
def cosetVOA : VertexOperatorAlgebra CosetSpace where
  toPreVertexAlgebra := cosetVertexAlgebra
  conformalVector := cosetOmegaState
  conformal_mem := cosetOmegaState_weight
  centralCharge := -22 / 5
  virasoro := by
    intro m n
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : End ℂ (ASpace ⊗[ℂ] BSpace) => f (x : ASpace ⊗[ℂ] BSpace))
      (cosetOmega_virasoro m n)
    simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
      Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul] at h ⊢
    by_cases hmn : m + n = 0
    · simpa only [if_pos hmn, LinearMap.smul_apply, Module.End.one_apply,
        Submodule.coe_smul, cosetY_mode_coe] using h
    · simpa only [if_neg hmn, LinearMap.zero_apply, Submodule.coe_zero,
        cosetY_mode_coe] using h
  L0_grading := by
    intro n x hx
    exact Subtype.ext (cosetOmega_L0 (n : ℂ) x hx x.property)
  translation := by
    intro x
    funext j
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact congrArg (fun f : FormalDist (End ℂ (ASpace ⊗[ℂ] BSpace)) => f j y)
      (cosetOmega_translation x x.property)
  vacuum_grade := cosetVertexAlgebra_vacuum_grade
  positivity := cosetVertexAlgebra_positivity

@[simp] theorem cosetVOA_vacuum :
    cosetVOA.vacuum = cosetVacuum diagonalAction.toAffineSl2Action := rfl

@[simp] theorem cosetVOA_mode (x y : CosetSpace) (n : ℤ) :
    cosetVOA.smul x n y =
      cosetMode diagonalAction.toAffineSl2Action diagonalAction.translation x n y := rfl

@[simp] theorem cosetVOA_conformalVector : cosetVOA.conformalVector = cosetOmegaState := rfl

@[simp] theorem cosetVOA_centralCharge : cosetVOA.centralCharge = -22 / 5 := rfl

/-- With the actual coset VOA constructed, only its simplicity remains for injectivity. -/
theorem leeYangCosetToH0_injective_of_cosetSimple (hsimple : cosetVOA.IsSimple) :
    Function.Injective leeYangCosetToH0 :=
  leeYangCosetToH0_injective cosetVOA hsimple cosetVOA_vacuum cosetVOA_mode

end
end VOA.Sl2CosetConcrete
