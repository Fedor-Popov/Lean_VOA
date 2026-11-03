/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LeeYangC2
import VOA.Examples.ZhuTripletW2
import VOA.Modules.ZhuVermaAnArchAModScope

/-!
# The Lee--Yang relation in Zhu's algebra

The level-four null vector of the simple Virasoro VOA `L(-22/5,0)` gives the honest Zhu-algebra
relation

`5 [omega]^2 + [omega] = 0`.

Consequently, whenever `[omega]` acts by a scalar `h` on a nonzero Zhu module, that scalar is
`0` or `-1/5`.  In particular every realized lowest-weight module has one of those two lowest
weights.

The file also turns the actual level-zero piece of an arbitrary `AdmissibleModule` into a bundled
`AMod`, using the proved `AdmLev` zero-mode laws.  This is still not admissible rationality:
admissible modules impose neither a nonzero bottom nor scalar `L₀`, and the repository contains no
extension-splitting theorem from bottom Zhu modules to complete reducibility of admissible modules.
-/

namespace VOA.LeeYangZhu

set_option maxHeartbeats 200000

open VOA
open VOA.VertexOperatorAlgebra
open VOA.VirModule
open VOA.VirSimple
open VOA.VirQuotForm
open VOA.LeeYang
open VOA.ZhuW2

private noncomputable abbrev WLY := virasoroSimple leeYangC

/-- The conformal-vector class in the Lee--Yang Zhu algebra. -/
noncomputable abbrev omegaA : A WLY := mk WLY WLY.conformalVector

/-- In the Lee--Yang simple quotient, the Zhu class of `L_{-2}^2|0>` is
`[omega]^2 + 2[omega]`. -/
theorem mk_mkQ_L2L2vac :
    mk WLY ((maxIdealVir leeYangC).mkQ (L2L2vac leeYangC)) =
      Amul (zhuRingData_holds WLY) omegaA omegaA + (2 : ℂ) • omegaA := by
  have houter := mkQ_L leeYangC (-2) (L2vac leeYangC)
  rw [virasoroVOA_L_eq_Lop, L2vac] at houter
  have hstate : (maxIdealVir leeYangC).mkQ (L2L2vac leeYangC) =
      WLY.smul WLY.conformalVector (-1) WLY.conformalVector := by
    rw [L2L2vac, houter,
      show (maxIdealVir leeYangC).mkQ (Lop leeYangC (-2) (vacVec leeYangC)) =
        WLY.conformalVector by rfl,
      VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def]
    norm_num
  rw [hstate, omega_sq]
  module

/-- In the Lee--Yang simple quotient, `[L_{-4}|0>] = 3[omega]` in Zhu's algebra. -/
theorem mk_mkQ_L4vac :
    mk WLY ((maxIdealVir leeYangC).mkQ (L4vac leeYangC)) = (3 : ℂ) • omegaA := by
  have h2 := mkQ_L leeYangC (-1) (L2vac leeYangC)
  rw [virasoroVOA_L_eq_Lop, Lop_neg_one_L2vac] at h2
  have h3 := mkQ_L leeYangC (-1) (L3vac leeYangC)
  rw [virasoroVOA_L_eq_Lop, Lop_neg_one_L3vac, map_smul] at h3
  have htrans : WLY.L (-1) (WLY.L (-1) WLY.conformalVector) =
      (2 : ℂ) • (maxIdealVir leeYangC).mkQ (L4vac leeYangC) := by
    change (virasoroSimple leeYangC).L (-1)
      ((virasoroSimple leeYangC).L (-1) ((maxIdealVir leeYangC).mkQ (L2vac leeYangC))) = _
    rw [h3, ← h2]
  have hmem : WLY.L (-1) WLY.conformalVector ∈ WLY.grading 3 := by
    have h := WLY.smul_mem_grading WLY.conformalVector_mem_grading_two
      WLY.conformalVector_mem_grading_two (0 : ℤ)
    simpa only [VertexOperatorAlgebra.L_def,
      show ((-1 : ℤ) + 1) = 0 by norm_num,
      show (2 + 2 - 0 - 1 : ℤ) = 3 by norm_num] using h
  have hfirst := mk_L_neg_one_of_mem_grading WLY WLY.conformalVector_mem_grading_two
  have hsecond := mk_L_neg_one_of_mem_grading WLY hmem
  rw [htrans, map_smul] at hsecond
  rw [hfirst] at hsecond
  have htwo : (2 : ℂ) • mk WLY ((maxIdealVir leeYangC).mkQ (L4vac leeYangC)) =
      (6 : ℂ) • omegaA := by
    rw [smul_smul] at hsecond
    norm_num at hsecond
    exact hsecond
  apply sub_eq_zero.mp
  apply eq_zero_of_smul_eq_zero (by norm_num : (2 : ℂ) ≠ 0)
  rw [smul_sub, htwo, smul_smul]
  norm_num

/-- The Lee--Yang quadratic Zhu relation: `5[omega]^2 + [omega] = 0`. -/
theorem leeYang_zhu_polynomial :
    (5 : ℂ) • Amul (zhuRingData_holds WLY) omegaA omegaA + omegaA = 0 := by
  have h := congrArg (mk WLY) mkQ_leeYangSingular_eq_zero
  simp only [leeYangSingular, map_add, map_smul, map_zero,
    mk_mkQ_L2L2vac, mk_mkQ_L4vac] at h
  rw [smul_add, smul_smul, smul_smul] at h
  norm_num at h
  rw [← Amul_mk] at h
  rw [add_assoc, ← neg_smul, ← add_smul] at h
  norm_num at h
  exact h

/-- The Lee--Yang polynomial acts by zero in every bundled Zhu module. -/
theorem rho_omega_polynomial (U : AMod WLY) :
    (5 : ℂ) • (U.ρ omegaA * U.ρ omegaA) + U.ρ omegaA = 0 := by
  have h := congrArg U.ρ leeYang_zhu_polynomial
  simpa only [map_add, map_smul, map_zero, AMod_rho_Amul] using h

/-- On a nonzero Zhu module where `[omega]` is scalar, that scalar is `0` or `-1/5`. -/
theorem omegaScalar_eq_zero_or_neg_one_fifth (U : AMod WLY) [Nontrivial U.carrier]
    {h : ℂ} (hU : U.OmegaScalar h) : h = 0 ∨ h = -(1 / 5 : ℂ) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : U.carrier)
  have hop := rho_omega_polynomial U
  have happ := LinearMap.congr_fun hop x
  rw [hU] at happ
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply, smul_smul] at happ
  have hpoly : 5 * h ^ 2 + h = 0 := by
    by_contra hne
    have hx0 : x = 0 := eq_zero_of_smul_eq_zero hne (by
      simpa only [add_smul, mul_smul, one_smul, pow_two] using happ)
    exact hx hx0
  have hfac : h * (5 * h + 1) = 0 := by
    calc
      h * (5 * h + 1) = 5 * h ^ 2 + h := by ring
      _ = 0 := hpoly
  rcases mul_eq_zero.mp hfac with hz | hz
  · exact Or.inl hz
  · right
    linear_combination (1 / 5 : ℂ) * hz

/-- Every realized Lee--Yang lowest-weight module has lowest weight `0` or `-1/5`. -/
theorem lowestWeight_eq_zero_or_neg_one_fifth (P : LWModule WLY) :
    P.h = 0 ∨ P.h = -(1 / 5 : ℂ) := by
  letI : Nontrivial P.toAMod.carrier := nontrivial_toAMod P
  exact omegaScalar_eq_zero_or_neg_one_fifth P.toAMod P.toAMod_omegaScalar

/-! ## The actual level-zero Zhu module of an admissible module -/

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- An `AdmissibleModule` supplies the weaker `AdmLev` interface consumed by the proved bottom
zero-mode laws. -/
def admissibleAdmLev (N : AdmissibleModule WLY M) : AdmLev WLY N.toWeakModule where
  lev := N.lev
  lev_neg := N.lev_eq_bot_of_neg
  act_lev := N.act_lev

/-- The zero-mode action on the level-zero piece before descent through `O(V)`. -/
noncomputable def admissibleBottomRhoV (N : AdmissibleModule WLY M) :
    (VirUniv leeYangC ⧸ maxIdealVir leeYangC) →ₗ[ℂ] Module.End ℂ (N.lev 0) where
  toFun v :=
    { toFun := fun x => ⟨oLevW N.toWeakModule 0 v (x : M), by
          simpa using oLevW_mem_lev (admissibleAdmLev N) 0 v x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add _ _ _
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact map_smul _ _ _ }
  map_add' := by
    intro u v
    ext x
    simp
  map_smul' := by
    intro c v
    ext x
    simp

theorem O_le_ker_admissibleBottomRhoV (N : AdmissibleModule WLY M) :
    O WLY ≤ LinearMap.ker (admissibleBottomRhoV N) := by
  intro v hv
  rw [LinearMap.mem_ker]
  ext x
  exact O_annihilates_lev_zero (admissibleAdmLev N) hv x.2

/-- The descended Zhu action on the actual level-zero piece of an arbitrary admissible module. -/
noncomputable def admissibleBottomRho (N : AdmissibleModule WLY M) :
    A WLY →ₗ[ℂ] Module.End ℂ (N.lev 0) :=
  (O WLY).liftQ (admissibleBottomRhoV N) (O_le_ker_admissibleBottomRhoV N)

@[simp] theorem admissibleBottomRho_mk (N : AdmissibleModule WLY M)
    (v : VirUniv leeYangC ⧸ maxIdealVir leeYangC) :
    admissibleBottomRho N (mk WLY v) = admissibleBottomRhoV N v := by
  rw [admissibleBottomRho, mk, Submodule.mkQ_apply, Submodule.liftQ_apply]

/-- The level-zero piece of every admissible Lee--Yang module is a genuine bundled Zhu module. -/
noncomputable def admissibleBottomAMod (N : AdmissibleModule WLY M) : AMod WLY where
  carrier := N.lev 0
  ρ := admissibleBottomRho N
  ρ_one := by
    ext x
    change oLevW N.toWeakModule 0 WLY.vacuum (x : M) = x
    rw [oLevW_homogeneous N.toWeakModule 0 WLY.vacuum_mem_grading_zero,
      N.toWeakModule.vacuum_YM, mode_one]
    simp
  ρ_mul := by
    intro u v
    ext x
    exact oLevW_zhuMul_lev_zero (admissibleAdmLev N) u v x.2

/-- The Lee--Yang quadratic polynomial acts by zero on the actual bottom of every admissible
module, without any ordinary-module or `L₀`-semisimplicity assumption. -/
theorem admissibleBottom_omega_polynomial (N : AdmissibleModule WLY M) :
    (5 : ℂ) • ((admissibleBottomAMod N).ρ omegaA *
      (admissibleBottomAMod N).ρ omegaA) + (admissibleBottomAMod N).ρ omegaA = 0 :=
  rho_omega_polynomial (admissibleBottomAMod N)

/-- If the admissible bottom is nonzero and `L₀ = [omega]` is scalar there, its scalar is one
of the two Lee--Yang lowest weights.  Neither nonzeroness nor scalarity is part of
`AdmissibleModule`. -/
theorem admissibleBottomScalar_eq_zero_or_neg_one_fifth (N : AdmissibleModule WLY M)
    [Nontrivial (N.lev 0)] {h : ℂ} (hN : (admissibleBottomAMod N).OmegaScalar h) :
    h = 0 ∨ h = -(1 / 5 : ℂ) := by
  letI : Nontrivial (admissibleBottomAMod N).carrier := by
    change Nontrivial (N.lev 0)
    infer_instance
  exact omegaScalar_eq_zero_or_neg_one_fifth (admissibleBottomAMod N) hN

end VOA.LeeYangZhu
