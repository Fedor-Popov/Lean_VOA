/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedGeneralModule
import VOA.Moonshine.TwistedPlus

/-! # The two parity pieces for arbitrary twisted charges
The conjugation proof is adapted from `TwistedPlusConj`; all generic
oscillator conjugation results and the fixed-point Jacobi theorem are reused. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open LatticeTwisted MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open IntegralLattice LatGen Extraspecial TwistedSector TwistedPlus
open Module (End)
open scoped BigOperators TensorProduct
section Lattice

open IntegralLattice LatGen Extraspecial TwistedSector

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)

theorem conj_YTL (α : L.carrier) (k : ℤ) :
    PT ∘ₗ YTL L hEven C α k ∘ₗ PT = YTL L hEven C (-α) k := by
  have hc : chargeCoord L (-α) = -chargeCoord L α := funext (chargeCoord_neg L α)
  have hf : L.form (-α) (-α) = L.form α α := by simp
  rw [YTL, YTL, hc, hf, eT_neg, conj_YTg]

theorem conjF_YTLFld (α : L.carrier) (e : ℤ) :
    conjF PT (YTLFld L hEven C α e) = YTLFld L hEven C (-α) e := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF]
  change (PT ∘ₗ mode (resc (YTL L hEven C α) 2 e) n ∘ₗ PT) x
    = mode (resc (YTL L hEven C (-α)) 2 e) n x
  rw [mode_resc, mode_resc, conj_YTL]

variable (hPos : L.PosDef)
include hPos

theorem conjF_Fw (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    conjF PT (Fw L hEven C α l e) = ((-1 : ℂ) ^ e) • Fw L hEven C α l e := by
  induction l generalizing e with
  | nil => rw [Fw_nil, conjF_YTLFld, YTLFld_neg]
  | cons c l ih =>
      rw [Fw_cons, ← star_conjF PT_PT (tloc L hEven C hPos (FgT_mem L hEven C c.2)
          (Fw_mem L hEven C hPos α l _)), conjF_FgT, ih,
        star_smul_left (tloc L hEven C hPos (FgT_mem L hEven C c.2)
          (smul_mem_tgenerated _ (Fw_mem L hEven C hPos α l _))),
        star_smul_right (tloc L hEven C hPos (FgT_mem L hEven C c.2)
          (Fw_mem L hEven C hPos α l _)), smul_smul]
      congr 1
      rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
      field_simp

theorem conjF_FL (e : ℤ) (u : LatModuleGen L) :
    conjF PT (FL L hEven C e u) = ((-1 : ℂ) ^ e) • FL L hEven C e u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, conjF_zero, smul_zero]
  | add x y hx hy => rw [map_add, conjF_add, hx, hy, smul_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, conjF_zero, smul_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, conjF_add, h₁, h₂, smul_add]
          | single α d =>
              rw [FL_monomial, conjF_smul, conjF_Fw L hEven C hPos, smul_comm]
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, conjF_add, hp, hq, smul_add]

theorem conj_YML (u : LatModuleGen L) (k : ℤ) :
    PT ∘ₗ YML L hEven C u k ∘ₗ PT = ((-1 : ℂ) ^ k) • YML L hEven C u k := by
  rw [YML_apply, ← mode_conjF, conjF_FL L hEven C hPos, Fld.smul_val, mode_smul]

noncomputable abbrev thetaTw : End ℂ (MT L hEven C) :=
  twTheta (rank L) (Space L hEven C)

omit hPos in
theorem thetaTw_thetaTw (x : MT L hEven C) : thetaTw L hEven C (thetaTw L hEven C x) = x :=
  twTheta_twTheta _ _ x

theorem YML_thetaTw (u : LatModuleGen L) (k : ℤ) :
    YML L hEven C (thetaLat L u) k
      = thetaTw L hEven C ∘ₗ YML L hEven C u k ∘ₗ thetaTw L hEven C := by
  rw [thetaTw, twTheta_eq]
  simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_neg]
  rw [conj_YML L hEven C hPos, YML_apply, YML_apply, FL_theta L hEven C hPos, Fld.smul_val,
    mode_smul]

variable [FiniteDimensional ℂ C.carrier]

theorem latticeTwistedModule_YM_theta (u : LatModuleGen L) (k : ℤ) :
    (latticeTwistedModule L hEven C hPos).YM (thetaAut L hEven hPos u) k
      = thetaTw L hEven C ∘ₗ (latticeTwistedModule L hEven C hPos).YM u k ∘ₗ
          thetaTw L hEven C :=
  YML_thetaTw L hEven C hPos u k
end Lattice

variable (L : IntegralLattice.{0}) (hEven : L.Even) (C : TwistedCharge L) (hPos : L.PosDef)
variable [FiniteDimensional ℂ C.carrier]

/-- The lift with minus sign on the charge space. Its fixed part has odd oscillator parity. -/
noncomputable def thetaLift : ThetaLift (latticeTwistedModule L hEven C hPos) where
  op := thetaTw L hEven C
  op_op := thetaTw_thetaTw L hEven C
  conj := latticeTwistedModule_YM_theta L hEven C hPos
  map_weight _ _ hx := twTheta_mem_weightLT hx

/-- Changing the sign of a lift exchanges its two eigenspaces. -/
def negateLift {V M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} {g : Aut W}
    {T : TwistedModule g 2 M} (θ : ThetaLift T) : ThetaLift T where
  op := -θ.op
  op_op x := by simp only [LinearMap.neg_apply, map_neg, neg_neg, θ.op_op]
  conj u k := by
    simpa only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg] using θ.conj u k
  map_weight α x hx := Submodule.neg_mem _ (θ.map_weight α x hx)

/-- The two eigenspaces form a direct sum of the whole twisted carrier. -/
theorem isCompl_lift_parities {V M : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} {g : Aut W}
    {T : TwistedModule g 2 M} (θ : ThetaLift T) :
    IsCompl (plusSub θ) (plusSub (negateLift θ)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hx' := (mem_plusSub θ).mp hx
    have hy' := (mem_plusSub (negateLift θ)).mp hy
    change -θ.op x = x at hy'
    rw [hx'] at hy'
    exact eq_zero_of_eq_neg hy'.symm
  · apply codisjoint_iff.mpr
    apply top_unique
    intro x _
    have hp : (1 / 2 : ℂ) • (x + θ.op x) ∈ plusSub θ := by
      rw [mem_plusSub]
      simp only [map_smul, map_add, θ.op_op, add_comm]
    have hn : (1 / 2 : ℂ) • (x - θ.op x) ∈ plusSub (negateLift θ) := by
      rw [mem_plusSub]
      change -θ.op ((1 / 2 : ℂ) • (x - θ.op x)) = _
      rw [map_smul, map_sub, θ.op_op, ← smul_neg, neg_sub]
    have he : (1 / 2 : ℂ) • (x + θ.op x) + (1 / 2 : ℂ) • (x - θ.op x) = x := by
      module
    exact he ▸ Submodule.add_mem_sup hp hn

/-- `false` selects even oscillator parity; `true` selects odd oscillator parity. -/
noncomputable def parityLift (odd : Bool) : ThetaLift (latticeTwistedModule L hEven C hPos) :=
  if odd then thetaLift L hEven C hPos else negateLift (thetaLift L hEven C hPos)

/-- Each parity piece is an ordinary module over the theta-fixed lattice VOA. -/
noncomputable def parityModule (odd : Bool) :
    OrdVModule (fixedVOA (thetaAut L hEven hPos))
      (plusSub (parityLift L hEven C hPos odd)) :=
  TwistedPlus.plusModule (parityLift L hEven C hPos odd)

theorem mode_parityModule (odd : Bool)
    (u : (orbifold (Subgroup.zpowers (thetaAut L hEven hPos))).carrier) (n : ℤ)
    (x : plusSub (parityLift L hEven C hPos odd)) :
    ((mode ((parityModule L hEven C hPos odd).YM u) n x :
      plusSub (parityLift L hEven C hPos odd)) : MT L hEven C) = YML L hEven C u.1 (2 * n) x :=
  TwistedPlus.mode_plusModule (parityLift L hEven C hPos odd) u n x

end VOA.Moonshine.LatticeTwistedGeneral
