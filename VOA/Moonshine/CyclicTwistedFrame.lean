/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TwistedPlusConj
import VOA.Moonshine.FrameTwisted
import VOA.Moonshine.InvFormTwisted

/-!
# The frame involution on the twisted sector lifts `g_χ`  (Moonshine step M8f, twisted half)

Let `L` be even unimodular, `χ : L → ℤ/2` a character and `w ∈ L` with `(-1)^{⟨w,α⟩} = (-1)^{χ α}`
(for the Leech lattice: `χ = β`, `w = 8e₀`, `FrameTwisted.lean`).  On `V_L^T = S[θ] ⊗ T` the
operator `P_J = id ⊗ J` (`J = c⁻¹ e_w`, `frameJ`) is a lift of the momentum-sign automorphism
`g_χ` (`LatGen.chiLat`):

  `Y^T(g_χ u)₍k/2₎ = P_J ∘ Y^T(u)₍k/2₎ ∘ P_J`     (`YML_chiLat`).

*Proof* (as for `θ`, `TwistedPlusConj.lean`): conjugation by the involution `P_J` is an
automorphism of the field calculus (`star_conjF`); it fixes the twisted Heisenberg generators
(`conjF_FgT_lTensor`: `P_J` acts on the other tensor factor) and multiplies `Y^T(e^α)` by
`(-1)^{χ α}`, because `J e_α J = (-1)^{⟨w,α⟩} e_α` (`frameJ_conj_eT`).  The inversion recursion
defining the word fields then gives `P_J F_e(p ⊗ e^α) P_J = (-1)^{χ α} F_e(p ⊗ e^α)`
(`conjF_Fw_frameJ`, `conjF_FL_frameJ`).

Consequently every mode of a `g_χ`-fixed state commutes with `P_J` and preserves the
two frame eigenspaces `S[θ] ⊗ T_±` (`twFrame`).

Also recorded, for the Leech module (transported along `rank Λ = 24`, as in `TwistedPlusConj`):
* `leechTwistedModule_YM_frameAut` — the lift statement;
* `leechTwistedModule_hgen` — `h_b(−1)𝟙` acts by `h_b(k/2) ⊗ 1` (and is `g_χ`-fixed);
* `leechTwistedModule_echg_vac` — `Y^T(e^α)₍(|α|²−2)/2₎ (1 ⊗ t) = 2^{−|α|²} (1 ⊗ e_α t)`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional (hypotheses `L.Even`, `L.PosDef`, unimodularity, and the displayed `hw`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

/-! ## `id ⊗ J` against the field calculus -/

section General

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

theorem conj_YTg_lTensor (J : End ℂ Tm) (v : Fin r → ℂ) (c0 : ℤ) (κ : ℂ) (g : End ℂ Tm) (k : ℤ) :
    J.lTensor (FockT r) ∘ₗ YTg v c0 κ g k ∘ₗ J.lTensor (FockT r) = YTg v c0 κ (J * g * J) k := by
  refine TensorProduct.ext' fun y t => ?_
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, YTg_tmul, map_smul,
    Module.End.mul_apply]

theorem YTg_smul_g (v : Fin r → ℂ) (c0 : ℤ) (κ s : ℂ) (g : End ℂ Tm) (k : ℤ) :
    YTg v c0 κ (s • g) k = s • YTg v c0 κ g k := by
  refine TensorProduct.ext' fun y t => ?_
  simp only [YTg_tmul, LinearMap.smul_apply, TensorProduct.tmul_smul, smul_comm s κ]

theorem conj_modeTT_lTensor {J : End ℂ Tm} (hJ : J * J = 1) (a : Fin r) (k : ℤ) :
    J.lTensor (FockT r) ∘ₗ modeTT (Tm := Tm) a k ∘ₗ J.lTensor (FockT r) = modeTT a k := by
  refine TensorProduct.ext' fun y t => ?_
  have h : J (J t) = t := by rw [← Module.End.mul_apply, hJ, Module.End.one_apply]
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, modeTT, LinearMap.rTensor_tmul, h]

theorem lTensor_lTensor_of_sq {J : End ℂ Tm} (hJ : J * J = 1) (x : FockT r ⊗[ℂ] Tm) :
    J.lTensor (FockT r) (J.lTensor (FockT r) x) = x := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← Module.End.mul_eq_comp, hJ,
    Module.End.one_eq_id, LinearMap.lTensor_id, LinearMap.id_apply]

theorem conjF_FgT_lTensor {J : End ℂ Tm} (hJ : J * J = 1) (a : Fin r) :
    conjF (J.lTensor (FockT r)) (FgT (Tm := Tm) a) = FgT a := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF, FgT_val, FgenT, mode_resc, conj_modeTT_lTensor hJ]

end General

/-! ## The lattice fields -/

section Lattice

open IntegralLattice LatGen Extraspecial FrameT

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (χ : L.carrier →+ ZMod 2) {w : L.carrier}
  (hw : ∀ α, (-1 : ℂ) ^ (L.form w α) = chiSign L χ α)

/-- The lift `P_J = id ⊗ J` on `S[θ] ⊗ T`. -/
noncomputable abbrev PJ (w : L.carrier) : End ℂ (MT L hEven hU) :=
  (frameJ L hEven hU w).lTensor (FockT (rank L))

theorem PJ_PJ (w : L.carrier) (x : MT L hEven hU) : PJ L hEven hU w (PJ L hEven hU w x) = x :=
  lTensor_lTensor_of_sq (frameJ_mul_self L hEven hU w) x

include hw in
/-- `J e_α J = (-1)^{χ α} e_α`. -/
theorem frameJ_conj_eT (α : L.carrier) :
    frameJ L hEven hU w * eT L hEven hU α * frameJ L hEven hU w = chiSign L χ α • eT L hEven hU α := by
  rw [frameJ_comm_sign, hw, smul_mul_assoc, mul_assoc, frameJ_mul_self, mul_one]

include hw in
theorem conj_YTL_frameJ (α : L.carrier) (k : ℤ) :
    PJ L hEven hU w ∘ₗ YTL L hEven hU α k ∘ₗ PJ L hEven hU w = chiSign L χ α • YTL L hEven hU α k := by
  rw [YTL, conj_YTg_lTensor, frameJ_conj_eT L hEven hU χ hw, YTg_smul_g]

include hw in
theorem conjF_YTLFld_frameJ (α : L.carrier) (e : ℤ) :
    conjF (PJ L hEven hU w) (YTLFld L hEven hU α e) = chiSign L χ α • YTLFld L hEven hU α e := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF, Fld.smul_val, mode_smul]
  change (PJ L hEven hU w ∘ₗ mode (resc (YTL L hEven hU α) 2 e) n ∘ₗ PJ L hEven hU w) x
    = (chiSign L χ α • mode (resc (YTL L hEven hU α) 2 e) n) x
  rw [mode_resc, conj_YTL_frameJ L hEven hU χ hw]

variable (hPos : L.PosDef)

include hw hPos in
/-- `P_J F_e(word over e^α) P_J = (-1)^{χ α} F_e(word over e^α)`. -/
theorem conjF_Fw_frameJ (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    conjF (PJ L hEven hU w) (Fw L hEven hU α l e) = chiSign L χ α • Fw L hEven hU α l e := by
  induction l generalizing e with
  | nil => rw [Fw_nil, conjF_YTLFld_frameJ L hEven hU χ hw]
  | cons c l ih =>
      rw [Fw_cons, ← star_conjF (PJ_PJ L hEven hU w) (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
          (Fw_mem L hEven hU hPos α l _)), conjF_FgT_lTensor (frameJ_mul_self L hEven hU w), ih,
        star_smul_right (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
          (Fw_mem L hEven hU hPos α l _))]

include hw hPos in
/-- `P_J F_e(u) P_J = F_e(g_χ u)` for every state `u ∈ V_L`. -/
theorem conjF_FL_frameJ (e : ℤ) (u : LatModuleGen L) :
    conjF (PJ L hEven hU w) (FL L hEven hU e u) = FL L hEven hU e (chiLat L χ u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, conjF_zero]
  | add x y hx hy => rw [map_add, conjF_add, hx, hy, map_add, map_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, conjF_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, conjF_add, h₁, h₂, map_add, map_add]
          | single α d =>
              have hs : Finsupp.single α d = d • eGen L α := by
                rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one]
              rw [FL_monomial, conjF_smul, conjF_Fw_frameJ L hEven hU χ hw hPos, hs,
                TensorProduct.tmul_smul, map_smul, chiLat_tmul, map_smul, map_smul,
                show eGen L α = Finsupp.single α 1 from rfl, FL_monomial, mul_one]
              simp only [smul_smul]
              congr 1
              ring
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, conjF_add, hp, hq, map_add, map_add]

include hw hPos in
/-- **`id ⊗ J` lifts `g_χ`**: `Y^T(g_χ u)₍k/2₎ = P_J ∘ Y^T(u)₍k/2₎ ∘ P_J`. -/
theorem YML_chiLat (u : LatModuleGen L) (k : ℤ) :
    YML L hEven hU (chiLat L χ u) k = PJ L hEven hU w ∘ₗ YML L hEven hU u k ∘ₗ PJ L hEven hU w := by
  rw [YML_apply, YML_apply, ← mode_conjF, conjF_FL_frameJ L hEven hU χ hw hPos]

/-! ## Transport along `rank L = r` -/

include hw in
theorem cast_YM_chiLat {r : ℕ} (h : rank L = r) (u : LatModuleGen L) (k : ℤ) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (chiLat L χ u) k
      = (frameJ L hEven hU w).lTensor (FockT r) ∘ₗ
          (h ▸ latticeTwistedModule L hEven hU hPos :
            TwistedModule (thetaAut L hEven hPos) 2
              (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM u k ∘ₗ
          (frameJ L hEven hU w).lTensor (FockT r) := by
  subst h
  exact YML_chiLat L hEven hU χ hw hPos u k

theorem cast_YM_hgen {r : ℕ} (h : rank L = r) (b : Fin r) :
    ∃ u : LatModuleGen L, (∀ (χ : L.carrier →+ ZMod 2), chiLat L χ u = u) ∧ ∀ k : ℤ,
      (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM u k
        = (modeT r b k).rTensor _ := by
  subst h
  refine ⟨hgen L b, fun χ => ?_, fun k => ?_⟩
  · rw [hgen, chiLat_tmul, chiSign_zero, one_smul]
  · exact InvForm.YML_hgen L hEven hU hPos b k

theorem cast_YM_echg_vac {r : ℕ} (h : rank L = r) (α : L.carrier)
    (t : Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM (echg L α)
          (L.form α α - 2) (vacT r ⊗ₜ t)
      = (2 : ℂ) ^ (-(L.form α α)) • (vacT r ⊗ₜ eT L hEven hU α t) := by
  subst h
  change YML L hEven hU (echg L α) (L.form α α - 2) (vacT (rank L) ⊗ₜ t) = _
  rw [InvForm.YML_echg L hEven hU hPos, YTL, YTg_tmul,
    show -(L.form α α - 2) - 2 + L.form α α = 0 by ring, vacT, DD_one,
    show sMz (chargeCoord L α) 0 = 1 by simp [sMz]]

end Lattice

end VOA.Moonshine.LatticeTwisted

/-! ## The Leech module -/

namespace VOA.Moonshine

open LatticeTwisted TwistedHeisenberg IntegralLattice LatGen Extraspecial FrameT
open Module (End)
open scoped TensorProduct

/-- **`id ⊗ J` lifts the frame automorphism on the Leech twisted module**:
`Y^T(g u)₍k/2₎ = (id ⊗ J) ∘ Y^T(u)₍k/2₎ ∘ (id ⊗ J)`, `g = frameAut`, `J = frameJ (8e₀)`. -/
theorem leechTwistedModule_YM_frameAut (u : LatModuleGen leech) (k : ℤ) :
    leechTwistedModule.YM (frameAut u) k
      = (frameJ leech leech_even leech_isUnit_det_gramMat frameW).lTensor (FockT 24) ∘ₗ
          leechTwistedModule.YM u k ∘ₗ
          (frameJ leech leech_even leech_isUnit_det_gramMat frameW).lTensor (FockT 24) :=
  cast_YM_chiLat leech leech_even leech_isUnit_det_gramMat frameChar frameW_sign leech_posDef
    leech_rank u k

/-- The twisted Heisenberg generators: for each `b : Fin 24` some `g`-fixed state acts by
`h_b(k/2) ⊗ 1`. -/
theorem leechTwistedModule_hgen (b : Fin 24) :
    ∃ u : LatModuleGen leech, frameAut u = u ∧ ∀ k : ℤ,
      leechTwistedModule.YM u k = (modeT 24 b k).rTensor leechT := by
  obtain ⟨u, hu, hk⟩ := cast_YM_hgen leech leech_even leech_isUnit_det_gramMat leech_posDef
    leech_rank b
  exact ⟨u, hu frameChar, hk⟩

/-- `Y^T(e^α)₍(|α|²−2)/2₎ (1 ⊗ t) = 2^{−|α|²} (1 ⊗ e_α t)`. -/
theorem leechTwistedModule_echg_vac (α : leech.carrier) (t : leechT) :
    leechTwistedModule.YM (echg leech α) (leech.form α α - 2) (vacT 24 ⊗ₜ t)
      = (2 : ℂ) ^ (-(leech.form α α)) • (vacT 24 ⊗ₜ eT leech leech_even leech_isUnit_det_gramMat α t) :=
  cast_YM_echg_vac leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank α t

end VOA.Moonshine
