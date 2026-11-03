/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedModule
import VOA.Moonshine.TwistedSectorDim

/-!
# `θ` on the twisted sector: the twisted module is `θ`-stable  (Moonshine step M8a, part 1)

Let `θ_T := thetaT ⊗ 1` on `S[θ] ⊗ T` (negate every twisted oscillator) and
`θ_tw := thetaT ⊗ (−1) = TwistedSector.twTheta` (FLM's lift, `θ = −1` on `T`).  Then

  `Y^T(θu)₍k/2₎ = θ_tw ∘ Y^T(u)₍k/2₎ ∘ θ_tw`     (`YML_thetaTw`).

The sign on `T` drops out of the conjugation (it is central), so the identity holds for either
lift; the choice `−1` only decides *which* eigenspace is the `+`-part (see `TwistedPlus.lean`).

Proof (no new analytic input).  Conjugation by the involution `θ_T` is an automorphism of the
field calculus (`prod_conjF`, `star_conjF`).  On the generators: `θ_T h_a(k/2) θ_T = −h_a(k/2)`
(`thetaT_modeT`), and `θ_T Y^T(e^α) θ_T = Y^T(e^{−α})` (`conj_YTL`), which is the charge
conjugation `θ E^±(α) θ = E^±(−α)` of the dressing (`thetaT_DD`, through `nexp_map` for
`E⁻` and an induction for the translation `E⁺`), together with `e_{−α} = e_α` on `T` (`eT_neg`).
By the inversion recursion defining the word fields this gives
`θ_T F_e(u) θ_T = (−1)ᵉ F_e(u)` (`conjF_FL`), and `FL_theta` (`F_e(θu) = (−1)ᵉ F_e(u)`) closes it.

## Main declarations
* `conjF P A` — the conjugated field `n ↦ P ∘ A n ∘ P`; `prod_conjF`, `star_conjF`.
* `thetaT_sM`, `thetaT_EpC`, `thetaT_DD`, `conj_YTg`, `conj_YTL`.
* `conjF_FgT`, `conjF_YTLFld`, `conjF_Fw`, `conjF_FL`, `conj_YML`.
* `YML_thetaTw` (all even positive-definite unimodular `L`), `latticeTwistedModule_YM_theta`.
* `leechTwistedModule_YM_theta` — the same for `leechTwistedModule` on `FockT 24 ⊗ T_Λ`, and
  `leechTwistedModule_weight` (its grading is `weightLT 24`).

## Status
All declarations `sorry`-free.  Unconditional (hypotheses `L.Even`, `L.PosDef`, unimodularity
only, discharged for `Λ`).
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

/-! ## Conjugating fields -/

section Conj

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem isField_conj (P : End ℂ M) {A : FormalDist (End ℂ M)} (hA : IsField A) :
    IsField (fun n => P ∘ₗ A n ∘ₗ P) := by
  intro x
  obtain ⟨B, hB⟩ := hA (P x)
  exact ⟨B, fun n hn => by
    simp only [LinearMap.comp_apply]
    rw [hB n hn, map_zero]⟩

/-- The conjugated field `n ↦ P ∘ A n ∘ P`. -/
noncomputable def conjF (P : End ℂ M) (A : Fld M) : Fld M :=
  ⟨fun n => P ∘ₗ A.1 n ∘ₗ P, isField_conj P A.2⟩

theorem mode_conjF (P : End ℂ M) (A : Fld M) (n : ℤ) :
    mode (conjF P A).1 n = P ∘ₗ mode A.1 n ∘ₗ P := by
  rw [mode_apply, mode_apply]; rfl

theorem conjF_zero (P : End ℂ M) : conjF P (0 : Fld M) = 0 := by
  apply Subtype.ext; funext n
  change P ∘ₗ (0 : End ℂ M) ∘ₗ P = 0
  rw [LinearMap.zero_comp, LinearMap.comp_zero]

theorem conjF_add (P : End ℂ M) (A B : Fld M) : conjF P (A + B) = conjF P A + conjF P B := by
  apply Subtype.ext; funext n
  change P ∘ₗ (A.1 n + B.1 n) ∘ₗ P = P ∘ₗ A.1 n ∘ₗ P + P ∘ₗ B.1 n ∘ₗ P
  rw [LinearMap.add_comp, LinearMap.comp_add]

theorem conjF_smul (P : End ℂ M) (c : ℂ) (A : Fld M) : conjF P (c • A) = c • conjF P A := by
  apply Subtype.ext; funext n
  change P ∘ₗ (c • A.1 n) ∘ₗ P = c • (P ∘ₗ A.1 n ∘ₗ P)
  rw [LinearMap.smul_comp, LinearMap.comp_smul]

theorem conjF_sum {ι : Type*} (P : End ℂ M) (s : Finset ι) (f : ι → Fld M) :
    conjF P (∑ i ∈ s, f i) = ∑ i ∈ s, conjF P (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, conjF_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, conjF_add, ih]

theorem conjF_fzmul (P : End ℂ M) (c : ℤ) (A : Fld M) :
    conjF P (fzmul c A) = fzmul c (conjF P A) := rfl

/-- Conjugation by an involution is a homomorphism for every field product. -/
theorem prod_conjF {P : End ℂ M} (hP : ∀ x, P (P x) = x) (ℓ : ℤ) (A B : Fld M) :
    Fld.prod ℓ (conjF P A) (conjF P B) = conjF P (Fld.prod ℓ A B) := by
  have hinj : Function.Injective (P : M →+ M) := fun x y h => by
    have := congrArg P h
    simpa [hP] using this
  apply fld_ext_mode
  intro N x
  rw [mode_conjF, LinearMap.comp_apply, LinearMap.comp_apply, Fld.mode_prod_iterate,
    Fld.mode_prod_iterate]
  change _ = (P : M →+ M) _
  rw [AddMonoidHom.map_finsum_of_injective _ hinj]
  refine finsum_congr fun i => ?_
  simp only [mode_conjF, LinearMap.comp_apply, hP, AddMonoidHom.coe_coe, map_sub, map_smul]

theorem star_conjF {P : End ℂ M} (hP : ∀ x, P (P x) = x) {A X : Fld M} (h : Local A.1 X.1)
    (α : ℂ) (p : ℤ) : star α (conjF P A) p (conjF P X) = conjF P (star α A p X) := by
  obtain ⟨K, hK⟩ := exists_prod_offset_zero h p
  rw [star_eq_sum_range α A p X K hK, star_eq_sum_range α (conjF P A) p (conjF P X) K
    (fun i hi => by rw [prod_conjF hP, hK i hi, conjF_zero]), conjF_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjF_smul, conjF_fzmul, prod_conjF hP]

end Conj

/-! ## Charge conjugation of the dressing -/

section Dressing

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

theorem thetaT_vVarT (v : Fin r → ℂ) (n : ℕ) : thetaT r (vVarT v n) = vVarT (-v) n := by
  rw [vVarT_neg, vVarT, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, thetaT_X, smul_neg]

theorem thetaT_dM (v : Fin r → ℂ) (k : ℕ) : thetaT r (dM v k) = dM (-v) k := by
  unfold dM
  split_ifs
  · rw [map_smul, thetaT_vVarT]
  · exact map_zero _

theorem thetaT_sM (v : Fin r → ℂ) (p : ℕ) : thetaT r (sM v p) = sM (-v) p := by
  have h := nexp_map (thetaT r).toAlgHom (dM v) p
  rw [sM, sM]
  convert h using 2
  funext k
  exact (thetaT_dM v k).symm

theorem thetaT_sMz (v : Fin r → ℂ) (p : ℤ) : thetaT r (sMz v p) = sMz (-v) p := by
  unfold sMz
  split_ifs
  · exact thetaT_sM v _
  · exact map_zero _

theorem thetaT_C (c : ℂ) : thetaT r (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]

theorem thetaT_EpC (v : Fin r → ℂ) (y : FockT r) :
    ∀ q : ℕ, thetaT r (EpC v q y) = EpC (-v) q (thetaT r y) := by
  induction y using MvPolynomial.induction_on with
  | C c =>
      intro q
      rw [EpC_C, thetaT_C, EpC_C]
      split_ifs
      · exact thetaT_C c
      · exact map_zero _
  | add a b ha hb => intro q; rw [map_add, map_add, ha, hb, map_add, map_add]
  | mul_X a x ha =>
      intro q
      rw [EpC_mul_X, map_mul, thetaT_X, mul_neg, map_neg, EpC_mul_X, map_sub, map_mul, thetaT_X,
        ha q]
      split_ifs
      · rw [map_smul, ha, Pi.neg_apply, neg_smul]
        ring
      · rw [map_zero]
        ring

theorem thetaT_DD (v : Fin r → ℂ) (a : ℤ) (y : FockT r) :
    thetaT r (DD v a y) = DD (-v) a (thetaT r y) := by
  obtain ⟨Q, hQ⟩ := EpC_eventually_zero v y
  rw [DD_apply_range v a y Q hQ, DD_apply_range (-v) a (thetaT r y) Q (fun q hq => by
    rw [← thetaT_EpC, hQ q hq, map_zero]), map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, thetaT_sMz, thetaT_EpC]

/-- `θ_T = thetaT ⊗ 1` on `S[θ] ⊗ T`. -/
noncomputable abbrev PT : End ℂ (FockT r ⊗[ℂ] Tm) := (thetaT r).toLinearMap.rTensor Tm

theorem PT_PT (x : FockT r ⊗[ℂ] Tm) : PT (PT x) = x := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  have h : (thetaT r).toLinearMap ∘ₗ (thetaT r).toLinearMap = LinearMap.id :=
    LinearMap.ext fun p => thetaT_thetaT r p
  rw [h, LinearMap.rTensor_id, LinearMap.id_apply]

/-- `θ_T Y^T_v θ_T = Y^T_{−v}` for the generic exponential field. -/
theorem conj_YTg (v : Fin r → ℂ) (c0 : ℤ) (κ : ℂ) (g : End ℂ Tm) (k : ℤ) :
    PT ∘ₗ YTg v c0 κ g k ∘ₗ PT = YTg (-v) c0 κ g k := by
  refine TensorProduct.ext' fun y t => ?_
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply, YTg_tmul,
    map_smul, thetaT_DD, thetaT_thetaT]

/-- `θ_T h_a(k/2) θ_T = −h_a(k/2)`. -/
theorem conj_modeTT (a : Fin r) (k : ℤ) :
    PT ∘ₗ modeTT (Tm := Tm) a k ∘ₗ PT = -modeTT a k := by
  refine TensorProduct.ext' fun y t => ?_
  simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, AlgEquiv.toLinearMap_apply, modeTT,
    thetaT_modeT, thetaT_thetaT, LinearMap.neg_apply, TensorProduct.neg_tmul]

theorem conjF_FgT (a : Fin r) : conjF PT (FgT (Tm := Tm) a) = (-1 : ℂ) • FgT a := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF, Fld.smul_val, mode_smul, FgT_val, FgenT, mode_resc, conj_modeTT]
  simp

end Dressing

/-! ## The lattice fields -/

section Lattice

open IntegralLattice LatGen Extraspecial TwistedSector

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)

/-- `θ_T Y^T(e^α) θ_T = Y^T(e^{−α})`. -/
theorem conj_YTL (α : L.carrier) (k : ℤ) :
    PT ∘ₗ YTL L hEven hU α k ∘ₗ PT = YTL L hEven hU (-α) k := by
  have hc : chargeCoord L (-α) = -chargeCoord L α := funext (chargeCoord_neg L α)
  have hf : L.form (-α) (-α) = L.form α α := by simp
  rw [YTL, YTL, hc, hf, eT_neg, conj_YTg]

theorem conjF_YTLFld (α : L.carrier) (e : ℤ) :
    conjF PT (YTLFld L hEven hU α e) = YTLFld L hEven hU (-α) e := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF]
  change (PT ∘ₗ mode (resc (YTL L hEven hU α) 2 e) n ∘ₗ PT) x
    = mode (resc (YTL L hEven hU (-α)) 2 e) n x
  rw [mode_resc, mode_resc, conj_YTL]

variable (hPos : L.PosDef)
include hPos

/-- `θ_T F_e(word over e^α) θ_T = (−1)ᵉ F_e(word over e^α)`. -/
theorem conjF_Fw (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    conjF PT (Fw L hEven hU α l e) = ((-1 : ℂ) ^ e) • Fw L hEven hU α l e := by
  induction l generalizing e with
  | nil => rw [Fw_nil, conjF_YTLFld, YTLFld_neg]
  | cons c l ih =>
      rw [Fw_cons, ← star_conjF PT_PT (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
          (Fw_mem L hEven hU hPos α l _)), conjF_FgT, ih,
        star_smul_left (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
          (smul_mem_tgenerated _ (Fw_mem L hEven hU hPos α l _))),
        star_smul_right (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
          (Fw_mem L hEven hU hPos α l _)), smul_smul]
      congr 1
      rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_one]
      field_simp

/-- `θ_T F_e(u) θ_T = (−1)ᵉ F_e(u)` for every state `u ∈ V_L`. -/
theorem conjF_FL (e : ℤ) (u : LatModuleGen L) :
    conjF PT (FL L hEven hU e u) = ((-1 : ℂ) ^ e) • FL L hEven hU e u := by
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
              rw [FL_monomial, conjF_smul, conjF_Fw L hEven hU hPos, smul_comm]
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, conjF_add, hp, hq, smul_add]

/-- `θ_T Y^T(u)₍k/2₎ θ_T = (−1)ᵏ Y^T(u)₍k/2₎`. -/
theorem conj_YML (u : LatModuleGen L) (k : ℤ) :
    PT ∘ₗ YML L hEven hU u k ∘ₗ PT = ((-1 : ℂ) ^ k) • YML L hEven hU u k := by
  rw [YML_apply, ← mode_conjF, conjF_FL L hEven hU hPos, Fld.smul_val, mode_smul]

/-- **FLM's `θ` on the twisted sector**, `θ_tw = thetaT ⊗ (−1)` (`= TwistedSector.twTheta`). -/
noncomputable abbrev thetaTw : End ℂ (MT L hEven hU) :=
  twTheta (rank L) (Rep (cocMat L) (isUnit_det_cocMat L hEven hU))

omit hPos in
theorem thetaTw_thetaTw (x : MT L hEven hU) : thetaTw L hEven hU (thetaTw L hEven hU x) = x :=
  twTheta_twTheta _ _ x

/-- **The twisted module is `θ`-stable**: `Y^T(θu)₍k/2₎ = θ_tw ∘ Y^T(u)₍k/2₎ ∘ θ_tw`. -/
theorem YML_thetaTw (u : LatModuleGen L) (k : ℤ) :
    YML L hEven hU (thetaLat L u) k
      = thetaTw L hEven hU ∘ₗ YML L hEven hU u k ∘ₗ thetaTw L hEven hU := by
  rw [thetaTw, twTheta_eq]
  simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_neg]
  rw [conj_YML L hEven hU hPos, YML_apply, YML_apply, FL_theta L hEven hU hPos, Fld.smul_val,
    mode_smul]

theorem latticeTwistedModule_YM_theta (u : LatModuleGen L) (k : ℤ) :
    (latticeTwistedModule L hEven hU hPos).YM (thetaAut L hEven hPos u) k
      = thetaTw L hEven hU ∘ₗ (latticeTwistedModule L hEven hU hPos).YM u k ∘ₗ
          thetaTw L hEven hU :=
  YML_thetaTw L hEven hU hPos u k

/-- Transport of the `θ`-stability along `rank L = r`. -/
theorem cast_YM_theta {r : ℕ} (h : rank L = r) (u : LatModuleGen L) (k : ℤ) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM
        (thetaAut L hEven hPos u) k
      = twTheta r (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) ∘ₗ
          (h ▸ latticeTwistedModule L hEven hU hPos :
            TwistedModule (thetaAut L hEven hPos) 2
              (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).YM u k ∘ₗ
          twTheta r (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) := by
  subst h
  exact YML_thetaTw L hEven hU hPos u k

/-- Transport of the grading along `rank L = r`. -/
theorem cast_weight {r : ℕ} (h : rank L = r) (α : ℂ) :
    (h ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2
          (FockT r ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU))).weight α
      = weightLT r (Rep (cocMat L) (isUnit_det_cocMat L hEven hU)) α := by
  subst h
  rfl

end Lattice

/-! ## The Leech case -/

section Leech

open IntegralLattice LatGen Extraspecial TwistedSector

/-- **`θ`-stability of the Leech twisted module** on `FockT 24 ⊗ T_Λ`:
`Y^T(θu)₍k/2₎ = θ_tw ∘ Y^T(u)₍k/2₎ ∘ θ_tw` with `θ_tw = twTheta 24 T_Λ = thetaT ⊗ (−1)`. -/
theorem leechTwistedModule_YM_theta (u : LatModuleGen leech) (k : ℤ) :
    leechTwistedModule.YM (leechTheta u) k
      = twTheta 24 leechT ∘ₗ leechTwistedModule.YM u k ∘ₗ twTheta 24 leechT :=
  cast_YM_theta leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank u k

/-- The grading of the Leech twisted module is `weightLT 24`. -/
theorem leechTwistedModule_weight (α : ℂ) :
    leechTwistedModule.weight α = weightLT 24 leechT α :=
  cast_weight leech leech_even leech_isUnit_det_gramMat leech_posDef leech_rank α

end Leech

end VOA.Moonshine.LatticeTwisted
