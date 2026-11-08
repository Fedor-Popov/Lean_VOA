import VOA.Moonshine.MoonshineLRLiftLattice
import VOA.Moonshine.InvFormTP

/-!
# Extraspecial charge operators on the twisted lattice module

The momentum character is the pairing modulo two. The charge operator is `id ⊗ eT μ`.
Conjugation by a scalar normalization of this operator propagates through the word fields.
The raw charge operator scales the invariant form; its multiplier is recorded explicitly.

`extraPhi_YML` proves intertwining for every state of an even positive-definite unimodular
lattice. `extraLeechPhi_YM` transports this to the Leech module with oscillator rank 24.
`extraPlusPhi_mode` restricts it to `TP` and `extraLeechPlusAut` on the fixed lattice VOA.
`extraPlusIsometry_form` gives a form-preserving normalization, still intertwining all modes.
The scalar roots are chosen individually; no coherent group action of these normalized lifts
or extension to the Moonshine VOA is claimed here.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA IntegralLattice LatGen LatticeTwisted TwistedHeisenberg TwistedReduction
open HeisenbergN MvPolynomial
open Module (End)
open scoped TensorProduct

/-- The pairing with `μ`, reduced modulo two. -/
def extraPairChar (L : IntegralLattice) (μ : L.carrier) : L.carrier →+ ZMod 2 :=
  (Int.castAddHom (ZMod 2)).comp (L.form μ).toAddMonoidHom

theorem extraPairChar_sign (L : IntegralLattice) (μ α : L.carrier) :
    chiSign L (extraPairChar L μ) α = (-1 : ℂ) ^ (L.form μ α) := by
  exact (Extraspecial.neg_one_zpow_eq_sgn _).symm

section Lattice

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (μ : L.carrier)

/-- The extraspecial charge operator, acting trivially on oscillators. -/
def extraPhi (r : ℕ) : End ℂ (FockT r ⊗[ℂ] ExtraT L hEven hU) :=
  (eT L hEven hU μ).lTensor (FockT r)

theorem extraPhi_tmul (r : ℕ) (p : FockT r) (t : ExtraT L hEven hU) :
    extraPhi L hEven hU μ r (p ⊗ₜ t) = p ⊗ₜ eT L hEven hU μ t :=
  LinearMap.lTensor_tmul _ _ _ _

theorem extraPhi_sq (r : ℕ) (x : FockT r ⊗[ℂ] ExtraT L hEven hU) :
    extraPhi L hEven hU μ r (extraPhi L hEven hU μ r x)
      = latticeCocycle L μ μ • x := by
  have h : extraPhi L hEven hU μ r * extraPhi L hEven hU μ r
      = latticeCocycle L μ μ • (1 : End ℂ _) := by
    rw [extraPhi, ← LinearMap.lTensor_mul, eT_mul_self', LinearMap.lTensor_smul]
    congr 1
    exact LinearMap.lTensor_id _ _
  exact LinearMap.congr_fun h x

theorem extraPhi_YTL (α : L.carrier) (k : ℤ)
    (x : FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :
    extraPhi L hEven hU μ (rank L) (YTL L hEven hU α k x)
      = chiSign L (extraPairChar L μ) α •
        YTL L hEven hU α k (extraPhi L hEven hU μ (rank L) x) := by
  have hc (t : ExtraT L hEven hU) :
      eT L hEven hU μ (eT L hEven hU α t)
        = chiSign L (extraPairChar L μ) α • eT L hEven hU α (eT L hEven hU μ t) := by
    rw [extraPairChar_sign]
    exact LinearMap.congr_fun (eT_comm_sign' L hEven hU μ α) t
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | tmul p t =>
    simp only [YTL, YTg_tmul, extraPhi_tmul, map_smul, hc, TensorProduct.tmul_smul]
    exact smul_comm _ _ _

/-- An auxiliary involution used only to transport the field products. -/
def extraConj : End ℂ (FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :=
  sqrtEpsL L μ • extraPhi L hEven hU μ (rank L)

theorem extraConj_sq (x : FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :
    extraConj L hEven hU μ (extraConj L hEven hU μ x) = x := by
  simp only [extraConj, LinearMap.smul_apply, map_smul]
  rw [extraPhi_sq, smul_smul, smul_smul, sqrtEpsL_mul_self,
    latticeCocycle_sq, one_smul]

theorem extraConj_YTL (α : L.carrier) (k : ℤ)
    (x : FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :
    extraConj L hEven hU μ (YTL L hEven hU α k (extraConj L hEven hU μ x))
      = chiSign L (extraPairChar L μ) α • YTL L hEven hU α k x := by
  have h (y) : extraConj L hEven hU μ (YTL L hEven hU α k y)
      = chiSign L (extraPairChar L μ) α • YTL L hEven hU α k
        (extraConj L hEven hU μ y) := by
    simp only [extraConj, LinearMap.smul_apply, extraPhi_YTL, map_smul]
    exact smul_comm _ _ _
  rw [h, extraConj_sq]

theorem extraConj_modeTT (a : Fin (rank L)) (k : ℤ)
    (x : FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :
    extraConj L hEven hU μ (modeTT a k (extraConj L hEven hU μ x)) = modeTT a k x := by
  have h (y) : extraConj L hEven hU μ (modeTT a k y)
      = modeTT a k (extraConj L hEven hU μ y) := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul p t =>
      simp only [extraConj, LinearMap.smul_apply, modeTT, LinearMap.rTensor_tmul,
        extraPhi_tmul, map_smul]
  rw [h, extraConj_sq]

theorem extraConj_FgT (a : Fin (rank L)) :
    conjF (extraConj L hEven hU μ) (FgT a) = FgT a := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF, LinearMap.comp_apply, LinearMap.comp_apply, FgT_val, FgenT, mode_resc]
  exact extraConj_modeTT L hEven hU μ a _ x

theorem extraConj_YTLFld (α : L.carrier) (e : ℤ) :
    conjF (extraConj L hEven hU μ) (YTLFld L hEven hU α e)
      = chiSign L (extraPairChar L μ) α • YTLFld L hEven hU α e := by
  apply fld_ext_mode
  intro n x
  rw [mode_conjF, LinearMap.comp_apply, LinearMap.comp_apply, Fld.smul_val, mode_smul]
  change extraConj L hEven hU μ (mode (resc (YTL L hEven hU α) 2 e) n
    (extraConj L hEven hU μ x)) =
      chiSign L (extraPairChar L μ) α • mode (resc (YTL L hEven hU α) 2 e) n x
  simp only [mode_resc]
  exact extraConj_YTL L hEven hU μ α _ x

variable (hPos : L.PosDef)

include hPos

theorem extraConj_Fw (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    conjF (extraConj L hEven hU μ) (Fw L hEven hU α l e)
      = chiSign L (extraPairChar L μ) α • Fw L hEven hU α l e := by
  induction l generalizing e with
  | nil => exact extraConj_YTLFld L hEven hU μ α e
  | cons c l ih =>
    rw [Fw_cons, ← star_conjF (extraConj_sq L hEven hU μ)
      (tloc L hEven hU hPos (FgT_mem L hEven hU c.2) (Fw_mem L hEven hU hPos α l _)),
      extraConj_FgT, ih, star_smul_right
      (tloc L hEven hU hPos (FgT_mem L hEven hU c.2) (Fw_mem L hEven hU hPos α l _))]

theorem extraConj_FL (e : ℤ) (u : LatModuleGen L) :
    conjF (extraConj L hEven hU μ) (FL L hEven hU e u)
      = FL L hEven hU e (chiLat L (extraPairChar L μ) u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, conjF_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, conjF_add, hx, hy]
  | tmul p g =>
    induction g using Finsupp.induction_linear with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, map_zero, conjF_zero]
    | add g h hg hh =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, conjF_add, hg, hh]
    | single α c =>
      have hc : (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α := by
        simp [eGen]
      rw [hc, TensorProduct.tmul_smul, map_smul, map_smul, map_smul, conjF_smul,
        chiLat_tmul, map_smul]
      congr 1
      induction p using MvPolynomial.induction_on' with
      | add p q hp hq =>
        rw [TensorProduct.add_tmul, map_add, conjF_add, hp, hq, smul_add]
      | monomial m a =>
        rw [eGen, FL_monomial, conjF_smul, extraConj_Fw L hEven hU μ hPos]
        exact smul_comm _ _ _

/-- All twisted modes intertwine the pairing-character automorphism. -/
theorem extraPhi_YML (u : LatModuleGen L) (k : ℤ)
    (x : FockT (rank L) ⊗[ℂ] ExtraT L hEven hU) :
    extraPhi L hEven hU μ (rank L) (YML L hEven hU u k x)
      = YML L hEven hU (chiLat L (extraPairChar L μ) u) k
        (extraPhi L hEven hU μ (rank L) x) := by
  have h := congrArg (fun A => mode (A : Fld _).1 0
      (extraConj L hEven hU μ x)) (extraConj_FL L hEven hU μ hPos k u)
  dsimp only at h
  rw [mode_conjF, LinearMap.comp_apply, LinearMap.comp_apply, extraConj_sq] at h
  change extraConj L hEven hU μ (YML L hEven hU u k x) =
    YML L hEven hU (chiLat L (extraPairChar L μ) u) k (extraConj L hEven hU μ x) at h
  simp only [extraConj, LinearMap.smul_apply, map_smul] at h
  have hn : sqrtEpsL L μ ≠ 0 := by
    intro hz
    have hs := sqrtEpsL_mul_self L μ
    rw [hz, zero_mul] at hs
    have he := latticeCocycle_sq L μ μ
    rw [← hs, zero_mul] at he
    exact zero_ne_one he
  exact (smul_right_injective _ hn) h

/-- The same statement after transporting the oscillator rank. -/
theorem extraPhi_cast_YM {r : ℕ} (hr : rank L = r) (u : LatModuleGen L) (k : ℤ)
    (x : FockT r ⊗[ℂ] ExtraT L hEven hU) :
    extraPhi L hEven hU μ r
      ((hr ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2 (FockT r ⊗[ℂ] ExtraT L hEven hU)).YM u k x)
      = (hr ▸ latticeTwistedModule L hEven hU hPos :
        TwistedModule (thetaAut L hEven hPos) 2 (FockT r ⊗[ℂ] ExtraT L hEven hU)).YM
        (chiLat L (extraPairChar L μ) u) k (extraPhi L hEven hU μ r x) := by
  subst hr
  exact extraPhi_YML L hEven hU μ hPos u k x

end Lattice

section Leech

open TwistedSector InvForm

variable (μ : leech.carrier)

/-- The pairing-character automorphism of the Leech lattice VOA. -/
def extraLeechAut : Aut leechVOA :=
  chiAut leech (extraPairChar leech μ) leech_even leech_posDef

theorem extraLeechAut_theta (u : LatModuleGen leech) :
    extraLeechAut μ (thetaLat leech u) = thetaLat leech (extraLeechAut μ u) :=
  chiLat_thetaLat leech (extraPairChar leech μ) u

/-- Its restriction to the fixed lattice VOA. -/
def extraLeechPlusAut : Aut leechVOAPlus :=
  leechPlusAutOfTheta (extraLeechAut μ) (extraLeechAut_theta μ)

/-- The unnormalized extraspecial operator on the Leech twisted sector. -/
def extraLeechPhi : End ℂ Tw :=
  extraPhi leech leech_even leech_isUnit_det_gramMat μ 24

theorem extraLeechPhi_YM (u : LatModuleGen leech) (k : ℤ) (x : Tw) :
    extraLeechPhi μ (leechTwistedModule.YM u k x)
      = leechTwistedModule.YM (extraLeechAut μ u) k (extraLeechPhi μ x) :=
  extraPhi_cast_YM leech leech_even leech_isUnit_det_gramMat μ leech_posDef leech_rank u k x

theorem extraLeechPhi_theta (x : Tw) :
    extraLeechPhi μ (thetaTwLeech x) = thetaTwLeech (extraLeechPhi μ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul p t =>
    change extraPhi leech leech_even leech_isUnit_det_gramMat μ 24
      (twTheta 24 leechT (p ⊗ₜ t)) = _
    simp only [extraLeechPhi, extraPhi_tmul, twTheta_tmul, map_neg]

theorem extraLeechPhi_mem_TP {x : Tw} (hx : x ∈ TP) : extraLeechPhi μ x ∈ TP := by
  rw [TP_eq_twFixed, mem_twFixed] at hx ⊢
  rw [← extraLeechPhi_theta, hx]

/-- Restriction of the charge operator to the plus twisted module. -/
def extraPlusPhi : End ℂ TP where
  toFun x := ⟨extraLeechPhi μ x, extraLeechPhi_mem_TP μ x.property⟩
  map_add' x y := Subtype.ext (map_add (extraLeechPhi μ) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (extraLeechPhi μ) c x.val)

@[simp] theorem extraPlusPhi_coe (x : TP) :
    (extraPlusPhi μ x : Tw) = extraLeechPhi μ x := rfl

/-- The requested intertwining on the ordinary plus module, for every state and mode. -/
theorem extraPlusPhi_mode (u : (orbifold (Subgroup.zpowers leechTheta)).carrier)
    (n : ℤ) (x : TP) :
    extraPlusPhi μ (mode (plusModule.YM u) n x)
      = mode (plusModule.YM (extraLeechPlusAut μ u)) n (extraPlusPhi μ x) := by
  apply Subtype.ext
  simp only [extraPlusPhi_coe, mode_plusModule]
  exact extraLeechPhi_YM μ u.val (2 * n) x.val

theorem extraPlusPhi_sq (x : TP) :
    extraPlusPhi μ (extraPlusPhi μ x) = latticeCocycle leech μ μ • x := by
  apply Subtype.ext
  exact extraPhi_sq leech leech_even leech_isUnit_det_gramMat μ 24 x.val

/-- The plus charge operator is invertible, with inverse `ε(μ,μ)` times itself. -/
def extraPlusEquiv : TP ≃ₗ[ℂ] TP :=
  LinearEquiv.ofLinear (extraPlusPhi μ) (latticeCocycle leech μ μ • extraPlusPhi μ)
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, LinearMap.id_apply]
      rw [extraPlusPhi_sq, smul_smul, latticeCocycle_sq, one_smul])
    (LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
      rw [extraPlusPhi_sq, smul_smul, latticeCocycle_sq, one_smul])

/-- The exact multiplier of the unnormalized charge action on the twisted form. -/
theorem extraLeechPhi_form (x y : Tw) :
    leechTwForm (extraLeechPhi μ x) (extraLeechPhi μ y)
      = ((-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ) * leechTwForm x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, mul_add]
  | tmul p t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz, mul_add]
    | tmul q s =>
      change twForm 24 TFormLeech.TForm
        (extraPhi leech leech_even leech_isUnit_det_gramMat μ 24 (p ⊗ₜ t))
        (extraPhi leech leech_even leech_isUnit_det_gramMat μ 24 (q ⊗ₜ s)) = _
      rw [extraPhi_tmul, extraPhi_tmul, twForm_tmul, TFormLeech.TForm_eT_eT]
      exact mul_assoc _ _ _

/-- The same multiplier on `TPForm`; raw `eT μ` need not be an isometry. -/
theorem extraPlusPhi_form (x y : TP) :
    TPForm (extraPlusPhi μ x) (extraPlusPhi μ y)
      = ((-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ) * TPForm x y :=
  extraLeechPhi_form μ x.val y.val

/-- The form multiplier is a sign, hence its own inverse. -/
theorem extraPlusFormFactor_sq :
    ((-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ) *
      ((-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ) = 1 := by
  rw [mul_mul_mul_comm, latticeCocycle_sq, mul_one, ← mul_zpow, neg_one_mul, neg_neg,
    one_zpow]

/-- A scalar correction making the individual charge operator preserve `TPForm`. -/
def extraPlusFormScalar : ℂ :=
  (IsAlgClosed.exists_eq_mul_self
    ((-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ)).choose

theorem extraPlusFormScalar_sq :
    extraPlusFormScalar μ * extraPlusFormScalar μ
      = (-1 : ℂ) ^ (leech.form μ μ / 2) * latticeCocycle leech μ μ :=
  (IsAlgClosed.exists_eq_mul_self _).choose_spec.symm

theorem extraPlusFormScalar_ne_zero : extraPlusFormScalar μ ≠ 0 := by
  intro h
  have hs := extraPlusFormScalar_sq μ
  rw [h, zero_mul] at hs
  have hf := extraPlusFormFactor_sq μ
  rw [← hs, zero_mul] at hf
  exact zero_ne_one hf

/-- A form-preserving normalization of the individual plus charge operator. -/
def extraPlusIsometry : End ℂ TP := extraPlusFormScalar μ • extraPlusPhi μ

theorem extraPlusIsometry_mode (u : (orbifold (Subgroup.zpowers leechTheta)).carrier)
    (n : ℤ) (x : TP) :
    extraPlusIsometry μ (mode (plusModule.YM u) n x)
      = mode (plusModule.YM (extraLeechPlusAut μ u)) n (extraPlusIsometry μ x) := by
  simp only [extraPlusIsometry, LinearMap.smul_apply, extraPlusPhi_mode, map_smul]

theorem extraPlusIsometry_form (x y : TP) :
    TPForm (extraPlusIsometry μ x) (extraPlusIsometry μ y) = TPForm x y := by
  simp only [extraPlusIsometry, LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [extraPlusPhi_form, ← mul_assoc, ← mul_assoc, extraPlusFormScalar_sq,
    extraPlusFormFactor_sq, one_mul]

theorem extraPlusIsometry_bijective : Function.Bijective (extraPlusIsometry μ) := by
  have hs : Function.Bijective (fun x : TP => extraPlusFormScalar μ • x) := by
    constructor
    · exact smul_right_injective _ (extraPlusFormScalar_ne_zero μ)
    · intro x
      refine ⟨(extraPlusFormScalar μ)⁻¹ • x, ?_⟩
      dsimp only
      rw [smul_smul, mul_inv_cancel₀ (extraPlusFormScalar_ne_zero μ), one_smul]
  exact hs.comp (extraPlusEquiv μ).bijective

/-- The normalized action packaged as a linear equivalence. -/
def extraPlusIsometryEquiv : TP ≃ₗ[ℂ] TP :=
  LinearEquiv.ofBijective (extraPlusIsometry μ) (extraPlusIsometry_bijective μ)

end Leech

end VOA.Moonshine.ConwayNorton.M8
