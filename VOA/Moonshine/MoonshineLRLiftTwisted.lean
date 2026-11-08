import VOA.Moonshine.MoonshineLRLiftLattice
import VOA.Moonshine.MoonshineLRLiftNatural

/-!
# Orthogonal changes on the twisted Fock space

The twisted and untwisted Fock spaces have the same polynomial carrier. We reuse
`LatGen.fockMap`, but prove its compatibility with the half-integer Heisenberg modes.
Creation and annihilation exponentials, and their full dressing `DD`, are covariant.
Tensoring with a charge equivalence gives covariance of `YTL`, conditional on the
charge-intertwining equation. The tensor equivalence commutes with theta and restricts
to `liftTwLeechPlusEquiv : TP ≃ₗ[ℂ] TP` for any supplied charge equivalence.

The operators `liftTwChargeOp α = latCob α • eT (ι α)` obey the unit, cocycle, and
modulo-`2L` relations. What remains is to extend these operators to a simple algebra
module and use representation uniqueness to construct the charge intertwiner; then
extend `YTL` covariance to all `YML` by twisted word-field induction, transport the
native lattice rank to 24, and prove preservation of `TPForm` after normalization.
The candidate on `TP` is not yet proved to intertwine `plusModule`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA LatGen TwistedHeisenberg MvPolynomial
open scoped BigOperators TensorProduct Matrix

section Fock

variable {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)

/-- Change the oscillator frame at every half-integer creation level. -/
def liftTwFockMap : FockT r →ₐ[ℂ] FockT s := fockMap Q

@[simp] theorem liftTwFockMap_X (m : ℕ) (a : Fin r) :
    liftTwFockMap Q (X (m, a)) = ∑ b : Fin s, Q b a • X (m, b) :=
  fockMap_X Q m a

/-- An orthogonal frame change is invertible, with transpose as inverse. -/
def liftTwFockEquiv (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1) :
    FockT r ≃ₗ[ℂ] FockT s := fockEquiv Q hQ hQ'

@[simp] theorem liftTwFockEquiv_apply (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1)
    (p : FockT r) : liftTwFockEquiv Q hQ hQ' p = liftTwFockMap Q p := rfl

/-- Orthogonality converts the chain rule into covariance of the annihilators. -/
theorem liftTwFockMap_pderiv (hQ : Qᵀ * Q = 1) (m : ℕ) (a : Fin r)
    (p : FockT r) :
    liftTwFockMap Q (pderiv (m, a) p) =
      ∑ b : Fin s, Q b a • pderiv (m, b) (liftTwFockMap Q p) := by
  change fockMap Q (pderiv (m, a) p) = _
  simp only [liftTwFockMap, fockMap_pderiv, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hδ : ∀ a' : Fin r, ∑ b : Fin s, Q b a * Q b a' = if a = a' then 1 else 0 := by
    intro a'
    have h := congrFun (congrFun hQ a) a'
    simpa only [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h
  simp only [← Finset.sum_smul, hδ]
  simp

/-- Covariance of every twisted Heisenberg mode, including the zero even modes. -/
theorem liftTwFockMap_modeT (hQ : Qᵀ * Q = 1) (a : Fin r) (k : ℤ)
    (p : FockT r) :
    liftTwFockMap Q (modeT r a k p) =
      ∑ b : Fin s, Q b a • modeT s b k (liftTwFockMap Q p) := by
  by_cases he : k % 2 = 0
  · simp only [modeT_even _ _ he, LinearMap.zero_apply, map_zero, smul_zero,
      Finset.sum_const_zero]
  · have ho : Odd k := Int.odd_iff.mpr (by omega)
    by_cases hn : k < 0
    · simp only [modeT_apply_neg _ _ ho hn, varT, map_mul, liftTwFockMap_X,
        Finset.sum_mul, smul_mul_assoc]
    · have hp : 0 < k := by omega
      simp only [modeT_apply_pos _ _ ho hp, varT, map_smul,
        liftTwFockMap_pderiv Q hQ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => smul_comm _ _ _

/-- Covariance of a linear combination of half-integer oscillators. -/
theorem liftTwFockMap_oscT (hQ : Qᵀ * Q = 1) (u : Fin r → ℂ) (v : Fin s → ℂ)
    (huv : Q *ᵥ u = v) (k : ℤ) (p : FockT r) :
    liftTwFockMap Q (LatticeTwisted.oscT u k p) =
      LatticeTwisted.oscT v k (liftTwFockMap Q p) := by
  simp only [LatticeTwisted.oscT, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, liftTwFockMap_modeT Q hQ,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, ← huv, Matrix.mulVec, dotProduct]
  congr 1
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The rescaled twisted Heisenberg fields transform by the same matrix. -/
theorem liftTwFockMap_Fgen (hQ : Qᵀ * Q = 1) (a : Fin r) (n : ℤ)
    (p : FockT r) :
    liftTwFockMap Q (Fgen r a n p) =
      ∑ b : Fin s, Q b a • Fgen s b n (liftTwFockMap Q p) := by
  simp only [Fgen_apply]
  exact liftTwFockMap_modeT Q hQ a _ p

/-- Frame changes commute with the twisted Fock involution. -/
theorem liftTwFockMap_thetaT (p : FockT r) :
    liftTwFockMap Q (thetaT r p) = thetaT s (liftTwFockMap Q p) := by
  have h : (liftTwFockMap Q).comp (thetaT r).toAlgHom =
      (thetaT s).toAlgHom.comp (liftTwFockMap Q) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨m, a⟩ := v
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom,
      thetaT_X, map_neg, liftTwFockMap_X, map_sum, map_smul, smul_neg,
      Finset.sum_neg_distrib]
  exact congrArg (fun f : FockT r →ₐ[ℂ] FockT s => f p) h

end Fock

section Exponentials

open LatticeTwisted

variable {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)
  (u : Fin r → ℂ) (v : Fin s → ℂ) (huv : Q *ᵥ u = v)

include huv

/-- Covariance of the charge creation variables. -/
theorem liftTwFockMap_vVarT (m : ℕ) :
    liftTwFockMap Q (vVarT u m) = vVarT v m :=
  fockMap_Xcomb Q u v huv m

/-- Covariance of the logarithm of the creation exponential. -/
theorem liftTwFockMap_dM (k : ℕ) : liftTwFockMap Q (dM u k) = dM v k := by
  unfold dM
  split_ifs
  · rw [map_smul, liftTwFockMap_vVarT Q u v huv]
  · exact map_zero _

/-- Covariance of every coefficient of the creation exponential. -/
theorem liftTwFockMap_sM (p : ℕ) : liftTwFockMap Q (sM u p) = sM v p := by
  rw [sM, nexp_map]
  exact congrArg (fun d => nexp d p) (funext (liftTwFockMap_dM Q u v huv))

/-- The same covariance with integer coefficient indices. -/
theorem liftTwFockMap_sMz (p : ℤ) : liftTwFockMap Q (sMz u p) = sMz v p := by
  unfold sMz
  split_ifs
  · exact liftTwFockMap_sM Q u v huv _
  · exact map_zero _

/-- Orthogonality also transforms annihilation charges contragrediently. -/
theorem liftTwTranspose_charge (hQ : Qᵀ * Q = 1) : Qᵀ *ᵥ v = u := by
  rw [← huv, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]

/-- Covariance of the polynomial translation defining the annihilation exponential. -/
theorem liftTwFockMap_Ep (hQ : Qᵀ * Q = 1) (p : FockT r) :
    Polynomial.mapAlgHom (liftTwFockMap Q) (Ep u p) = Ep v (liftTwFockMap Q p) := by
  have h : (Polynomial.mapAlgHom (liftTwFockMap Q)).comp (Ep u) =
      (Ep v).comp (liftTwFockMap Q) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    obtain ⟨m, a⟩ := x
    have hc : ∑ b : Fin s, Q b a * v b = u a := by
      exact congrFun (liftTwTranspose_charge Q u v huv hQ) a
    simp only [AlgHom.comp_apply, Ep_X, map_sub, map_smul, map_pow,
      Polynomial.coe_mapAlgHom, Polynomial.map_C, Polynomial.map_X,
      liftTwFockMap_X, map_sum, Ep_X, smul_sub, Finset.sum_sub_distrib,
      smul_smul, ← Finset.sum_smul, hc]
    congr 1
    change Polynomial.C (liftTwFockMap Q (X (m, a))) = _
    simp only [liftTwFockMap_X, map_sum, Polynomial.smul_C]
  exact congrArg (fun f : FockT r →ₐ[ℂ] Polynomial (FockT s) => f p) h

/-- Covariance of each annihilation exponential coefficient. -/
theorem liftTwFockMap_EpC (hQ : Qᵀ * Q = 1) (q : ℕ) (p : FockT r) :
    liftTwFockMap Q (EpC u q p) = EpC v q (liftTwFockMap Q p) := by
  simpa only [Polynomial.coeff_mapAlgHom_apply, EpC_apply] using
    congrArg (fun f : Polynomial (FockT s) => f.coeff q)
      (liftTwFockMap_Ep Q u v huv hQ p)

/-- The full oscillator dressing of a twisted exponential is covariant. -/
theorem liftTwFockMap_DD (hQ : Qᵀ * Q = 1) (a : ℤ) (p : FockT r) :
    liftTwFockMap Q (DD u a p) = DD v a (liftTwFockMap Q p) := by
  obtain ⟨N, hN⟩ := EpC_eventually_zero u p
  have hN' : ∀ q, N ≤ q → EpC v q (liftTwFockMap Q p) = 0 := by
    intro q hq
    rw [← liftTwFockMap_EpC Q u v huv hQ, hN q hq, map_zero]
  rw [DD_apply_range u a p N hN, DD_apply_range v a _ N hN', map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, liftTwFockMap_sMz Q u v huv, liftTwFockMap_EpC Q u v huv hQ]

end Exponentials

section Tensor

open LatticeTwisted TwistedSector

variable {r s : ℕ} {T U : Type*} [AddCommGroup T] [Module ℂ T]
  [AddCommGroup U] [Module ℂ U]
  (Q : Matrix (Fin s) (Fin r) ℂ) (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1)
  (ρ : T ≃ₗ[ℂ] U)

/-- The candidate twisted lift, before imposing its charge-intertwining property. -/
def liftTwTensorEquiv : (FockT r ⊗[ℂ] T) ≃ₗ[ℂ] (FockT s ⊗[ℂ] U) :=
  TensorProduct.congr (liftTwFockEquiv Q hQ hQ') ρ

@[simp] theorem liftTwTensorEquiv_tmul (p : FockT r) (t : T) :
    liftTwTensorEquiv Q hQ hQ' ρ (p ⊗ₜ t) = liftTwFockMap Q p ⊗ₜ ρ t := rfl

/-- The candidate lift commutes with the FLM parity operator, for every `ρ`. -/
theorem liftTwTensorEquiv_theta (x : FockT r ⊗[ℂ] T) :
    liftTwTensorEquiv Q hQ hQ' ρ (twTheta r T x) =
      twTheta s U (liftTwTensorEquiv Q hQ hQ' ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p t =>
    simp only [twTheta_tmul, liftTwTensorEquiv_tmul, liftTwFockMap_thetaT, map_neg]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Twisted oscillator covariance on the tensor product. -/
theorem liftTwTensorEquiv_modeTT (a : Fin r) (k : ℤ) (x : FockT r ⊗[ℂ] T) :
    liftTwTensorEquiv Q hQ hQ' ρ (modeTT a k x) =
      ∑ b : Fin s, Q b a • modeTT b k (liftTwTensorEquiv Q hQ hQ' ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero, Finset.sum_const_zero]
  | tmul p t =>
    simp only [modeTT, LinearMap.rTensor_tmul, liftTwTensorEquiv_tmul,
      liftTwFockMap_modeT Q hQ, TensorProduct.sum_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy, smul_add, Finset.sum_add_distrib]

/-- Dressing covariance and a charge intertwiner give the twisted exponential fields. -/
theorem liftTwTensorEquiv_YTg (u : Fin r → ℂ) (v : Fin s → ℂ) (huv : Q *ᵥ u = v)
    (g : Module.End ℂ T) (g' : Module.End ℂ U) (c : ℂ)
    (hρ : ∀ t, ρ (g t) = c • g' (ρ t)) (c0 k : ℤ) (κ : ℂ)
    (x : FockT r ⊗[ℂ] T) :
    liftTwTensorEquiv Q hQ hQ' ρ (YTg u c0 κ g k x) =
      c • YTg v c0 κ g' k (liftTwTensorEquiv Q hQ hQ' ρ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul p t =>
    simp only [YTg_tmul, map_smul, liftTwTensorEquiv_tmul,
      liftTwFockMap_DD Q u v huv hQ, hρ, TensorProduct.tmul_smul]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- Restriction of the tensor equivalence to the theta-fixed subspaces. -/
def liftTwFixedEquiv : twFixed r T ≃ₗ[ℂ] twFixed s U where
  toFun x := ⟨liftTwTensorEquiv Q hQ hQ' ρ x,
    mem_twFixed.mpr (by
      rw [← liftTwTensorEquiv_theta, mem_twFixed.mp x.2])⟩
  invFun x := ⟨(liftTwTensorEquiv Q hQ hQ' ρ).symm x,
    mem_twFixed.mpr (by
      apply (liftTwTensorEquiv Q hQ hQ' ρ).injective
      rw [liftTwTensorEquiv_theta, LinearEquiv.apply_symm_apply,
        mem_twFixed.mp x.2])⟩
  left_inv x := Subtype.ext ((liftTwTensorEquiv Q hQ hQ' ρ).symm_apply_apply x)
  right_inv x := Subtype.ext ((liftTwTensorEquiv Q hQ hQ' ρ).apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add (liftTwTensorEquiv Q hQ hQ' ρ) x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (liftTwTensorEquiv Q hQ hQ' ρ) c x.val)

@[simp] theorem liftTwFixedEquiv_coe (x : twFixed r T) :
    (liftTwFixedEquiv Q hQ hQ' ρ x : FockT s ⊗[ℂ] U) =
      liftTwTensorEquiv Q hQ hQ' ρ x := rfl

end Tensor

section Charge

open IntegralLattice

variable (L : IntegralLattice) (ι : L.carrier →ₗ[ℤ] L.carrier)

/-- The coboundary used in the untwisted lift descends to `L / 2L`. -/
theorem liftTwLatCob_add_two (α β : L.carrier) :
    latCob L L ι (α + 2 • β) = latCob L L ι α := by
  let S := symForm (latticeBasis L) (cocDiff L L ι)
  have hS : S (α + 2 • β) (α + 2 • β) = S α α + 4 * (S α β + S β β) := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
      nsmul_eq_mul]
    rw [show S β α = S α β from symForm_comm _ _ β α]
    ring
  change Complex.I ^ (S (α + 2 • β) (α + 2 • β)) = Complex.I ^ (S α α)
  rw [hS, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  have hI : Complex.I ^ (4 : ℤ) = 1 := by
    exact_mod_cast Complex.I_pow_four
  rw [hI, one_zpow, mul_one]

variable (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)

/-- Pull back the charge operators with precisely the untwisted lift's coboundary. -/
def liftTwChargeOp (α : L.carrier) : Module.End ℂ (ExtraT L hEven hU) :=
  latCob L L ι α • eT L hEven hU (ι α)

theorem liftTwChargeOp_zero : liftTwChargeOp L ι hEven hU 0 = 1 := by
  rw [liftTwChargeOp, map_zero, latCob_zero, eT_zero, one_smul]

include hι in
/-- The pulled-back operators obey the original lattice cocycle multiplication law. -/
theorem liftTwChargeOp_mul (α β : L.carrier) :
    liftTwChargeOp L ι hEven hU α * liftTwChargeOp L ι hEven hU β =
      latticeCocycle L α β • liftTwChargeOp L ι hEven hU (α + β) := by
  simp only [liftTwChargeOp, smul_mul_smul_comm, eT_mul, smul_smul, ← map_add]
  congr 1
  calc latCob L L ι α * latCob L L ι β * latticeCocycle L (ι α) (ι β)
      = latticeCocycle L (ι α) (ι β) * (latCob L L ι α * latCob L L ι β) := by ring
    _ = _ := latticeCocycle_map_mul_latCob L L hEven hEven ι hι α β

/-- The pulled-back charge operators also factor through `L / 2L`. -/
theorem liftTwChargeOp_add_two (α β : L.carrier) :
    liftTwChargeOp L ι hEven hU (α + 2 • β) = liftTwChargeOp L ι hEven hU α := by
  rw [liftTwChargeOp, liftTwLatCob_add_two, map_add, map_nsmul,
    eT_add_two_nsmul, liftTwChargeOp]

end Charge

section Lattice

open IntegralLattice LatticeTwisted

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)
  (hPos : L.PosDef) (ι : L.carrier →ₗ[ℤ] L.carrier)
  (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)
  (ρ : ExtraT L hEven hU ≃ₗ[ℂ] ExtraT L hEven hU)

/-- The tensor candidate on the twisted module in the lattice's native rank indexing. -/
def liftTwLatticeTensorEquiv : MT L hEven hU ≃ₗ[ℂ] MT L hEven hU :=
  liftTwTensorEquiv (oscMatrix L L ι) (oscMatrix_transpose_mul L L hPos hPos ι hι)
    (oscMatrix_mul_transpose L L hPos hPos ι hι rfl) ρ

/-- Charge compatibility suffices for covariance on every exponential lattice generator. -/
theorem liftTwLatticeTensorEquiv_YTL
    (hρ : ∀ α t, ρ (eT L hEven hU α t) =
      latCob L L ι α • eT L hEven hU (ι α) (ρ t))
    (α : L.carrier) (k : ℤ) (x : MT L hEven hU) :
    liftTwLatticeTensorEquiv L hEven hU hPos ι hι ρ (YTL L hEven hU α k x) =
      latCob L L ι α • YTL L hEven hU (ι α) k
        (liftTwLatticeTensorEquiv L hEven hU hPos ι hι ρ x) := by
  unfold YTL
  rw [hι]
  exact liftTwTensorEquiv_YTg (oscMatrix L L ι)
    (oscMatrix_transpose_mul L L hPos hPos ι hι)
    (oscMatrix_mul_transpose L L hPos hPos ι hι rfl) ρ _ _
    (oscMatrix_chargeCoord L L hPos ι α) _ _ _ (hρ α) _ _ _ x

end Lattice

section Leech

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- The orthogonal frame matrix, reindexed by the concrete 24 oscillator directions. -/
def liftTwLeechMatrix : Matrix (Fin 24) (Fin 24) ℂ :=
  (oscMatrix leech leech ι).submatrix (finCongr leech_rank.symm) (finCongr leech_rank.symm)

include hι in
theorem liftTwLeechMatrix_transpose_mul :
    (liftTwLeechMatrix ι)ᵀ * liftTwLeechMatrix ι = 1 := by
  rw [liftTwLeechMatrix, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    oscMatrix_transpose_mul leech leech leech_posDef leech_posDef ι hι,
    Matrix.submatrix_one_equiv]

include hι in
theorem liftTwLeechMatrix_mul_transpose :
    liftTwLeechMatrix ι * (liftTwLeechMatrix ι)ᵀ = 1 := by
  rw [liftTwLeechMatrix, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
    oscMatrix_mul_transpose leech leech leech_posDef leech_posDef ι hι rfl,
    Matrix.submatrix_one_equiv]

/-- A candidate on `TP` for each choice of equivalence of the charge representation. -/
def liftTwLeechPlusEquiv (ρ : leechT ≃ₗ[ℂ] leechT) : TP ≃ₗ[ℂ] TP :=
  liftTwFixedEquiv (liftTwLeechMatrix ι) (liftTwLeechMatrix_transpose_mul ι hι)
    (liftTwLeechMatrix_mul_transpose ι hι) ρ

end Leech

end VOA.Moonshine.ConwayNorton.M8
