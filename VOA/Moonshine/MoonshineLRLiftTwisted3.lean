import VOA.Moonshine.MoonshineLRLiftTwisted2

/-!
# Form normalization of the twisted lattice lift

The orthogonal oscillator change preserves the twisted Fock form. On the charge
space, the pulled-back form has the same adjoint operation on every endomorphism;
a rank-one argument proves scalar uniqueness. Nondegeneracy makes this scalar
nonzero. Tensoring, transporting to rank 24, and restricting to the theta-fixed
sector retain the multiplier. A square root of its inverse normalizes the lift,
giving `liftTwVnatAut` without any additional form hypothesis.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA IntegralLattice LatGen Extraspecial TwistedHeisenberg MvPolynomial
open InvForm TFormLeech
open scoped BigOperators TensorProduct Matrix

/-- Orthogonal oscillator changes preserve the constant coefficient. -/
theorem liftTwFockMap_constantCoeff {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)
    (p : FockT r) : constantCoeff (liftTwFockMap Q p) = constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [liftTwFockMap, fockMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    obtain ⟨m, a⟩ := v
    simp [map_mul, liftTwFockMap_X, map_sum, constantCoeff_X]

/-- The twisted Fock form is invariant under an orthogonal oscillator change. -/
theorem liftTwFockMap_form {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)
    (hQ : Qᵀ * Q = 1) (p q : FockT r) :
    fockForm s (liftTwFockMap Q p) (liftTwFockMap Q q) = fockForm r p q := by
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    rw [show (MvPolynomial.C c : FockT r) = c • 1 by rw [smul_eq_C_mul, mul_one], map_smul, map_one,
      map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      fockForm_one, fockForm_one, ← constantCoeff_eq, ← constantCoeff_eq,
      liftTwFockMap_constantCoeff]
  | add p p' hp hp' => simp only [map_add, LinearMap.add_apply, hp, hp']
  | mul_X p v hp =>
    obtain ⟨m, a⟩ := v
    rw [mul_comm p, map_mul, liftTwFockMap_X, Finset.sum_mul]
    simp only [smul_mul_assoc, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, fockForm_X_mul, smul_eq_mul]
    rw [show (∑ b : Fin s, Q b a * (cVar (m, b) *
        fockForm s (liftTwFockMap Q p) (pderiv (m, b) (liftTwFockMap Q q)))) =
      cVar (m, a) * fockForm s (liftTwFockMap Q p)
        (∑ b : Fin s, Q b a • pderiv (m, b) (liftTwFockMap Q q)) by
          simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, cVar]
          apply Finset.sum_congr rfl
          intro b _
          ring]
    rw [← liftTwFockMap_pderiv Q hQ, hp]

/-- Forms with the same adjoint operation on every endomorphism are proportional. -/
theorem liftTwForm_unique {T : Type*} [AddCommGroup T] [Module ℂ T] [Nontrivial T]
    (B D : LinearMap.BilinForm ℂ T) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (J : Module.End ℂ T →ₗ[ℂ] Module.End ℂ T)
    (hBJ : ∀ A x y, B (A x) y = B x (J A y))
    (hDJ : ∀ A x y, D (A x) y = D x (J A y)) :
    ∃ z : ℂ, ∀ x y, D x y = z * B x y := by
  obtain ⟨u, hu⟩ := exists_ne (0 : T)
  obtain ⟨v, huv⟩ : ∃ v, B u v ≠ 0 := by
    by_contra! h
    exact hu (hB.1 u h)
  refine ⟨D u v / B u v, fun x y => ?_⟩
  let A : Module.End ℂ T := (B v).smulRight x
  have hA : J A y = B x y • v := by
    apply sub_eq_zero.mp
    apply hB.2
    intro t
    rw [map_sub, ← hBJ, map_smul, smul_eq_mul]
    change B ((B v t) • x) y - B x y * B t v = 0
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs v t]
    ring
  have h := hDJ A u y
  rw [hA, map_smul, smul_eq_mul] at h
  change D (B v u • x) y = B x y * D u v at h
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hs v u] at h
  apply (mul_left_cancel₀ huv)
  calc
    B u v * D x y = B x y * D u v := h
    _ = B u v * (D u v / B u v * B x y) := by field_simp

section ChargeForm

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- Pull back the charge form by the chosen charge intertwiner. -/
def liftTwChargeForm : LinearMap.BilinForm ℂ TL :=
  TForm.compl₁₂ (liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι)
    (liftTwChargeEquiv leech ι leech_even leech_isUnit_det_gramMat hι)

/-- The pulled-back charge form has the original adjointness law. -/
theorem liftTwChargeForm_eT (α : leech.carrier) (x y : TL) :
    liftTwChargeForm ι hι (eT leech leech_even leech_isUnit_det_gramMat α x) y =
      (-1 : ℂ) ^ (leech.form α α / 2) *
        liftTwChargeForm ι hι x (eT leech leech_even leech_isUnit_det_gramMat α y) := by
  change TForm (liftTwChargeEquiv _ _ _ _ _ _) (liftTwChargeEquiv _ _ _ _ _ _) =
    _ * TForm (liftTwChargeEquiv _ _ _ _ _ _) (liftTwChargeEquiv _ _ _ _ _ _)
  rw [liftTwChargeEquiv_eT, liftTwChargeEquiv_eT, map_smul, LinearMap.smul_apply,
    map_smul, TForm_eT, hι, smul_eq_mul, smul_eq_mul]
  ring

/-- The adjointness law extends from charges to all endomorphisms. -/
theorem liftTwChargeForm_iota (A : Module.End ℂ TL) (x y : TL) :
    liftTwChargeForm ι hι (A x) y =
      liftTwChargeForm ι hι x (iotaL leech leech_even leech_isUnit_det_gramMat A y) := by
  let E := repEquiv (cocMat leech)
    (isUnit_det_cocMat leech leech_even leech_isUnit_det_gramMat)
  obtain ⟨a, rfl⟩ := E.surjective A
  have ha : a ∈ Submodule.span ℂ (Set.range (eA leech)) := by rw [span_eA]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨α, rfl⟩ := ha
    change liftTwChargeForm ι hι (eT leech leech_even leech_isUnit_det_gramMat α x) y =
      liftTwChargeForm ι hι x (iotaL leech leech_even leech_isUnit_det_gramMat
        (eT leech leech_even leech_isUnit_det_gramMat α) y)
    rw [iotaL_eT, LinearMap.smul_apply, map_smul, smul_eq_mul]
    exact liftTwChargeForm_eT ι hι α x y
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul c a _ ha =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ha]

/-- The charge intertwiner scales the charge form by a nonzero scalar. -/
theorem liftTwChargeForm_scalar :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x y, liftTwChargeForm ι hι x y = z * TForm x y := by
  obtain ⟨z, hz⟩ := liftTwForm_unique TForm (liftTwChargeForm ι hι)
    TForm_nondegenerate TForm_symm (iotaL leech leech_even leech_isUnit_det_gramMat)
    TForm_iota (liftTwChargeForm_iota ι hι)
  refine ⟨z, ?_, hz⟩
  intro hzero
  have hform : TForm = 0 := by
    ext x y
    obtain ⟨u, rfl⟩ := (liftTwChargeEquiv leech ι leech_even
      leech_isUnit_det_gramMat hι).surjective x
    obtain ⟨v, rfl⟩ := (liftTwChargeEquiv leech ι leech_even
      leech_isUnit_det_gramMat hι).surjective y
    have h := hz u v
    rw [hzero, zero_mul] at h
    exact h
  exact TForm_nondegenerate.ne_zero hform

end ChargeForm

/-- Tensoring with an orthogonal Fock change retains the charge form multiplier. -/
theorem liftTwTensorEquiv_form {r s : ℕ} (Q : Matrix (Fin s) (Fin r) ℂ)
    (hQ : Qᵀ * Q = 1) (hQ' : Q * Qᵀ = 1)
    {T : Type*} [AddCommGroup T] [Module ℂ T] (B : LinearMap.BilinForm ℂ T)
    (ρ : T ≃ₗ[ℂ] T) (z : ℂ) (hz : ∀ t u, B (ρ t) (ρ u) = z * B t u)
    (x y : FockT r ⊗[ℂ] T) :
    twForm s B (liftTwTensorEquiv Q hQ hQ' ρ x) (liftTwTensorEquiv Q hQ hQ' ρ y) =
      z * twForm r B x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul p t =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy', mul_add]
    | tmul q u =>
      rw [liftTwTensorEquiv_tmul, liftTwTensorEquiv_tmul, twForm_tmul, twForm_tmul,
        hz, liftTwFockMap_form Q hQ, mul_assoc]

/-- Form covariance survives transport of the oscillator rank. -/
theorem liftTwCastEquiv_form (L : IntegralLattice.{0}) (hEven : L.Even)
    (hU : IsUnit (gramMat L).det) (hPos : L.PosDef)
    (ι : L.carrier →ₗ[ℤ] L.carrier)
    (hι : ∀ α β, L.form (ι α) (ι β) = L.form α β)
    (B : LinearMap.BilinForm ℂ (ExtraT L hEven hU)) (z : ℂ)
    (hz : ∀ t u, B (liftTwChargeEquiv L ι hEven hU hι t)
      (liftTwChargeEquiv L ι hEven hU hι u) = z * B t u)
    {r : ℕ} (hr : rank L = r) (x y : FockT r ⊗[ℂ] ExtraT L hEven hU) :
    twForm r B (liftTwCastEquiv L hEven hU hPos ι hι hr x)
      (liftTwCastEquiv L hEven hU hPos ι hι hr y) = z * twForm r B x y := by
  subst hr
  exact liftTwTensorEquiv_form (oscMatrix L L ι)
    (oscMatrix_transpose_mul L L hPos hPos ι hι)
    (oscMatrix_mul_transpose L L hPos hPos ι hι rfl) B
    (liftTwChargeEquiv L ι hEven hU hι) z hz x y

section Normalization

open TwistedSector

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- The full twisted lift is a similitude with nonzero multiplier. -/
theorem liftTwLeechEquiv_formScalar :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ x y : Tw,
      leechTwForm (liftTwLeechEquiv ι hι x) (liftTwLeechEquiv ι hι y) =
        z * leechTwForm x y := by
  obtain ⟨z, hz, hform⟩ := liftTwChargeForm_scalar ι hι
  exact ⟨z, hz, liftTwCastEquiv_form leech leech_even leech_isUnit_det_gramMat
    leech_posDef ι hι TForm z hform leech_rank⟩

/-- Restrict the nonzero form multiplier to the theta-fixed twisted sector. -/
theorem liftTwPlusEquiv_formScalar :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ t u : TP,
      TPForm (liftTwPlusEquiv ι hι t) (liftTwPlusEquiv ι hι u) = z * TPForm t u := by
  obtain ⟨z, hz, hform⟩ := liftTwLeechEquiv_formScalar ι hι
  exact ⟨z, hz, fun t u => hform t.val u.val⟩

/-- A square root of the inverse multiplier normalizes the twisted lift. -/
theorem liftTwExists_formScalar : ∃ c : ℂˣ, ∀ t t' : TP,
    TPForm (liftTwNormalizedPlusEquiv ι hι c t)
      (liftTwNormalizedPlusEquiv ι hι c t') = TPForm t t' := by
  obtain ⟨z, hz, hform⟩ := liftTwPlusEquiv_formScalar ι hι
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_eq_mul_self z⁻¹
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact (inv_ne_zero hz) hc
  refine ⟨Units.mk0 c hc0, fun t u => ?_⟩
  simp only [liftTwNormalizedPlusEquiv_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Units.val_mk0, hform]
  rw [← mul_assoc, ← mul_assoc, ← hc, inv_mul_cancel₀ hz, one_mul]

/-- The unconditional twisted lattice lift to an automorphism of the Moonshine VOA. -/
def liftTwVnatAut (hsurj : Function.Surjective ι) : AutMonster.AutVnat :=
  liftTwVnatAutOfForm ι hι hsurj (liftTwExists_formScalar ι hι).choose
    (liftTwExists_formScalar ι hι).choose_spec

/-- The lift acts by the lattice automorphism and the normalized twisted equivalence. -/
@[simp] theorem liftTwVnatAut_apply (hsurj : Function.Surjective ι)
    (u : SkewVP) (t : TP) :
    liftTwVnatAut ι hι hsurj ((u, t) : Vnat) =
      (leechPlusLatMorphAut ι hι hsurj u,
        liftTwNormalizedPlusEquiv ι hι (liftTwExists_formScalar ι hι).choose t) := rfl

end Normalization

end VOA.Moonshine.ConwayNorton.M8
