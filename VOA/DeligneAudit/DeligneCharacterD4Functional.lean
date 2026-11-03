/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Ratio
import VOA.DeligneAudit.DeligneCharacterD4Theta

/-!
# The constant-term functionals of the D₄ kernel (layer 4)

`CT_x Θ(x) F(x)` and `CT_x Θ'(x) F(x)` on Laurent polynomials, with the explicit theta coefficients
`θ_{2k} = (-1)^k (q^{C(k,2)} + q^{C(k+1,2)})` and `θ'_{2k} = (-1)^k q^{C(k+1,2)}` (odd ones vanish),
here valued in `𝕜 = ℚ((q^{1/2}))`.

Coefficient laws (each an instance of `triC_succ`):
* `thK_eq` (`Θ = (1-x²)Θ'`): `θ_i = θ'_i - θ'_{i-2}`;
* `thpK_qshift` (`Θ'(qx) = q⁻³x⁻⁴Θ'(x)`): `θ'_{-j} = q^{j-3} θ'_{4-j}`;
* `thK_half` (`Θ(√q x) = Θ'(x)(1 - q⁻¹x⁻²)`): `θ_{-j} = r^j (θ'_{-j} - q⁻¹ θ'_{2-j})`;
* `thpK_inv` (`Θ'(x⁻¹) = -x²Θ'(x)`): `θ'_{-j} = -θ'_{j-2}`.
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4K

open PowerSeries

noncomputable section

/-- `(-1)^{|k|}` in `𝕜`. -/
def sgn (k : ℤ) : Kq := (-1) ^ k.natAbs

theorem sgn_add_one (k : ℤ) : sgn (k + 1) = -sgn k := neg_one_pow_natAbs_add_one k

theorem sgn_add_two (k : ℤ) : sgn (k + 2) = sgn k := by
  rw [show k + 2 = k + 1 + 1 by ring, sgn_add_one, sgn_add_one, neg_neg]

theorem sgn_neg (k : ℤ) : sgn (-k) = sgn k := by simp [sgn]

/-- `q^{C(k,2)}` in `𝕜`. -/
def qC (k : ℤ) : Kq := qq ^ (triC k : ℤ)

theorem qC_succ (k : ℤ) : qC (k + 1) = qC k * qq ^ k := by
  rw [qC, qC, triC_succ, zpow_add₀ qq_ne_zero]

theorem triC_neg (k : ℤ) : triC (-k) = triC (k + 1) := by
  unfold triC; congr 2; ring_nf

theorem qC_neg (k : ℤ) : qC (-k) = qC (k + 1) := by rw [qC, qC, triC_neg]

/-- `θ_{2k} = (-1)^k (q^{C(k,2)} + q^{C(k+1,2)})`. -/
def thK (i : ℤ) : Kq := if Even i then sgn (i / 2) * (qC (i / 2) + qC (i / 2 + 1)) else 0

/-- `θ'_{2k} = (-1)^k q^{C(k+1,2)}`. -/
def thpK (i : ℤ) : Kq := if Even i then sgn (i / 2) * qC (i / 2 + 1) else 0

theorem thK_even (k : ℤ) : thK (2 * k) = sgn k * (qC k + qC (k + 1)) := by
  rw [thK, if_pos (even_two_mul k), Int.mul_ediv_cancel_left _ two_ne_zero]

theorem thpK_even (k : ℤ) : thpK (2 * k) = sgn k * qC (k + 1) := by
  rw [thpK, if_pos (even_two_mul k), Int.mul_ediv_cancel_left _ two_ne_zero]

theorem thK_odd {i : ℤ} (h : ¬ Even i) : thK i = 0 := by rw [thK, if_neg h]

theorem thpK_odd {i : ℤ} (h : ¬ Even i) : thpK i = 0 := by rw [thpK, if_neg h]

/-- `Θ = (1-x²)Θ'`. -/
theorem thK_eq (i : ℤ) : thK i = thpK i - thpK (i - 2) := by
  rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
  · rw [thK_even, thpK_even, show 2 * k - 2 = 2 * (k - 1) by ring, thpK_even,
      show k - 1 + 1 = k by ring]
    have := sgn_add_one (k - 1)
    rw [show k - 1 + 1 = k by ring] at this
    rw [this]; ring
  · have h1 : ¬ Even (2 * k + 1) := by rw [Int.not_even_iff_odd]; exact odd_two_mul_add_one k
    have h2 : ¬ Even (2 * k + 1 - 2) := by
      rw [Int.not_even_iff_odd, show 2 * k + 1 - 2 = 2 * (k - 1) + 1 by ring]
      exact odd_two_mul_add_one _
    rw [thK_odd h1, thpK_odd h1, thpK_odd h2, sub_zero]

/-- `Θ'(qx) = q⁻³x⁻⁴Θ'(x)`, coefficientwise. -/
theorem thpK_qshift (j : ℤ) : thpK (-j) = qq ^ (j - 3) * thpK (4 - j) := by
  rcases Int.even_or_odd' (-j) with ⟨k, hk | hk⟩
  · have hj : j = -(2 * k) := by omega
    subst hj
    rw [neg_neg, thpK_even, show 4 - -(2 * k) = 2 * (k + 2) by ring, thpK_even, sgn_add_two,
      show k + 2 + 1 = k + 1 + 1 + 1 by ring, qC_succ, qC_succ]
    rw [show -(2 * k) - 3 = -(k + 1) - (k + 2) by ring]
    rw [zpow_sub₀ qq_ne_zero, zpow_neg]
    have hq := qq_ne_zero
    field_simp
    rw [qC_succ, qC_succ]
    ring_nf
  · have h1 : ¬ Even (-j) := by rw [hk, Int.not_even_iff_odd]; exact odd_two_mul_add_one k
    have h2 : ¬ Even (4 - j) := by
      rw [Int.not_even_iff_odd, show 4 - j = 2 * (k + 2) + 1 by omega]
      exact odd_two_mul_add_one _
    rw [thpK_odd h1, thpK_odd h2, mul_zero]

theorem rr_zpow_two_mul (m : ℤ) : rr ^ (2 * m) = qq ^ m := by
  rw [qq_eq_rr_sq, ← zpow_natCast, ← zpow_mul]; norm_num

/-- `Θ(√q x) = Θ'(x)(1 - q⁻¹x⁻²)`, coefficientwise. -/
theorem thK_half (j : ℤ) : thK (-j) = rr ^ j * (thpK (-j) - qq⁻¹ * thpK (2 - j)) := by
  rcases Int.even_or_odd' (-j) with ⟨k, hk | hk⟩
  · have hj : j = 2 * (-k) := by omega
    rw [hk, hj, thK_even, thpK_even, show 2 - 2 * -k = 2 * (k + 1) by ring, thpK_even,
      sgn_add_one, rr_zpow_two_mul, show k + 1 + 1 = k + 1 + 1 from rfl, qC_succ (k + 1), qC_succ k]
    have hq := qq_ne_zero
    rw [zpow_neg]
    field_simp
    ring_nf
    rw [zpow_add₀ hq, zpow_one]
    ring
  · have h1 : ¬ Even (-j) := by rw [hk, Int.not_even_iff_odd]; exact odd_two_mul_add_one k
    have h2 : ¬ Even (2 - j) := by
      rw [Int.not_even_iff_odd, show 2 - j = 2 * (k + 1) + 1 by omega]
      exact odd_two_mul_add_one _
    rw [thK_odd h1, thpK_odd h1, thpK_odd h2]; ring

/-- `Θ'(x⁻¹) = -x²Θ'(x)`, coefficientwise. -/
theorem thpK_inv (j : ℤ) : thpK (-j) = -thpK (j - 2) := by
  rcases Int.even_or_odd' (-j) with ⟨k, hk | hk⟩
  · rw [hk, show j - 2 = 2 * (-k - 1) by omega, thpK_even, thpK_even,
      show -k - 1 + 1 = -k by ring, qC_neg, show -k - 1 = -(k + 1) by ring, sgn_neg, sgn_add_one]
    ring
  · have h1 : ¬ Even (-j) := by rw [hk, Int.not_even_iff_odd]; exact odd_two_mul_add_one k
    have h2 : ¬ Even (j - 2) := by
      rw [Int.not_even_iff_odd, show j - 2 = 2 * (-k - 2) + 1 by omega]
      exact odd_two_mul_add_one _
    rw [thpK_odd h1, thpK_odd h2, neg_zero]

/-- `θ₀ = 2`. -/
theorem thK_zero : thK 0 = 2 := by
  have := thK_even 0
  simp only [mul_zero] at this
  rw [this]
  simp [sgn, qC, triC]
  norm_num

/-! ## Domain maps -/

/-- The monoid hom `v ↦ z^{f v}`. -/
def domHomAux (f : V →+ V) : Multiplicative V →* R where
  toFun v := mon (f (Multiplicative.toAdd v)) 1
  map_one' := by simp [mon]; rfl
  map_mul' v w := by rw [mon_mul_mon, toAdd_mul, map_add, mul_one]

/-- `z^v ↦ z^{f v}`, an algebra endomorphism of `R`. -/
def domHom (f : V →+ V) : R →ₐ[Kq] R := AddMonoidAlgebra.lift Kq R V (domHomAux f)

theorem domHom_mon (f : V →+ V) (v : V) (c : Kq) : domHom f (mon v c) = mon (f v) c := by
  rw [domHom, mon, AddMonoidAlgebra.lift_single]
  simp only [domHomAux, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [mon, mon, AddMonoidAlgebra.smul_single', mul_one]

/-! ## The functionals -/

/-- Forget the `x`-exponent. -/
def killX (v : V) : V := Function.update v 0 0

/-- `F ↦ CT_x θ(x) F(x)` for a coefficient family `θf` (`x^j ↦ θf(-j)`). -/
def ctFun (θf : ℤ → Kq) : R →ₗ[Kq] R :=
  Finsupp.linearCombination Kq fun v => mon (killX v) (θf (-(v 0)))

theorem ctFun_mon (θf : ℤ → Kq) (v : V) (c : Kq) :
    ctFun θf (mon v c) = mon (killX v) (c * θf (-(v 0))) := by
  change (Finsupp.linearCombination Kq _) (Finsupp.single v c) = _
  rw [Finsupp.linearCombination_single, mon, AddMonoidAlgebra.smul_single', mul_comm]
  rfl

theorem mon_sub (v : V) (a b : Kq) : mon v a - mon v b = mon v (a - b) :=
  (Finsupp.single_sub v a b).symm

/-- `CT_x Θ F`. -/
abbrev ctTheta : R →ₗ[Kq] R := ctFun thK
/-- `CT_x Θ' F`. -/
abbrev ctThetaP : R →ₗ[Kq] R := ctFun thpK

theorem xv_zero : xv 0 = 1 := by simp [xv]

theorem killX_add_xv (v : V) (j : ℤ) : killX (v + j • xv) = killX v := by
  ext i; by_cases h : i = 0 <;> simp [killX, xv, h, Function.update]

theorem add_xv_zero (v : V) (j : ℤ) : (v + j • xv) 0 = v 0 + j := by simp [xv]

/-- `Θ = (1-x²)Θ'`. -/
theorem ctTheta_eq (f : R) : ctTheta f = ctThetaP ((1 - mon ((2 : ℤ) • xv) 1) * f) := by
  have : ctTheta = ctThetaP ∘ₗ LinearMap.mulLeft Kq (1 - mon ((2 : ℤ) • xv) 1) := by
    apply Finsupp.lhom_ext
    intro v c
    change ctTheta (mon v c) = ctThetaP ((1 - mon ((2 : ℤ) • xv) 1) * mon v c)
    rw [sub_mul, one_mul, mon_mul_mon, map_sub, ctFun_mon, ctFun_mon, ctFun_mon,
      show (2 : ℤ) • xv + v = v + (2 : ℤ) • xv by abel, killX_add_xv, add_xv_zero, one_mul,
      thK_eq, show -(v 0 + 2) = -v 0 - 2 by ring, mon_sub, mul_sub]
  rw [this]; rfl

/-- `Θ'(qx) = q⁻³x⁻⁴Θ'(x)`: `CT Θ' F = CT Θ' (q⁻³x⁻⁴ F(qx))`. -/
theorem ctThetaP_qshift (f : R) :
    ctThetaP f = ctThetaP (mon ((-4 : ℤ) • xv) (qq ^ (-3 : ℤ)) * twist chiX qq qq_ne_zero f) := by
  have : ctThetaP = ctThetaP ∘ₗ LinearMap.mulLeft Kq (mon ((-4 : ℤ) • xv) (qq ^ (-3 : ℤ))) ∘ₗ
      (twist chiX qq qq_ne_zero).toLinearMap := by
    apply Finsupp.lhom_ext
    intro v c
    change ctThetaP (mon v c) = ctThetaP (mon ((-4 : ℤ) • xv) (qq ^ (-3 : ℤ)) *
      twist chiX qq qq_ne_zero (mon v c))
    rw [twist_mon, mon_mul_mon, ctFun_mon, ctFun_mon,
      show (-4 : ℤ) • xv + v = v + (-4 : ℤ) • xv by abel, killX_add_xv, add_xv_zero,
      show chiX v = v 0 from rfl, thpK_qshift (v 0), show -(v 0 + -4) = 4 - v 0 by ring,
      show v 0 - 3 = -3 + v 0 by ring, zpow_add₀ qq_ne_zero]
    ring_nf
  conv_lhs => rw [this]
  rfl

/-- `Θ(√q x) = Θ'(x)(1 - q⁻¹x⁻²)`: `CT Θ F = CT Θ' ((1 - q⁻¹x⁻²) F(√q x))`. -/
theorem ctTheta_half (f : R) :
    ctTheta f = ctThetaP ((1 - mon ((-2 : ℤ) • xv) qq⁻¹) * twist chiX rr rr_ne_zero f) := by
  have : ctTheta = ctThetaP ∘ₗ LinearMap.mulLeft Kq (1 - mon ((-2 : ℤ) • xv) qq⁻¹) ∘ₗ
      (twist chiX rr rr_ne_zero).toLinearMap := by
    apply Finsupp.lhom_ext
    intro v c
    change ctTheta (mon v c) = ctThetaP ((1 - mon ((-2 : ℤ) • xv) qq⁻¹) *
      twist chiX rr rr_ne_zero (mon v c))
    rw [twist_mon, sub_mul, one_mul, mon_mul_mon, map_sub, ctFun_mon, ctFun_mon, ctFun_mon,
      show (-2 : ℤ) • xv + v = v + (-2 : ℤ) • xv by abel, killX_add_xv, add_xv_zero,
      show chiX v = v 0 from rfl, thK_half (v 0), show -(v 0 + -2) = 2 - v 0 by ring, mon_sub]
    ring_nf
  conv_lhs => rw [this]
  rfl

/-- Inversion of the `x`-exponent. -/
def negX : V →+ V where
  toFun v := v - (2 * v 0) • xv
  map_zero' := by simp
  map_add' v w := by simp only [Pi.add_apply, mul_add, add_smul]; abel

theorem killX_sub_xv (v : V) (j : ℤ) : killX (v - j • xv) = killX v := by
  rw [sub_eq_add_neg, ← neg_smul, killX_add_xv]

/-- `Θ'(x⁻¹) = -x²Θ'(x)`: `CT Θ' F = CT Θ' (-x² F(x⁻¹))`. -/
theorem ctThetaP_inv (f : R) :
    ctThetaP f = ctThetaP (mon ((2 : ℤ) • xv) (-1) * domHom negX f) := by
  have : ctThetaP = ctThetaP ∘ₗ LinearMap.mulLeft Kq (mon ((2 : ℤ) • xv) (-1)) ∘ₗ
      (domHom negX).toLinearMap := by
    apply Finsupp.lhom_ext
    intro v c
    change ctThetaP (mon v c) = ctThetaP (mon ((2 : ℤ) • xv) (-1) * domHom negX (mon v c))
    have h0 : (negX v + (2 : ℤ) • xv) 0 = -v 0 + 2 := by simp [negX, xv]; ring
    have hk : killX (negX v + (2 : ℤ) • xv) = killX v := by
      rw [killX_add_xv]; exact killX_sub_xv v _
    rw [domHom_mon, mon_mul_mon, ctFun_mon, ctFun_mon,
      show (2 : ℤ) • xv + negX v = negX v + (2 : ℤ) • xv by abel, hk, h0, thpK_inv (v 0),
      show -(-v 0 + 2) = v 0 - 2 by ring]
    ring_nf
  conv_lhs => rw [this]
  rfl

end

end VOA.DeligneAudit.DeligneCharacter.D4K

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ctTheta_eq
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ctThetaP_qshift
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ctTheta_half
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.ctThetaP_inv
#print axioms VOA.DeligneAudit.DeligneCharacter.D4K.thK_zero
end AxiomAudit
