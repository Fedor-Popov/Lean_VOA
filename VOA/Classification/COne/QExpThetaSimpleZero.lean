import VOA.Classification.COne.QExpThetaLambert

/-! # A simple zero of the product at the origin -/

open Complex
open scoped UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

theorem thetaEulerProduct_ne_zero_of_norm_lt_one {r u : ℂ}
    (hr : ‖r‖ < 1) (hu : ‖u‖ < 1) : thetaEulerProduct r u ≠ 0 := by
  apply thetaEulerProduct_ne_zero hr
  intro n hn
  have hb : ‖u * r ^ n‖ < 1 := by
    rw [norm_mul, norm_pow]
    calc
      ‖u‖ * ‖r‖ ^ n ≤ ‖u‖ * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg r) hr.le) (norm_nonneg u)
      _ < 1 := by simpa using hu
  rw [hn, norm_one] at hb
  exact lt_irrefl _ hb

/-- Extracting the factor that vanishes at zero. -/
theorem thetaShiftedProduct_factor_origin (τ : ℍ) (x : ℂ) :
    thetaShiftedProduct x τ = (1 - thetaExp x) *
      (thetaEulerProduct (thetaExp τ) (thetaExp x * thetaExp τ) *
        thetaEulerProduct (thetaExp τ) (thetaExp ((τ : ℂ) - x))) := by
  unfold thetaShiftedProduct
  rw [thetaEulerProduct_shift (thetaExp_norm_lt_one τ.im_pos)]
  ring

/-- Explicit derivative at the origin. -/
theorem thetaShiftedProduct_hasDerivAt_zero (τ : ℍ) :
    HasDerivAt (fun x => thetaShiftedProduct x τ)
      (-(2 * Real.pi * I) * thetaEulerProduct (thetaExp τ) (thetaExp τ) ^ 2) 0 := by
  have hr := thetaExp_norm_lt_one τ.im_pos
  have hF := thetaEulerProduct_differentiable hr
  have hE : Differentiable ℂ thetaExp := fun x => (thetaExp_hasDerivAt x).differentiableAt
  have hrest : Differentiable ℂ (fun x =>
      thetaEulerProduct (thetaExp τ) (thetaExp x * thetaExp τ) *
        thetaEulerProduct (thetaExp τ) (thetaExp ((τ : ℂ) - x))) :=
    (hF.comp (hE.mul_const _)).mul
      (hF.comp (hE.comp ((differentiable_const (τ : ℂ)).sub differentiable_id)))
  have h := ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (thetaExp_hasDerivAt 0)).mul
    (hrest 0).hasDerivAt
  have heq : (fun x => thetaShiftedProduct x τ) = (fun x => (1 - thetaExp x) *
      (thetaEulerProduct (thetaExp τ) (thetaExp x * thetaExp τ) *
        thetaEulerProduct (thetaExp τ) (thetaExp ((τ : ℂ) - x)))) :=
    funext (thetaShiftedProduct_factor_origin τ)
  rw [heq]
  convert h using 1
  simp [thetaExp, pow_two, mul_assoc]

/-- In particular the lattice zero at zero is simple. -/
theorem thetaShiftedProduct_deriv_zero_ne_zero (τ : ℍ) :
    _root_.deriv (fun x => thetaShiftedProduct x τ) 0 ≠ 0 := by
  rw [(thetaShiftedProduct_hasDerivAt_zero τ).deriv]
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
  · exact pow_ne_zero _ (thetaEulerProduct_ne_zero_of_norm_lt_one
      (thetaExp_norm_lt_one τ.im_pos) (thetaExp_norm_lt_one τ.im_pos))

/-- Theta vanishes at every translate of its half-period zero. -/
theorem theta_lattice_zero (τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ ((m : ℂ) + (k : ℂ) * τ - (τ + 1) / 2) τ = 0 := by
  have h1 : Function.Periodic (fun z => jacobiTheta₂ z τ = 0) (1 : ℂ) := by
    intro z
    dsimp only
    rw [jacobiTheta₂_add_left]
  have ht : Function.Periodic (fun z => jacobiTheta₂ z τ = 0) τ := by
    intro z
    dsimp only
    rw [jacobiTheta₂_add_left', mul_eq_zero]
    simp only [Complex.exp_ne_zero, false_or]
  have hb : jacobiTheta₂ (-(τ + 1) / 2) τ = 0 := by
    rw [neg_div, jacobiTheta₂_neg_left, theta_halfPeriod_zero]
  have hm := h1.int_mul m ((k : ℂ) * τ - (τ + 1) / 2)
  have hk := ht.int_mul k (-(τ + 1) / 2)
  simp only [mul_one] at hm
  rw [show (m : ℂ) + k * τ - (τ + 1) / 2 =
    ((k : ℂ) * τ - (τ + 1) / 2) + m by ring, hm]
  rw [show (k : ℂ) * τ - (τ + 1) / 2 = -(τ + 1) / 2 + k * τ by ring, hk]
  exact hb

/-- Derivatives inherit the ordinary period. -/
theorem thetaShiftedProduct_deriv_add_one (τ : ℍ) (x : ℂ) :
    _root_.deriv (fun y => thetaShiftedProduct y τ) (x + 1) =
      _root_.deriv (fun y => thetaShiftedProduct y τ) x := by
  have hd := ((thetaShiftedProduct_differentiable τ) (x + 1)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const 1)
  have he : (fun y => thetaShiftedProduct (y + 1) τ) =
      (fun y => thetaShiftedProduct y τ) := funext (fun y => thetaShiftedProduct_add_one y τ)
  simpa only [Function.comp_def, id_eq, mul_one, he] using hd.deriv.symm

/-- At a zero, the extra term in the differentiated quasi-period law vanishes. -/
theorem thetaShiftedProduct_deriv_add_tau_of_zero (τ : ℍ) (x : ℂ)
    (hx : thetaShiftedProduct x τ = 0) :
    _root_.deriv (fun y => thetaShiftedProduct y τ) (x + τ) =
      -(thetaExp x)⁻¹ * _root_.deriv (fun y => thetaShiftedProduct y τ) x := by
  have hE : Differentiable ℂ (fun y : ℂ => -(thetaExp y)⁻¹) := by
    have h : Differentiable ℂ thetaExp := fun y => (thetaExp_hasDerivAt y).differentiableAt
    exact (h.inv thetaExp_ne_zero).neg
  have hleft := ((thetaShiftedProduct_differentiable τ) (x + τ)).hasDerivAt.comp x
    ((hasDerivAt_id x).add_const (τ : ℂ))
  have hright := (hE x).hasDerivAt.mul ((thetaShiftedProduct_differentiable τ) x).hasDerivAt
  have he : (fun y => thetaShiftedProduct (y + τ) τ) =
      (fun y => -(thetaExp y)⁻¹ * thetaShiftedProduct y τ) :=
    funext (fun y => thetaShiftedProduct_add_tau y τ)
  have hleft' : HasDerivAt (fun y => -(thetaExp y)⁻¹ * thetaShiftedProduct y τ)
      (_root_.deriv (fun y => thetaShiftedProduct y τ) (x + τ)) x := by
    simpa only [Function.comp_def, id_eq, mul_one, he] using hleft
  simpa only [hx, mul_zero, zero_add] using hleft'.unique hright

/-- Every zero of the product is simple. -/
theorem thetaShiftedProduct_deriv_ne_zero_of_zero (τ : ℍ) (x : ℂ)
    (hx : thetaShiftedProduct x τ = 0) :
    _root_.deriv (fun y => thetaShiftedProduct y τ) x ≠ 0 := by
  let H := fun x : ℂ => thetaShiftedProduct x τ = 0 ∧
    _root_.deriv (fun y => thetaShiftedProduct y τ) x ≠ 0
  have h1 : Function.Periodic H 1 := by
    intro y
    dsimp [H]
    rw [thetaShiftedProduct_add_one, thetaShiftedProduct_deriv_add_one]
  have ht : Function.Periodic H (τ : ℂ) := by
    intro y
    apply propext
    dsimp [H]
    have hc : -(thetaExp y)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (thetaExp_ne_zero y))
    have hz : thetaShiftedProduct (y + τ) τ = 0 ↔ thetaShiftedProduct y τ = 0 := by
      rw [thetaShiftedProduct_add_tau, mul_eq_zero]
      simp only [hc, false_or]
    constructor
    · rintro ⟨hz', hd⟩
      have hy := hz.mp hz'
      rw [thetaShiftedProduct_deriv_add_tau_of_zero τ y hy] at hd
      exact ⟨hy, (mul_ne_zero_iff.mp hd).2⟩
    · rintro ⟨hy, hd⟩
      refine ⟨hz.mpr hy, ?_⟩
      rw [thetaShiftedProduct_deriv_add_tau_of_zero τ y hy]
      exact mul_ne_zero hc hd
  obtain ⟨m, k, rfl⟩ := (thetaShiftedProduct_eq_zero_iff τ x).mp hx
  have h0 : H 0 := ⟨by simpa using thetaShiftedProduct_lattice_zero (τ : ℂ) 0 0,
    thetaShiftedProduct_deriv_zero_ne_zero τ⟩
  have hp := (h1.int_mul m).add_period (ht.int_mul k)
  have hh := hp.eq
  simp only [mul_one] at hh
  have hh0 : H ((m : ℂ) + (k : ℂ) * τ) := hh.mpr h0
  exact hh0.2

end VOA.Classification.COne.SSHecke
