import VOA.Classification.COne.QExpWeightTwoTheta
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Convergent products for the theta comparison

The Euler product here omits the factor independent of the elliptic variable.
All product results in this file are unconditional. No identification with the
Jacobi theta series is assumed or asserted here.
-/

open Complex Filter
open scoped Topology UpperHalfPlane

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- Euler's product, with its zeroth factor included. -/
def thetaEulerProduct (r u : ℂ) : ℂ := ∏' n : ℕ, (1 - u * r ^ n)

theorem thetaEulerProduct_summable {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    Summable (fun n : ℕ => ‖-(u * r ^ n)‖) := by
  simpa only [norm_neg, norm_mul, norm_pow] using
    (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left ‖u‖

theorem thetaEulerProduct_multipliable {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    Multipliable (fun n : ℕ => 1 - u * r ^ n) := by
  simpa only [sub_eq_add_neg] using
    multipliable_one_add_of_summable (thetaEulerProduct_summable hr u)

theorem thetaEulerProduct_ne_zero {r u : ℂ} (hr : ‖r‖ < 1)
    (hu : ∀ n : ℕ, u * r ^ n ≠ 1) : thetaEulerProduct r u ≠ 0 := by
  apply tprod_one_add_ne_zero_of_summable (f := fun n => -(u * r ^ n))
    (fun n => by
      change 1 - u * r ^ n ≠ 0
      exact sub_ne_zero.mpr (Ne.symm (hu n)))
    (thetaEulerProduct_summable hr u)

/-- Removing the first factor does not require any factors to be nonzero. -/
theorem thetaEulerProduct_shift {r : ℂ} (hr : ‖r‖ < 1) (u : ℂ) :
    thetaEulerProduct r u = (1 - u) * thetaEulerProduct r (u * r) := by
  have he (n : ℕ) : 1 - u * r ^ (n + 1) = 1 - (u * r) * r ^ n := by
    rw [pow_succ]
    ring
  have hs : Multipliable (fun n : ℕ => 1 - u * r ^ (n + 1)) := by
    simp_rw [he]
    exact thetaEulerProduct_multipliable hr (u * r)
  have ht := tprod_eq_zero_mul' (f := fun n : ℕ => 1 - u * r ^ n) hs
  simpa only [he, pow_zero, mul_one, thetaEulerProduct] using ht

/-- Locally uniform convergence on the entire elliptic parameter plane. -/
theorem thetaEulerProduct_hasProdLocallyUniformlyOn {r : ℂ} (hr : ‖r‖ < 1) :
    HasProdLocallyUniformlyOn (fun n (u : ℂ) => 1 - u * r ^ n)
      (thetaEulerProduct r) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  have hs := (summable_geometric_of_lt_one (norm_nonneg r) hr).mul_left M
  simpa only [thetaEulerProduct, sub_eq_add_neg] using
    hs.hasProdUniformlyOn_one_add hK
      (f := fun n (u : ℂ) => -(u * r ^ n))
      (Eventually.of_forall (fun n u hu => by
        simpa only [norm_neg, norm_mul, norm_pow] using
          mul_le_mul_of_nonneg_right (hM u hu) (pow_nonneg (norm_nonneg r) n)))
      (fun n => (continuous_id.mul continuous_const).neg.continuousOn)

/-- The product is entire in its second argument. -/
theorem thetaEulerProduct_differentiable {r : ℂ} (hr : ‖r‖ < 1) :
    Differentiable ℂ (thetaEulerProduct r) := by
  rw [← differentiableOn_univ]
  apply (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
    (thetaEulerProduct_hasProdLocallyUniformlyOn hr)).differentiableOn
  · exact Eventually.of_forall (fun s =>
      (Differentiable.fun_finsetProd (fun n _ =>
        (differentiable_const (1 : ℂ)).sub (differentiable_id.mul_const (r ^ n)))).differentiableOn)
  · exact isOpen_univ

/-- Exponential with period one. -/
def thetaExp (z : ℂ) : ℂ := cexp (2 * Real.pi * I * z)

theorem thetaExp_add (z w : ℂ) : thetaExp (z + w) = thetaExp z * thetaExp w := by
  simp [thetaExp, mul_add, Complex.exp_add]

theorem thetaExp_ne_zero (z : ℂ) : thetaExp z ≠ 0 := Complex.exp_ne_zero _

theorem thetaExp_nat_mul (n : ℕ) (z : ℂ) : thetaExp ((n : ℂ) * z) = thetaExp z ^ n := by
  simp only [thetaExp, ← Complex.exp_nat_mul]
  congr 1
  ring

theorem thetaExp_norm (z : ℂ) : ‖thetaExp z‖ = Real.exp (-2 * Real.pi * z.im) := by
  simp [thetaExp, Complex.norm_exp, mul_re, mul_im]

theorem thetaExp_norm_lt_one {z : ℂ} (hz : 0 < z.im) : ‖thetaExp z‖ < 1 := by
  rw [thetaExp_norm, Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos]

theorem thetaExp_eq_one_iff (z : ℂ) : thetaExp z = 1 ↔ ∃ m : ℤ, z = m := by
  rw [thetaExp, Complex.exp_eq_one_iff]
  have hp : (2 * Real.pi * I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, mul_left_cancel₀ hp (by simpa only [mul_comm] using hm)⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

/-- Product in the shifted coordinate `x = z + (τ+1)/2`.
Its factors are `(1-exp(2πi(x+nτ)))` and `(1-exp(2πi((n+1)τ-x)))`. -/
def thetaShiftedProduct (x τ : ℂ) : ℂ :=
  thetaEulerProduct (thetaExp τ) (thetaExp x) *
    thetaEulerProduct (thetaExp τ) (thetaExp (τ - x))

theorem thetaShiftedProduct_differentiable (τ : ℍ) :
    Differentiable ℂ (fun x => thetaShiftedProduct x τ) := by
  have h := thetaEulerProduct_differentiable (thetaExp_norm_lt_one τ.im_pos)
  exact (h.comp (Complex.differentiable_exp.comp ((differentiable_const (2 * Real.pi * I : ℂ)).mul
    differentiable_id))).mul (h.comp (Complex.differentiable_exp.comp
    ((differentiable_const (2 * Real.pi * I : ℂ)).mul
      ((differentiable_const (τ : ℂ)).sub differentiable_id))))

/-- The nonvanishing half of the product zero-locus theorem. -/
theorem thetaShiftedProduct_ne_zero (τ : ℍ) (x : ℂ)
    (hx : ∀ m k : ℤ, x ≠ (m : ℂ) + (k : ℂ) * τ) :
    thetaShiftedProduct x τ ≠ 0 := by
  have hr := thetaExp_norm_lt_one τ.im_pos
  apply mul_ne_zero <;> apply thetaEulerProduct_ne_zero hr
  · intro n hn
    rw [← thetaExp_nat_mul, ← thetaExp_add, thetaExp_eq_one_iff] at hn
    obtain ⟨m, hm⟩ := hn
    apply hx m (-(n : ℤ))
    push_cast
    linear_combination hm
  · intro n hn
    rw [← thetaExp_nat_mul, ← thetaExp_add, thetaExp_eq_one_iff] at hn
    obtain ⟨m, hm⟩ := hn
    apply hx (-m) ((n : ℤ) + 1)
    push_cast
    linear_combination -hm

/-- The half-period zero follows directly from evenness and quasi-periodicity. -/
theorem theta_halfPeriod_zero (τ : ℂ) : jacobiTheta₂ ((τ + 1) / 2) τ = 0 := by
  let z := (τ + 1) / 2
  have h := jacobiTheta₂_add_left' (-z) τ
  have he : -Real.pi * I * (τ + 2 * -z) = Real.pi * I := by dsimp [z]; ring
  rw [he, Complex.exp_pi_mul_I, jacobiTheta₂_neg_left] at h
  have hz : -z + τ = z - 1 := by dsimp [z]; ring
  rw [hz] at h
  have hp := jacobiTheta₂_add_left (z - 1) τ
  rw [sub_add_cancel] at hp
  rw [← hp] at h
  change jacobiTheta₂ z τ = 0
  linear_combination (1 / 2 : ℂ) * h

end VOA.Classification.COne.SSHecke
