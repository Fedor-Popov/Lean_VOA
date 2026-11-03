import VOA.Huang.GenusOneG1eSeries
import VOA.Modularity.SquareBracketSubst
import VOA.Modularity.SquareBracketWitt

/-!
# The scalar identities behind the bracket energy commutator

Formal power series in the bracket variable `z`. `E = (e^z − 1)/z` (`exponentialUnit`),
`F_b = E^b` (`exponentialUnitPower b`), `e^{αz}` (`expA α`), and `xS = z·E = e^z − 1`.
`cc k = [w^k]((1+w) u(w))` are the coefficients of `L[0] = Σ_k cc k L(k)` (Zhu), where
`(1+w) log(1+w) = w (1+w) u(w)`.

* `unitPower_ode`: `z · d/dz E^b = b (E^{b−1} e^z − E^b)`;
* `energy_scalar_K`: the `L(−1)`/`L(0)` part of the energy commutator in convolution form;
* `energy_scalar_J`: the `L(j−1)`, `j ≥ 2`, part in convolution form.

No module, intertwiner, convergence or analytic power occurs here.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open PowerSeries
open VOA.Huang.GenusOne.IntCoord (exponentialUnit exponentialUnitPower bracketCoeff
  exponentialUnit_sub_one_constant X_mul_exponentialUnit exponentialUnit_constant)
open VOA.Huang.GenusOneG1e (expA unitPower_add_nat)
open scoped BigOperators

/-! ## §1 Basic series -/

/-- `xS = z E(z) = e^z − 1`. -/
def xS : PowerSeries ℂ := X * exponentialUnit

theorem xS_eq : xS = exp ℂ - 1 := X_mul_exponentialUnit

theorem xS_eq_expMinusOne : xS = VOA.expMinusOne := by rw [xS_eq]; rfl

theorem hasSubst_xS : HasSubst xS := by
  rw [xS_eq]; exact HasSubst.exp_sub_one

theorem subst_one' {a : PowerSeries ℂ} (ha : HasSubst a) :
    (1 : PowerSeries ℂ).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

theorem subst_C' {a : PowerSeries ℂ} (_ha : HasSubst a) (c : ℂ) :
    (PowerSeries.C c : PowerSeries ℂ).subst a = PowerSeries.C c := by
  rw [PowerSeries.subst_C]; rfl

theorem subst_one_xS : (1 : PowerSeries ℂ).subst xS = 1 := by
  rw [← map_one (PowerSeries.C (R := ℂ)), PowerSeries.subst_C]; rfl

theorem subst_C_xS (a : ℂ) : (PowerSeries.C a : PowerSeries ℂ).subst xS = PowerSeries.C a := by
  rw [PowerSeries.subst_C]; rfl

theorem subst_onePlusX_xS : (1 + X : PowerSeries ℂ).subst xS = exp ℂ := by
  rw [PowerSeries.subst_add hasSubst_xS, subst_one_xS, PowerSeries.subst_X hasSubst_xS, xS_eq]; ring

theorem exponentialUnit_ne_zero : exponentialUnit ≠ 0 := by
  intro h
  have := exponentialUnit_constant
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem X_ne_zero' : (X : PowerSeries ℂ) ≠ 0 := X_ne_zero

theorem expA_one : expA 1 = exp ℂ := by
  rw [expA, PowerSeries.rescale_one]; rfl

theorem expA_add (a b : ℂ) : expA a * expA b = expA (a + b) :=
  PowerSeries.exp_mul_exp_eq_exp_add a b

theorem expA_mul_exp (a : ℂ) : expA a * exp ℂ = expA (a + 1) := by
  rw [← expA_one, expA_add]

theorem exp_pow_eq (m : ℕ) : (exp ℂ) ^ m = expA m := by
  induction m with
  | zero => ext n; simp [expA]
  | succ m ih => rw [pow_succ, ih, expA_mul_exp]; push_cast; rfl

theorem coeff_X_mul_eq (H : PowerSeries ℂ) (t : ℕ) :
    coeff t (X * H) = if t = 0 then 0 else coeff (t - 1) H := by
  cases t with
  | zero => simp
  | succ t => simp

/-! ## §2 The ODE of `E^b` -/

theorem choose_succ_mul (β : ℂ) (m : ℕ) :
    ((m : ℂ) + 1) * Ring.choose β (m + 1) = (β - m) * Ring.choose β m := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right,
    Polynomial.smeval_mul, smul_eq_mul, smul_eq_mul]
  have hs : (Polynomial.X - (m : Polynomial ℤ)).smeval β = β - m := by
    rw [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast]
    simp
  rw [hs, Nat.factorial_succ]
  have h1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  push_cast
  field_simp

theorem binomial_ode (β : ℂ) :
    (1 + X) * d⁄dX ℂ (PowerSeries.binomialSeries ℂ β) =
      PowerSeries.C β * PowerSeries.binomialSeries ℂ β := by
  ext m
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_C_mul, PowerSeries.binomialSeries_coeff,
    PowerSeries.coeff_derivative,
    PowerSeries.binomialSeries_coeff]
  cases m with
  | zero =>
    simp only [PowerSeries.coeff_zero_X_mul, add_zero, smul_eq_mul, mul_one, Nat.cast_zero,
      zero_add]
    have := choose_succ_mul β 0
    simp only [Nat.cast_zero, zero_add, one_mul, sub_zero] at this
    rw [this]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      PowerSeries.binomialSeries_coeff]
    simp only [smul_eq_mul, mul_one]
    have h := choose_succ_mul β (m + 1)
    push_cast at h ⊢
    linear_combination h

theorem derivative_exponentialUnit :
    X * d⁄dX ℂ exponentialUnit = exp ℂ - exponentialUnit := by
  have h := congrArg (d⁄dX ℂ) X_mul_exponentialUnit
  rw [Derivation.leibniz, PowerSeries.derivative_X, map_sub, PowerSeries.derivative_exp,
    Derivation.map_one_eq_zero,
    sub_zero, smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [← h]; ring

/-- **The ODE of the complex unit power**: `z · d/dz E^b = b (E^{b−1} e^z − E^b)`. -/
theorem unitPower_ode (β : ℂ) :
    X * d⁄dX ℂ (exponentialUnitPower β) =
      PowerSeries.C β * (exponentialUnitPower (β - 1) * exp ℂ - exponentialUnitPower β) := by
  have ha := HasSubst.of_constantCoeff_zero' exponentialUnit_sub_one_constant
  have hd : d⁄dX ℂ (exponentialUnitPower β) =
      (d⁄dX ℂ (PowerSeries.binomialSeries ℂ β)).subst (exponentialUnit - 1) *
        d⁄dX ℂ exponentialUnit := by
    rw [exponentialUnitPower, PowerSeries.derivative_subst ℂ ha, map_sub,
      Derivation.map_one_eq_zero,
      sub_zero]
  have hode := congrArg (fun f => f.subst (exponentialUnit - 1)) (binomial_ode β)
  simp only at hode
  rw [PowerSeries.subst_mul ha, PowerSeries.subst_mul ha, PowerSeries.subst_add ha,
    PowerSeries.subst_X ha, subst_one' ha, subst_C' ha] at hode
  have h1 : (1 : PowerSeries ℂ) + (exponentialUnit - 1) = exponentialUnit := by ring
  rw [h1] at hode
  have hF : exponentialUnitPower β = exponentialUnitPower (β - 1) * exponentialUnit := by
    have := unitPower_add_nat (β - 1) 1
    rw [pow_one] at this
    rw [← this]; congr 1; push_cast; ring
  apply mul_left_cancel₀ exponentialUnit_ne_zero
  rw [hd]
  calc exponentialUnit * (X * ((d⁄dX ℂ (PowerSeries.binomialSeries ℂ β)).subst
          (exponentialUnit - 1) *
          d⁄dX ℂ exponentialUnit))
      = (exponentialUnit * (d⁄dX ℂ (PowerSeries.binomialSeries ℂ β)).subst (exponentialUnit - 1)) *
          (X * d⁄dX ℂ exponentialUnit) := by ring
    _ = (PowerSeries.C β * exponentialUnitPower β) * (exp ℂ - exponentialUnit) := by
          rw [hode, derivative_exponentialUnit]; rfl
    _ = _ := by rw [hF]; ring

theorem derivative_expA (α : ℂ) : d⁄dX ℂ (expA α) = PowerSeries.C α * expA α := by
  ext m
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, VOA.Huang.GenusOneG1e.coeff_expA,
    VOA.Huang.GenusOneG1e.coeff_expA, Nat.factorial_succ]
  have h1 : ((m.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  push_cast
  field_simp
  ring

/-- `z · d/dz (e^{αz} E^b) = α z e^{αz} E^b + b (e^{(α+1)z} E^{b−1} − e^{αz} E^b)`. -/
theorem bracketFactor_ode (α β : ℂ) :
    X * d⁄dX ℂ (expA α * exponentialUnitPower β) =
      PowerSeries.C α * (X * (expA α * exponentialUnitPower β)) +
        PowerSeries.C β * (expA (α + 1) * exponentialUnitPower (β - 1) -
          expA α * exponentialUnitPower β) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add, derivative_expA,
    ← expA_mul_exp]
  have h := unitPower_ode β
  calc X * (expA α * d⁄dX ℂ (exponentialUnitPower β)) +
        X * (exponentialUnitPower β * (PowerSeries.C α * expA α))
      = expA α * (X * d⁄dX ℂ (exponentialUnitPower β)) +
          PowerSeries.C α * (X * (expA α * exponentialUnitPower β)) := by ring
    _ = _ := by rw [h]; ring

/-- **The `L(−1)`, `L(0)` scalar identity, series form.** -/
theorem energy_scalar_K_series (α β : ℂ) (t : ℕ) :
    (t : ℂ) * coeff t (expA α * exponentialUnitPower β) =
      α * coeff t (X * (expA α * exponentialUnitPower β)) +
        β * coeff t (expA (α + 1) * exponentialUnitPower (β - 1)) -
          β * coeff t (expA α * exponentialUnitPower β) := by
  have h := congrArg (coeff t) (bracketFactor_ode α β)
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, map_sub] at h
  have key : coeff t (X * d⁄dX ℂ (expA α * exponentialUnitPower β)) =
      (t : ℂ) * coeff t (expA α * exponentialUnitPower β) := by
    cases t with
    | zero => simp
    | succ t => rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring
  rw [key] at h
  linear_combination h

/-! ## §3 The coefficients of `L[0]` and their generating series in the `z`-coordinate -/

/-- `L[0] = Σ_k cc k · L(k)`: `cc k = [w^k]((1+w) u(w))`, `w (1+w) u(w) = (1+w) log(1+w)`. -/
def cc (k : ℕ) : ℂ := coeff k ((1 + X) * VOA.uSeries)

theorem cc_eq_sqBracketCoeffZ (k : ℕ) : VOA.sqBracketCoeffZ 2 1 ((k + 1 : ℕ) : ℤ) = cc k := by
  have hc := VOA.sqBracketCoeffZ_two_eq_coeff_Pw 0 (k : ℤ)
  simpa [VOA.Pw, VOA.uUnit_coe, cc] using hc

theorem cc_zero : cc 0 = 1 := by
  simp [cc, VOA.uSeries]

theorem coeff_uSeries (i : ℕ) : coeff i VOA.uSeries = (-1 : ℂ) ^ i / (i + 1 : ℂ) := by
  simp [VOA.uSeries]

theorem cc_succ (s : ℕ) : cc (s + 1) = (-1 : ℂ) ^ s / (((s : ℂ) + 1) * ((s : ℂ) + 2)) := by
  rw [cc, add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul, coeff_uSeries,
    coeff_uSeries]
  have h1 : ((s : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have h2 : ((s : ℂ) + 2) ≠ 0 := by
    have : ((s : ℂ) + 2) = ((s + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero (s + 1)
  have h2' : ((s : ℂ) + 1 + 1) ≠ 0 := by rw [add_assoc]; norm_num at h2 ⊢; exact h2
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- `E · u(e^z − 1) = 1`. -/
theorem exponentialUnit_mul_subst_u : exponentialUnit * VOA.uSeries.subst xS = 1 := by
  have h1 : (X * VOA.uSeries).subst xS = X := by
    rw [← VOA.logOnePlusX_eq_X_mul_u, VOA.logOnePlusXSeries_eq_log, xS_eq_expMinusOne,
      VOA.log_subst_expMinusOne]
  rw [PowerSeries.subst_mul hasSubst_xS, PowerSeries.subst_X hasSubst_xS] at h1
  apply mul_left_cancel₀ X_ne_zero'
  rw [mul_one, ← mul_assoc, ← xS]
  exact h1

/-- `Σ_k cc k x^k` at `x = e^z − 1`, times `E`, is `e^z`. -/
theorem phi_subst_mul_E : ((1 + X) * VOA.uSeries).subst xS * exponentialUnit = exp ℂ := by
  rw [PowerSeries.subst_mul hasSubst_xS, subst_onePlusX_xS, mul_assoc, mul_comm _ exponentialUnit,
    exponentialUnit_mul_subst_u, mul_one]

/-- `Σ_k cc k (k+1) x^k = 1 + log(1+x)`. -/
def psi1 : PowerSeries ℂ := PowerSeries.mk fun k => cc k * ((k : ℂ) + 1)

theorem psi1_eq : psi1 = 1 + PowerSeries.log ℂ := by
  have hG : (X : PowerSeries ℂ) * ((1 + X) * VOA.uSeries) = (1 + X) * PowerSeries.log ℂ := by
    rw [← VOA.logOnePlusXSeries_eq_log, VOA.logOnePlusX_eq_X_mul_u]; ring
  have hd : psi1 = d⁄dX ℂ ((X : PowerSeries ℂ) * ((1 + X) * VOA.uSeries)) := by
    ext k
    rw [psi1, PowerSeries.coeff_mk, PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul, cc]
  rw [hd, hG, Derivation.leibniz, smul_eq_mul, smul_eq_mul, VOA.derivative_log_eq_geoAltSeries,
    map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add, mul_one,
    VOA.onePlusX_mul_geoAltSeries]

theorem psi1_subst : psi1.subst xS = 1 + X := by
  rw [psi1_eq, PowerSeries.subst_add hasSubst_xS, subst_one' hasSubst_xS, xS_eq_expMinusOne,
    VOA.log_subst_expMinusOne]

/-- `(1+w)^{−(d+1)} = Σ_i (−1)^i C(d+i, d) w^i`. -/
def nu (d : ℕ) : PowerSeries ℂ := PowerSeries.mk fun i => (-1 : ℂ) ^ i * ((d + i).choose d : ℂ)

theorem onePlusX_mul_nu_succ (d : ℕ) : (1 + X) * nu (d + 1) = nu d := by
  ext i
  rw [add_mul, one_mul, map_add]
  cases i with
  | zero => simp [nu]
  | succ s =>
    rw [PowerSeries.coeff_succ_X_mul, nu, PowerSeries.coeff_mk, PowerSeries.coeff_mk, nu,
      PowerSeries.coeff_mk]
    have hp : (d + 1 + (s + 1)).choose (d + 1) =
        (d + 1 + s).choose d + (d + 1 + s).choose (d + 1) := by
      rw [show d + 1 + (s + 1) = (d + 1 + s) + 1 by omega, Nat.choose_succ_succ']
    have hq : d + (s + 1) = d + 1 + s := by omega
    rw [hp, hq]
    push_cast
    rw [pow_succ]
    ring

theorem onePlusX_pow_mul_nu (d : ℕ) : (1 + X) ^ (d + 1) * nu d = 1 := by
  induction d with
  | zero =>
    have : nu 0 = VOA.geoAltSeries := by ext i; simp [nu, VOA.geoAltSeries]
    rw [this, zero_add, pow_one, VOA.onePlusX_mul_geoAltSeries]
  | succ d ih =>
    rw [pow_succ, mul_assoc, onePlusX_mul_nu_succ, ih]

/-- `Σ_i cc(i+d+1) C(i+d+2, d+2) x^i`, the `L(d+1)` Taylor coefficient. -/
def psiJ (d : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => cc (i + d + 1) * ((i + d + 2).choose (d + 2) : ℂ)

theorem choose_identity (d i : ℕ) :
    ((i + d + 2).choose (d + 2) : ℂ) * (((d : ℂ) + 1) * ((d : ℂ) + 2)) =
      ((d + i).choose d : ℂ) * (((i + d : ℕ) : ℂ) + 1) * (((i + d : ℕ) : ℂ) + 2) := by
  have h1 := Nat.add_one_mul_choose_eq (d + i) d
  have h2 := Nat.add_one_mul_choose_eq (d + i + 1) (d + 1)
  have e : i + d + 2 = d + i + 1 + 1 := by omega
  rw [e]
  have h1' : ((d + i + 1 : ℕ) : ℂ) * ((d + i).choose d : ℂ) =
      ((d + i + 1).choose (d + 1) : ℂ) * ((d + 1 : ℕ) : ℂ) := by exact_mod_cast h1
  have h2' : ((d + i + 1 + 1 : ℕ) : ℂ) * ((d + i + 1).choose (d + 1) : ℂ) =
      ((d + i + 1 + 1).choose (d + 1 + 1) : ℂ) * ((d + 1 + 1 : ℕ) : ℂ) := by exact_mod_cast h2
  push_cast at h1' h2' ⊢
  linear_combination (-((d : ℂ) + 1)) * h2' + (-((i : ℂ) + d + 2)) * h1'

theorem psiJ_eq (d : ℕ) : psiJ d = PowerSeries.C (cc (d + 1)) * nu d := by
  ext i
  rw [psiJ, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, nu, PowerSeries.coeff_mk,
    show i + d + 1 = (i + d) + 1 by omega, cc_succ, cc_succ]
  have hc := choose_identity d i
  have hd1 : ((d : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have hd2 : ((d : ℂ) + 2) ≠ 0 := by
    have : ((d : ℂ) + 2) = ((d + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero (d + 1)
  have he1 : (((i + d : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (i + d)
  have he2 : (((i + d : ℕ) : ℂ) + 2) ≠ 0 := by
    have : (((i + d : ℕ) : ℂ) + 2) = ((i + d + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero (i + d + 1)
  rw [pow_add]
  field_simp
  linear_combination hc

theorem psiJ_mul_onePlusX_pow (d : ℕ) :
    psiJ d * (1 + X) ^ (d + 1) = PowerSeries.C (cc (d + 1)) := by
  rw [psiJ_eq, mul_assoc, mul_comm (nu d), onePlusX_pow_mul_nu, mul_one]

theorem psiJ_subst_mul (d : ℕ) :
    (psiJ d).subst xS * expA ((d : ℂ) + 1) = PowerSeries.C (cc (d + 1)) := by
  have h := congrArg (fun f => f.subst xS) (psiJ_mul_onePlusX_pow d)
  simp only at h
  rw [PowerSeries.subst_mul hasSubst_xS, PowerSeries.subst_pow hasSubst_xS, subst_onePlusX_xS,
    subst_C' hasSubst_xS, exp_pow_eq] at h
  rw [← h]; push_cast; rfl

/-! ## §4 Coefficients of a product with a substituted series -/

theorem coeff_mul_subst_xS (H ψ : PowerSeries ℂ) (t : ℕ) :
    coeff t (H * ψ.subst xS) =
      ∑ i ∈ Finset.range (t + 1), coeff i ψ * coeff (t - i) (H * exponentialUnit ^ i) := by
  set P : PowerSeries ℂ := ∑ i ∈ Finset.range (t + 1), PowerSeries.C (coeff i ψ) * X ^ i with hP
  have hdiv : (X : PowerSeries ℂ) ^ (t + 1) ∣ ψ - P := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hP, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range (t + 1)) m, if_pos (Finset.mem_range.mpr hm), sub_self]
  obtain ⟨ρ, hρ⟩ := hdiv
  have hψ : ψ = P + X ^ (t + 1) * ρ := by rw [← hρ]; ring
  have hxp : xS ^ (t + 1) = X ^ (t + 1) * exponentialUnit ^ (t + 1) := by rw [xS, mul_pow]
  have hzero : coeff t (H * (xS ^ (t + 1) * ρ.subst xS)) = 0 := by
    rw [hxp, show H * (X ^ (t + 1) * exponentialUnit ^ (t + 1) * ρ.subst xS) =
      X ^ (t + 1) * (H * exponentialUnit ^ (t + 1) * ρ.subst xS) by ring,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  conv_lhs => rw [hψ, PowerSeries.subst_add hasSubst_xS, PowerSeries.subst_mul hasSubst_xS,
    PowerSeries.subst_pow hasSubst_xS, PowerSeries.subst_X hasSubst_xS, mul_add, map_add, hzero,
    add_zero, hP, ← PowerSeries.coe_substAlgHom hasSubst_xS, map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hit : i ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [PowerSeries.coe_substAlgHom hasSubst_xS, PowerSeries.subst_mul hasSubst_xS,
    subst_C' hasSubst_xS, PowerSeries.subst_pow hasSubst_xS, PowerSeries.subst_X hasSubst_xS]
  have hxi : xS ^ i = X ^ i * exponentialUnit ^ i := by rw [xS, mul_pow]
  rw [hxi, show H * (PowerSeries.C (coeff i ψ) * (X ^ i * exponentialUnit ^ i)) =
      PowerSeries.C (coeff i ψ) * (X ^ i * (H * exponentialUnit ^ i)) by ring,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos hit]

/-! ## §5 The convolution identities for the explicit bracket coefficients -/

/-- `b(α, n, t−i) = [z^{t−i}] (e^{αz} E^{−n−t−1} E^i)` for `i ≤ t`. -/
theorem bracketCoeff_shift (α n : ℂ) {i t : ℕ} (hit : i ≤ t) :
    bracketCoeff α n (t - i) =
      coeff (t - i) (expA α * exponentialUnitPower (-n - t - 1) * exponentialUnit ^ i) := by
  rw [bracketCoeff, mul_assoc, ← unitPower_add_nat, ← expA]
  congr 3
  push_cast [Nat.cast_sub hit]
  ring

theorem conv_eq_coeff (A : ℕ → ℂ) (α n : ℂ) (t : ℕ) :
    ∑ i ∈ Finset.range (t + 1), A i * bracketCoeff α n (t - i) =
      coeff t (expA α * exponentialUnitPower (-n - t - 1) * (PowerSeries.mk A).subst xS) := by
  rw [coeff_mul_subst_xS]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [PowerSeries.coeff_mk, bracketCoeff_shift α n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem bracketCoeff_eq_coeff (α n : ℂ) (t : ℕ) :
    bracketCoeff α n t = coeff t (expA α * exponentialUnitPower (-n - t - 1)) := rfl

/-- **The `L(d+1)` part (`j = d + 2`) of the bracket energy commutator.** -/
theorem energy_scalar_J (α n : ℂ) (d t : ℕ) :
    ∑ i ∈ Finset.range (t + 1), cc (i + d + 1) * ((i + d + 2).choose (d + 2) : ℂ) *
        bracketCoeff α n (t - i) =
      cc (d + 1) * bracketCoeff (α - (d + 1)) n t := by
  have h := conv_eq_coeff (fun i => cc (i + d + 1) * ((i + d + 2).choose (d + 2) : ℂ)) α n t
  rw [h, show (PowerSeries.mk fun i => cc (i + d + 1) * ((i + d + 2).choose (d + 2) : ℂ)) =
      psiJ d from rfl,
    bracketCoeff_eq_coeff]
  have hα : expA α = expA (α - (d + 1)) * expA ((d : ℂ) + 1) := by rw [expA_add]; ring_nf
  rw [hα, show expA (α - (d + 1)) * expA ((d : ℂ) + 1) * exponentialUnitPower (-n - t - 1) *
      (psiJ d).subst xS = expA (α - (d + 1)) * exponentialUnitPower (-n - t - 1) *
        ((psiJ d).subst xS * expA ((d : ℂ) + 1)) by ring, psiJ_subst_mul,
    mul_comm _ (PowerSeries.C _), PowerSeries.coeff_C_mul]

/-- **The `L(−1)`, `L(0)` part of the bracket energy commutator.** -/
theorem energy_scalar_K (α n : ℂ) (t : ℕ) :
    -(n + t + 1) * ∑ i ∈ Finset.range (t + 1), cc i * bracketCoeff α n (t - i) +
      α * ∑ i ∈ Finset.range (t + 1), cc i * ((i : ℂ) + 1) * bracketCoeff α n (t - i) =
        (α - n - 1) * bracketCoeff α n t := by
  have h0 := conv_eq_coeff cc α n t
  have h1 := conv_eq_coeff (fun i => cc i * ((i : ℂ) + 1)) α n t
  rw [show (PowerSeries.mk cc) = (1 + X) * VOA.uSeries by
    ext k; rw [PowerSeries.coeff_mk]; rfl] at h0
  rw [show (PowerSeries.mk fun i => cc i * ((i : ℂ) + 1)) = psi1 from rfl, psi1_subst] at h1
  rw [h0, h1, bracketCoeff_eq_coeff]
  set β : ℂ := -n - t - 1 with hβ
  have hF : exponentialUnitPower β = exponentialUnitPower (β - 1) * exponentialUnit := by
    have := unitPower_add_nat (β - 1) 1
    rw [pow_one] at this
    rw [← this]; congr 1; push_cast; ring
  have e0 : expA α * exponentialUnitPower β * ((1 + X) * VOA.uSeries).subst xS =
      expA (α + 1) * exponentialUnitPower (β - 1) := by
    rw [hF, ← expA_mul_exp, ← phi_subst_mul_E]; ring
  have e1 : expA α * exponentialUnitPower β * (1 + X) =
      expA α * exponentialUnitPower β + X * (expA α * exponentialUnitPower β) := by ring
  rw [e0, e1, map_add]
  have hK := energy_scalar_K_series α β t
  linear_combination (-1 : ℂ) * hK +
    (coeff t (expA α * exponentialUnitPower β) -
      coeff t (expA (α + 1) * exponentialUnitPower (β - 1))) * hβ

end VOA.Huang.GenusOneG1f
