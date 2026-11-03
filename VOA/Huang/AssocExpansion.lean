/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocTarget
import VOA.Huang.FrobeniusFundamental

/-!
# Products at the iterate point: the log-Frobenius expansion (analytic half)

The associativity theorem must show that a
product of intertwining operators equals a finite sum of iterates on the overlap
`z₁ > z₂ > z₁ − z₂ > 0` (`AssocTarget.AssociativityInput`).  Huang's proof (2005, CCM 7, Thm 3.5)
has an analytic half — the product, continued to the overlap, has a finite expansion
`Σ u^{λ} (log u)^k h(u)` at the iterate point `u = (z₁ − z₂)/z₂ = 0`, eq. (3.3) — and an algebraic
half (the log terms vanish and the coefficients are iterates: Huang–Lepowsky tensor product
theory).  This file does the analytic half, from one named TRUE input.

## Normalization
By homogeneity (`prodValue_scale`, `iterValue_scale`) everything reduces to `z₂ = 1`,
`z₁ = 1 + u`, `z₀ = u ∈ (0, 1)` (`associativityInput_of_atOne`).  Work on the universal cover
`u = e^t`: the **overlap domain** `overlapDomain = {Re t < 0, |Im t| < π/2}` (convex, contains
`log u` for `u ∈ (0,1)`), on which `z₁ = 1 + e^t` has `Re z₁ > 1` (principal powers holomorphic,
product convergent).

## Main results
* `logFuchsianEq_const_of_fuchsianEq`: the library's log-free `FuchsianEq` is the constant-in-`ℓ`
  case of `LogFuchsianEq`.
* `iterFun_eq_logFun`, `iterFun_ode`: the iterate (canonical base) is a log-free
  Frobenius function at `u = 0` and solves Huang's iterate equation on the overlap domain
  (unconditional for strongly rational `V`, from `huangODEInput_holds`).
* `prodFun_eq`, `differentiableOn_prodFun`: the product is holomorphic on the overlap domain
  (unconditional for strongly rational `V`).
* `ProductODEAtIterPoint` (named, TRUE: Huang 2005 Thm 1.4 + Thm 2.3 at `z₁ = z₂`): the product
  solves a Fuchsian equation regular at the iterate point.
* `prod_frobenius_expansion` / `prod_frobenius_expansion_real`: conditional on
  `ProductODEAtIterPoint` only, the product on the overlap is a finite sum
  `Σⱼ aⱼ u^{λⱼ} Σₙ uⁿ pⱼₙ(log u)` with `λⱼ` the indicial roots — Huang's (3.3).
* `prodValue_scale`, `iterValue_scale`, `AssociativityAtOne`, `associativityInput_of_atOne`,
  `AssociativityConverseAtOne`, `associativityConverse_of_atOne`.

## Status
No `sorry`, no new axioms.  `ProductODEAtIterPoint` is open in this file.
-/

namespace VOA.Huang.AssocExpansion

open VOA VOA.Huang.MatrixCoeff VOA.Huang.Convergence VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.FrobeniusLog VOA.Huang.FuchsianODE
open Filter Topology
open scoped BigOperators

universe u

/-! ## The overlap domain -/

/-- `{t : Re t < 0, |Im t| < π/2}`: the image of the overlap `u ∈ (0,1)` thickened in the
universal cover `u = e^t`. -/
def overlapDomain : Set ℂ := {t | t.re < 0 ∧ |t.im| < Real.pi / 2}

theorem isOpen_overlapDomain : IsOpen overlapDomain :=
  (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)

theorem convex_overlapDomain : Convex ℝ overlapDomain := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  rw [abs_lt] at hx2 hy2
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab; subst hab; simpa using hy1
    · nlinarith [mul_lt_mul_of_pos_left hx1 ha']
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    rw [abs_lt]
    obtain ⟨hx3, hx4⟩ := hx2
    obtain ⟨hy3, hy4⟩ := hy2
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab; subst hab; constructor <;> linarith
    · constructor
      · nlinarith [mul_lt_mul_of_pos_left hx3 ha', mul_le_mul_of_nonneg_left hy3.le hb]
      · nlinarith [mul_lt_mul_of_pos_left hx4 ha', mul_le_mul_of_nonneg_left hy4.le hb]

theorem isPreconnected_overlapDomain : IsPreconnected overlapDomain :=
  convex_overlapDomain.isPreconnected

theorem overlapDomain_subset : overlapDomain ⊆ halfPlane := fun _ ht => ht.1

theorem log_mem_overlapDomain {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ((Real.log u : ℝ) : ℂ) ∈ overlapDomain := by
  refine ⟨by simpa using Real.log_neg hu0 hu1, ?_⟩
  simp only [Complex.ofReal_im, abs_zero]
  positivity

theorem overlapDomain_nonempty : overlapDomain.Nonempty :=
  ⟨_, log_mem_overlapDomain (u := 1 / 2) (by norm_num) (by norm_num)⟩

theorem im_bounds {t : ℂ} (ht : t ∈ overlapDomain) : -Real.pi < t.im ∧ t.im ≤ Real.pi := by
  have h := abs_lt.mp ht.2
  constructor <;> linarith [Real.pi_pos]

/-! ## Log-free Fuchsian equations are log-Fuchsian -/

theorem thetaL_iterate_const (lam : ℂ) (G : PowerSeries ℂ) (i n : ℕ) :
    (FrobeniusLog.thetaL lam)^[i] (fun n => Polynomial.C (PowerSeries.coeff n G)) n
      = Polynomial.C (PowerSeries.coeff n ((thetaShift lam)^[i] G)) := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', FrobeniusLog.thetaL, ih,
      dOp_X_add_C_apply, Polynomial.derivative_C, zero_add, coeff_thetaShift, Polynomial.smul_C,
      smul_eq_mul]

/-- **The library's log-free Fuchsian equation is the constant-in-`ℓ` log-Fuchsian equation.** -/
theorem logFuchsianEq_const_of_fuchsianEq {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ}
    {G : PowerSeries ℂ} (h : FuchsianEq lam s c G) :
    LogFuchsianEq lam s c (fun n => Polynomial.C (PowerSeries.coeff n G)) := by
  intro n
  have hn := congrArg (PowerSeries.coeff n) h
  simp only [map_add, map_sum, map_zero] at hn
  have hps : ∀ i, FrobeniusLog.psMul (c i)
      ((FrobeniusLog.thetaL lam)^[i] (fun n => Polynomial.C (PowerSeries.coeff n G))) n
      = Polynomial.C (PowerSeries.coeff n (c i * (thetaShift lam)^[i] G)) := by
    intro i
    rw [FrobeniusLog.psMul, mul_comm, coeff_mul_range, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [thetaL_iterate_const, Polynomial.smul_C, smul_eq_mul, mul_comm]
  rw [thetaL_iterate_const, Finset.sum_congr rfl fun i _ => hps i, ← map_sum, ← map_add, hn,
    map_zero]

/-- A Fuchsian equation can always be taken of order `≥ 1`. -/
theorem exists_fuchsianEq_pos {lam : ℂ} {s : ℕ} {c : ℕ → PowerSeries ℂ} {G : PowerSeries ℂ}
    (hc : ∀ i < s, c i ∈ SubexpPS) (h : FuchsianEq lam s c G) :
    ∃ s' c', 1 ≤ s' ∧ (∀ i < s', c' i ∈ SubexpPS) ∧ FuchsianEq lam s' c' G := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1, fun _ => 0, le_rfl, fun _ _ => SubexpPS.zero_mem, ?_⟩
    have hG : G = 0 := by simpa [FuchsianEq] using h
    simp [FuchsianEq, hG]
  · exact ⟨s, c, hs, hc, h⟩

/-! ## Iterates -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The iterate at `z₂ = 1`, `z₀ = e^t`. -/
noncomputable def iterFun (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ t : ℂ) : ℂ :=
  iterValue Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ (Complex.exp t) 1

/-- The product at `z₂ = 1`, `z₁ = 1 + e^t`. -/
noncomputable def prodFun (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ t : ℂ) : ℂ :=
  prodValue Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ (1 + Complex.exp t) 1

theorem exp_cpow {t : ℂ} (w : ℂ) (h1 : -Real.pi < t.im) (h2 : t.im ≤ Real.pi) :
    Complex.exp t ^ w = Complex.exp (w * t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero t), Complex.log_exp h1 h2, mul_comm]

/-- **The iterate is a log-free Frobenius function** at `u = 0`: exponent `−ν₀ − 1`,
coefficients the iterate series. -/
theorem iterFun_eq_logFun (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) {t : ℂ}
    (h1 : -Real.pi < t.im) (h2 : t.im ≤ Real.pi) :
    iterFun Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ t
      = logFun (-ν₀ - 1)
          (fun k => Polynomial.C (PowerSeries.coeff k (iterSeries Y₃ Y₄ f w₁ w₂ w₃ σ ν₀))) t := by
  unfold iterFun iterValue logFun
  refine tsum_congr fun k => ?_
  rw [Complex.one_cpow, mul_one, exp_cpow _ h1 h2, Polynomial.eval_C, coeff_iterSeries, mul_comm]
  congr 2
  ring

/-- **The iterate solves Huang's iterate equation on the overlap domain** (unconditional for
strongly rational `V`; canonical base of an irreducible intermediate module `Q`). -/
theorem iterFun_ode (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier}
    {Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier}
    (hY₃ : IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃)
    (hY₄ : IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    ∃ s, 1 ≤ s ∧ ∃ c : ℕ → PowerSeries ℂ, (∀ i < s, c i ∈ SubexpPS) ∧
      ∀ t ∈ overlapDomain,
        iteratedDeriv s (iterFun Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)) t
          + ∑ i ∈ Finset.range s, psEval (c i) (Complex.exp t)
            * iteratedDeriv i
                (iterFun Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)) t = 0 := by
  set σ := α₁ + α₂ + α₃ - h₄ - 2
  set ν₀ := α₁ + α₂ - 1 - Q.h
  have hR := (VOA.Huang.ModuleC2.huangODEInput_holds 𝒱 W hV).2 P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ Q.isMod
    hY₃ hY₄ h₁ h₂ h₃ hf (isBase_canonical Q hY₄ h₁ h₂)
  obtain ⟨s₀, b, c₀, p, hc, hG⟩ := hR
  have hc₀ : ∀ i < s₀, c₀ i ∈ SubexpPS := fun i hi =>
    VOA.Huang.FuchsianODE.mem_subexpPS_of_mul_eq' (a := -1) (by simp) (hc i hi)
  obtain ⟨s, c, hs, hcS, hG'⟩ := exists_fuchsianEq_pos hc₀ hG
  refine ⟨s, hs, c, hcS, fun t ht => ?_⟩
  set q : ℕ → Polynomial ℂ :=
    fun k => Polynomial.C (PowerSeries.coeff k (iterSeries Y₃ Y₄ f w₁ w₂ w₃ σ ν₀)) with hq
  have hlog := logFuchsianEq_const_of_fuchsianEq hG'
  have hgood := logGood_of_logFuchsianEq hs hcS hlog
  have hev : iterFun Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ =ᶠ[𝓝 t] logFun (-ν₀ - 1) q :=
    Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht) fun y hy =>
      iterFun_eq_logFun Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ (im_bounds hy).1 (im_bounds hy).2
  rw [hev.iteratedDeriv_eq, Finset.sum_congr rfl fun i _ => by rw [hev.iteratedDeriv_eq]]
  exact logFun_ode hcS hgood hlog (overlapDomain_subset ht)

/-! ## Products: holomorphy on the overlap domain -/

theorem one_lt_re {t : ℂ} (ht : t ∈ overlapDomain) : 1 < (1 + Complex.exp t).re := by
  rw [Complex.add_re, Complex.one_re, Complex.exp_re]
  have hcos : 0 < Real.cos t.im := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp ht.2).1],
    (abs_lt.mp ht.2).2⟩
  have := mul_pos (Real.exp_pos t.re) hcos
  linarith

theorem one_add_exp_ne_zero {t : ℂ} (ht : t ∈ overlapDomain) : 1 + Complex.exp t ≠ 0 := by
  intro h
  have := one_lt_re ht
  rw [h, Complex.zero_re] at this
  linarith

theorem one_add_exp_mem_slitPlane {t : ℂ} (ht : t ∈ overlapDomain) :
    1 + Complex.exp t ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [one_lt_re ht]))

theorem one_lt_norm {t : ℂ} (ht : t ∈ overlapDomain) : 1 < ‖1 + Complex.exp t‖ :=
  lt_of_lt_of_le (one_lt_re ht) (Complex.re_le_norm _)

theorem inv_mem_slitPlane {t : ℂ} (ht : t ∈ overlapDomain) :
    (1 + Complex.exp t)⁻¹ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [Complex.inv_re]
  exact div_pos (by linarith [one_lt_re ht]) (Complex.normSq_pos.mpr (one_add_exp_ne_zero ht))

theorem log_inv_mem_halfPlane {t : ℂ} (ht : t ∈ overlapDomain) :
    Complex.log ((1 + Complex.exp t)⁻¹) ∈ halfPlane := by
  change (Complex.log ((1 + Complex.exp t)⁻¹)).re < 0
  rw [Complex.log_re, norm_inv]
  have h1 := one_lt_norm ht
  exact Real.log_neg (inv_pos.mpr (by linarith)) (inv_lt_one_of_one_lt₀ h1)

/-- The product at `z₂ = 1` as `z₁^{−(σ−ν₀)−1} · G(1/z₁)`, `G` the product series. -/
theorem prodFun_eq (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) {t : ℂ}
    (ht : t ∈ overlapDomain) :
    prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ t
      = (1 + Complex.exp t) ^ (-(σ - ν₀) - 1)
        * psEval (prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) ((1 + Complex.exp t)⁻¹) := by
  have hz := one_add_exp_ne_zero ht
  unfold prodFun prodValue psEval
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [Complex.one_cpow, mul_one, coeff_prodSeries]
  have e : (1 + Complex.exp t) ^ (-(σ - ν₀ + k) - 1)
      = (1 + Complex.exp t) ^ (-(σ - ν₀) - 1) * ((1 + Complex.exp t)⁻¹) ^ k := by
    rw [show -(σ - ν₀ + k) - 1 = (-(σ - ν₀) - 1) + (-(k : ℂ)) by ring,
      Complex.cpow_add _ _ hz, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
  rw [e]
  ring

/-- **The product is holomorphic on the overlap domain** (for any product whose series has
subexponential coefficients, e.g. every product among irreducible modules of a strongly rational
`V`: `differentiableOn_prodFun_of_stronglyRational`). -/
theorem differentiableOn_prodFun (Y₁ : IntertwiningModes M₁ M₅ M₄)
    (Y₂ : IntertwiningModes M₂ M₃ M₅) (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ)
    (hsub : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) :
    DifferentiableOn ℂ (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) overlapDomain := by
  set G := prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀
  set g : ℂ → ℂ := fun t => (1 + Complex.exp t) ^ (-(σ - ν₀) - 1)
    * psEval G (Complex.exp (Complex.log ((1 + Complex.exp t)⁻¹))) with hg
  have heq : Set.EqOn (prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀) g overlapDomain := by
    intro t ht
    rw [prodFun_eq Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ht, hg]
    simp only
    rw [Complex.exp_log (inv_ne_zero (one_add_exp_ne_zero ht))]
  refine DifferentiableOn.congr (fun t ht => ?_) heq
  have hd1 : DifferentiableAt ℂ (fun t => 1 + Complex.exp t) t :=
    (differentiableAt_const _).add Complex.differentiableAt_exp
  have hA : DifferentiableAt ℂ (fun t => (1 + Complex.exp t) ^ (-(σ - ν₀) - 1)) t :=
    hd1.cpow_const (one_add_exp_mem_slitPlane ht)
  have hL : DifferentiableAt ℂ (fun t => Complex.log ((1 + Complex.exp t)⁻¹)) t :=
    (hd1.inv (one_add_exp_ne_zero ht)).clog (inv_mem_slitPlane ht)
  have hP : DifferentiableAt ℂ (fun τ => psEval G (Complex.exp τ))
      (Complex.log ((1 + Complex.exp t)⁻¹)) :=
    ((differentiableOn_psEval_exp hsub).differentiableAt
      (isOpen_halfPlane.mem_nhds (log_inv_mem_halfPlane ht)))
  exact (hA.mul (hP.comp t hL)).differentiableWithinAt

theorem prodSeries_mem_subexpPS (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) ∈ SubexpPS :=
  mem_subexpPS.mpr (subexponential_of_ratFuchsian (by simp)
    ((VOA.Huang.ModuleC2.huangODEInput_holds 𝒱 W hV).1 P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ Q.isMod
      hY₁ hY₂ h₁ h₂ h₃ hf (isBase_canonical Q hY₂ h₂ h₃)))

/-! ## The equation at the iterate point and the expansion -/

/-- **Huang's product equation, regular at the iterate point** (V4-ODE; TRUE for strongly rational
`W`: Huang 2005, CCM 7, Thm 1.4 — products satisfy the system of `R ⊗ W₀ ⊗ ⋯ ⊗ W₃ / J` — and
Thm 2.3 at the singular point `z₁ = z₂`, with `z₂ = 1`; the `C₁`-cofiniteness input is
Abe–Buhl–Dong, already proved in the library as `moduleC1Input_holds`).  In `u = z₁ − 1 = e^t` the
equation is monic in `θ_u = d/dt` with coefficients holomorphic on `|u| < 1` (its only other finite
singular point is `u = −1`, i.e. `z₁ = 0`). -/
def ProductODEAtIterPoint (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
    (f : P₄.carrier →ₗ[ℂ] ℂ),
    w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
    SupportedAt P₄.isMod f h₄ →
  ∃ s, 1 ≤ s ∧ ∃ c : ℕ → PowerSeries ℂ, (∀ i < s, c i ∈ SubexpPS) ∧
    ∀ t ∈ overlapDomain,
      iteratedDeriv s (prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)) t
        + ∑ i ∈ Finset.range s, psEval (c i) (Complex.exp t)
          * iteratedDeriv i
              (prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)) t = 0

/-- **Huang's expansion (3.3) of a product at the iterate point**, conditional on
`ProductODEAtIterPoint` only: on the overlap domain the product is a finite sum of log-Frobenius
functions `y^{λⱼ} Σₙ yⁿ pⱼₙ(log y)` of the equation (`y = e^t = z₁ − z₂`, `z₂ = 1`), the `λⱼ`
indicial roots. -/
theorem prod_frobenius_expansion (hV : StronglyRational W) (hODE : ProductODEAtIterPoint W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    ∃ s, 1 ≤ s ∧ ∃ c : ℕ → PowerSeries ℂ, (∀ i < s, c i ∈ SubexpPS) ∧
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℂ) (p : ι → ℕ → Polynomial ℂ) (a : ι → ℂ),
      Fintype.card ι = s ∧ (∀ j, LogFuchsianEq (lam j) s c (p j)) ∧
      (∀ j, (indicial s c).IsRoot (lam j)) ∧
      ∀ t ∈ overlapDomain,
        prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
          = ∑ j, a j * logFun (lam j) (p j) t := by
  obtain ⟨s, hs, c, hc, hode⟩ :=
    hODE P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf
  refine ⟨s, hs, c, hc, ?_⟩
  exact fundamental_system hs hc isOpen_overlapDomain isPreconnected_overlapDomain
    overlapDomain_subset overlapDomain_nonempty
    (differentiableOn_prodFun Y₁ Y₂ f w₁ w₂ w₃ _ _
      (prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf)) hode

/-- The same on the real overlap `u = z₁ − z₂ ∈ (0, 1)`, `z₂ = 1`:
`⟨f, 𝒴₁(w₁, 1+u)𝒴₂(w₂, 1)w₃⟩ = Σⱼ aⱼ u^{λⱼ} Σₙ uⁿ pⱼₙ(log u)`. -/
theorem prod_frobenius_expansion_real (hV : StronglyRational W)
    (hODE : ProductODEAtIterPoint W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄) :
    ∃ s, 1 ≤ s ∧ ∃ c : ℕ → PowerSeries ℂ, (∀ i < s, c i ∈ SubexpPS) ∧
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℂ) (p : ι → ℕ → Polynomial ℂ) (a : ι → ℂ),
      Fintype.card ι = s ∧ (∀ j, LogFuchsianEq (lam j) s c (p j)) ∧
      ∀ x : ℝ, 0 < x → x < 1 →
        prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)
            (((1 + x : ℝ)) : ℂ) 1
          = ∑ j, a j * logFun (lam j) (p j) (Real.log x) := by
  obtain ⟨s, hs, c, hc, ι, hι, lam, p, a, hcard, hlog, -, heq⟩ :=
    prod_frobenius_expansion hV hODE i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf
  refine ⟨s, hs, c, hc, ι, hι, lam, p, a, hcard, hlog, fun x hx0 hx1 => ?_⟩
  have h := heq _ (log_mem_overlapDomain hx0 hx1)
  rw [prodFun, ← Complex.ofReal_exp, Real.exp_log hx0] at h
  rw [← h]
  push_cast
  rfl

/-! ## Normalization to `z₂ = 1` -/

/-- Homogeneity of the product: `prodValue(r x₁, r x₂) = r^{−σ−2} prodValue(x₁, x₂)` for real
`r > 0`, `x₁, x₂ ≥ 0`. -/
theorem prodValue_scale (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) {r x₁ x₂ : ℝ} (hr : 0 < r)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) :
    prodValue Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ((r * x₁ : ℝ) : ℂ) ((r * x₂ : ℝ) : ℂ)
      = (r : ℂ) ^ (-σ - 2) * prodValue Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ x₁ x₂ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold prodValue
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg hr.le hx₁, Complex.mul_cpow_ofReal_nonneg hr.le hx₂]
  have hab : (r : ℂ) ^ (-(σ - ν₀ + k) - 1) * (r : ℂ) ^ (-(ν₀ - k) - 1) = (r : ℂ) ^ (-σ - 2) := by
    rw [← Complex.cpow_add _ _ hr0]; congr 1; ring
  rw [← hab]
  ring

/-- Homogeneity of the iterate. -/
theorem iterValue_scale (Y₃ : IntertwiningModes M₅ M₃ M₄) (Y₄ : IntertwiningModes M₁ M₂ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) {r x₀ x₂ : ℝ} (hr : 0 < r)
    (hx₀ : 0 ≤ x₀) (hx₂ : 0 ≤ x₂) :
    iterValue Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ ((r * x₀ : ℝ) : ℂ) ((r * x₂ : ℝ) : ℂ)
      = (r : ℂ) ^ (-σ - 2) * iterValue Y₃ Y₄ f w₁ w₂ w₃ σ ν₀ x₀ x₂ := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold iterValue
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  rw [Complex.mul_cpow_ofReal_nonneg hr.le hx₀, Complex.mul_cpow_ofReal_nonneg hr.le hx₂]
  have hab : (r : ℂ) ^ (-(σ - ν₀ + k) - 1) * (r : ℂ) ^ (-(ν₀ - k) - 1) = (r : ℂ) ^ (-σ - 2) := by
    rw [← Complex.cpow_add _ _ hr0]; congr 1; ring
  rw [← hab]
  ring

/-- **Associativity normalized to `z₂ = 1`**: the same statement as
`AssocTarget.AssociativityInput`, on `z₁ = 1 + x`, `z₀ = x ∈ (0, 1)`. -/
def AssociativityAtOne (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Y₄ : ∀ j, IntertwiningModes P₁.carrier P₂.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₁.isMod P₂.isMod (Qs j).isMod (Y₄ j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ x : ℝ, 0 < x → x < 1 →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)
          (((1 + x : ℝ)) : ℂ) ((1 : ℝ) : ℂ)
        = ∑ j, iterValue (Y₃ j) (Y₄ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) ((x : ℝ) : ℂ) ((1 : ℝ) : ℂ)

/-- **Associativity reduces to `z₂ = 1`** (homogeneity). -/
theorem associativityInput_of_atOne (h : AssociativityAtOne W) : AssociativityInput W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, heq⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf z₁ z₂ hpos hlt
  have hz₂ : 0 < z₂ := by linarith
  set x : ℝ := (z₁ - z₂) / z₂ with hx
  have hx0 : 0 < x := div_pos hpos hz₂
  have hx1 : x < 1 := (div_lt_one hz₂).mpr hlt
  have e1 : z₁ = z₂ * (1 + x) := by rw [hx]; field_simp; ring
  have e2 : z₁ - z₂ = z₂ * x := by rw [hx]; field_simp
  have e3 : z₂ = z₂ * 1 := (mul_one z₂).symm
  have hP := prodValue_scale Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) hz₂
    (x₁ := 1 + x) (x₂ := 1) (by linarith) zero_le_one
  rw [← e1, ← e3] at hP
  rw [hP, heq α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf x hx0 hx1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hI := iterValue_scale (Y₃ j) (Y₄ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
    (α₁ + α₂ - 1 - (Qs j).h) hz₂ (x₀ := x) (x₂ := 1) hx0.le zero_le_one
  rw [← e2, ← e3] at hI
  rw [hI]

/-- **The converse normalized to `z₂ = 1`** (same statement as `AssocTarget.AssociativityConverse`,
on `z₁ = 1 + x`, `z₀ = x ∈ (0, 1)`). -/
def AssociativityConverseAtOne (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₃ : IntertwiningModes Q.carrier P₃.carrier P₄.carrier)
    (Y₄ : IntertwiningModes P₁.carrier P₂.carrier Q.carrier),
    IsIntertwiningOperator Q.isMod P₃.isMod P₄.isMod Y₃ →
    IsIntertwiningOperator P₁.isMod P₂.isMod Q.isMod Y₄ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₁ : ∀ j, IntertwiningModes P₁.carrier (Qs j).carrier P₄.carrier)
    (Y₂ : ∀ j, IntertwiningModes P₂.carrier P₃.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator P₁.isMod (Qs j).isMod P₄.isMod (Y₁ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₃.isMod (Qs j).isMod (Y₂ j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ x : ℝ, 0 < x → x < 1 →
      iterValue Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h)
          ((x : ℝ) : ℂ) ((1 : ℝ) : ℂ)
        = ∑ j, prodValue (Y₁ j) (Y₂ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₂ + α₃ - 1 - (Qs j).h) (((1 + x : ℝ)) : ℂ) ((1 : ℝ) : ℂ)

/-- **The converse reduces to `z₂ = 1`** (homogeneity). -/
theorem associativityConverse_of_atOne (h : AssociativityConverseAtOne W) :
    AssociativityConverse W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₃ Y₄ hY₃ hY₄
  obtain ⟨r, Qs, iQs, Y₁, Y₂, hY₁, hY₂, heq⟩ := h P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₃ Y₄ hY₃ hY₄
  refine ⟨r, Qs, iQs, Y₁, Y₂, hY₁, hY₂, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf z₁ z₂ hpos hlt
  have hz₂ : 0 < z₂ := by linarith
  set x : ℝ := (z₁ - z₂) / z₂ with hx
  have hx0 : 0 < x := div_pos hpos hz₂
  have hx1 : x < 1 := (div_lt_one hz₂).mpr hlt
  have e1 : z₁ = z₂ * (1 + x) := by rw [hx]; field_simp; ring
  have e2 : z₁ - z₂ = z₂ * x := by rw [hx]; field_simp
  have e3 : z₂ = z₂ * 1 := (mul_one z₂).symm
  have hI := iterValue_scale Y₃ Y₄ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₁ + α₂ - 1 - Q.h) hz₂
    (x₀ := x) (x₂ := 1) hx0.le zero_le_one
  rw [← e2, ← e3] at hI
  rw [hI, heq α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf x hx0 hx1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hP := prodValue_scale (Y₁ j) (Y₂ j) f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
    (α₂ + α₃ - 1 - (Qs j).h) hz₂ (x₁ := 1 + x) (x₂ := 1) (by linarith) zero_le_one
  rw [← e1, ← e3] at hP
  rw [hP]

end VOA.Huang.AssocExpansion
