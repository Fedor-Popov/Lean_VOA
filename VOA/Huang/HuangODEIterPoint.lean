/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HuangODEIterPointAlg
import VOA.Huang.AssocExpansion

/-!
# Products at the iterate point: the analytic equation

From the formal relation `exists_dop_relation_prodSeries` (`Huang/HuangODEIterPointAlg.lean`) to
the analytic statement `AssocExpansion.ProductODEAtIterPoint`: at `z₂ = 1`, `z₁ = 1 + e^t`,
`x = z₂/z₁ = (1 + e^t)⁻¹`, the product is `Ev κ σ H` (`prodFun_eq_Ev`), where
`Ev κ σ Z t = e^{−σt}(1 + e^t)^{−κ} Z(x(t))`, and `d/dt ∘ Ev = Ev ∘ DOp` (`hasDerivAt_Ev`).
Polynomials in `x` become power series in `u = e^t` converging on `|u| < 1`
(`exists_subexp_of_mem_ratRing_zero`: `x = Σ (−u)ⁿ`).

## Main results
* `psEval_add`, `psEval_mul`, `psEval_pow`, `psEval_sum`, `psEval_coe` — evaluation of series with
  subexponential coefficients inside the unit disc is a ring map.
* `hasDerivAt_psEval_exp`, `hasDerivAt_Ev`, `iteratedDeriv_Ev`.
* `productODEAtIterPoint_holds : StronglyRational W → ProductODEAtIterPoint W`
  (Huang 2005, Thm 1.4 + Thm 2.3 at `z₂⁻¹(z₁ − z₂) = 0`, for products).
* `prod_frobenius_expansion_holds`, `prod_frobenius_expansion_real_holds` — Huang's (3.3),
  unconditional for strongly rational `V`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.HuangODEIterPoint

open VOA VOA.Huang.FuchsianODE VOA.Huang.HuangODEAlgebra VOA.Huang.AssocExpansion
  VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget VOA.Huang.HuangODEProduct
open VOA.Huang.FrobeniusLog (psEval logFun halfPlane LogGood LogFuchsianEq)
open Filter Topology
open scoped BigOperators

universe u

/-! ## Evaluating convergent power series inside the unit disc -/

section Eval

theorem summable_norm_psEval {c : PowerSeries ℂ} (hc : c ∈ SubexpPS) {y : ℂ} (hy : ‖y‖ < 1) :
    Summable fun n => ‖PowerSeries.coeff n c * y ^ n‖ := by
  have := summable_of_subexponential (fun n => norm_nonneg _) (mem_subexpPS.mp hc)
    (norm_nonneg y) hy
  refine this.congr fun n => ?_
  rw [norm_mul, norm_pow]

theorem psEval_add {A B : PowerSeries ℂ} (hA : A ∈ SubexpPS) (hB : B ∈ SubexpPS) {y : ℂ}
    (hy : ‖y‖ < 1) : psEval (A + B) y = psEval A y + psEval B y := by
  unfold psEval
  rw [← (summable_norm_psEval hA hy).of_norm.tsum_add (summable_norm_psEval hB hy).of_norm]
  exact tsum_congr fun n => by rw [map_add, add_mul]

theorem psEval_smul (a : ℂ) (A : PowerSeries ℂ) (y : ℂ) : psEval (a • A) y = a * psEval A y := by
  unfold psEval
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_smul, smul_eq_mul, mul_assoc]

theorem psEval_C_mul (a : ℂ) (A : PowerSeries ℂ) (y : ℂ) :
    psEval (PowerSeries.C a * A) y = a * psEval A y := by
  rw [← PowerSeries.smul_eq_C_mul, psEval_smul]

theorem psEval_neg (A : PowerSeries ℂ) (y : ℂ) : psEval (-A) y = -psEval A y := by
  unfold psEval
  rw [← tsum_neg]
  exact tsum_congr fun n => by rw [map_neg, neg_mul]

theorem psEval_sub {A B : PowerSeries ℂ} (hA : A ∈ SubexpPS) (hB : B ∈ SubexpPS) {y : ℂ}
    (hy : ‖y‖ < 1) : psEval (A - B) y = psEval A y - psEval B y := by
  rw [sub_eq_add_neg, psEval_add hA (SubexpPS.neg_mem hB) hy, psEval_neg, ← sub_eq_add_neg]

theorem psEval_mul {A B : PowerSeries ℂ} (hA : A ∈ SubexpPS) (hB : B ∈ SubexpPS) {y : ℂ}
    (hy : ‖y‖ < 1) : psEval (A * B) y = psEval A y * psEval B y := by
  unfold psEval
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm (summable_norm_psEval hA hy)
    (summable_norm_psEval hB hy)]
  refine tsum_congr fun n => ?_
  rw [coeff_mul_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hp : y ^ n = y ^ m * y ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hp]; ring

theorem psEval_one (y : ℂ) : psEval 1 y = 1 := by
  unfold psEval
  rw [tsum_eq_single 0 (fun n hn => by rw [PowerSeries.coeff_one, if_neg hn, zero_mul])]
  simp

theorem psEval_X (y : ℂ) : psEval PowerSeries.X y = y := by
  unfold psEval
  rw [tsum_eq_single 1 (fun n hn => by rw [PowerSeries.coeff_X, if_neg hn, zero_mul])]
  simp

theorem X_mem_subexp : (PowerSeries.X : PowerSeries ℂ) ∈ SubexpPS := by
  simpa [Polynomial.coe_X] using polynomial_mem_subexpPS Polynomial.X

theorem C_mem_subexp (a : ℂ) : PowerSeries.C a ∈ SubexpPS := by
  simpa [Polynomial.coe_C] using polynomial_mem_subexpPS (Polynomial.C a)

theorem one_sub_X_mem_subexp : (1 - PowerSeries.X : PowerSeries ℂ) ∈ SubexpPS :=
  SubexpPS.sub_mem SubexpPS.one_mem X_mem_subexp

theorem psEval_pow {A : PowerSeries ℂ} (hA : A ∈ SubexpPS) {y : ℂ} (hy : ‖y‖ < 1) (n : ℕ) :
    psEval (A ^ n) y = psEval A y ^ n := by
  induction n with
  | zero => simp [psEval_one]
  | succ n ih => rw [pow_succ, psEval_mul (SubexpPS.pow_mem hA n) hA hy, ih, pow_succ]

theorem psEval_sum {ι : Type*} (S : Finset ι) {A : ι → PowerSeries ℂ}
    (hA : ∀ i ∈ S, A i ∈ SubexpPS) {y : ℂ} (hy : ‖y‖ < 1) :
    psEval (∑ i ∈ S, A i) y = ∑ i ∈ S, psEval (A i) y := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold psEval; simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      psEval_add (hA a (Finset.mem_insert_self a S))
        (SubexpPS.sum_mem fun i hi => hA i (Finset.mem_insert_of_mem hi)) hy,
      ih fun i hi => hA i (Finset.mem_insert_of_mem hi)]

/-- A polynomial evaluates to its value. -/
theorem psEval_coe (p : Polynomial ℂ) (y : ℂ) : psEval (p : PowerSeries ℂ) y = p.eval y := by
  unfold psEval
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1)) (fun n hn => by
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simp only [Finset.mem_range, not_lt] at hn; omega), zero_mul]),
    Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl fun n _ => by rw [Polynomial.coeff_coe]

theorem mem_ratRing_zero {r : PowerSeries ℂ} (hr : r ∈ ratRing 0) :
    ∃ p : Polynomial ℂ, r = (p : PowerSeries ℂ) := by
  obtain ⟨b, p, hp⟩ := exists_poly_of_mem_ratRing hr
  refine ⟨p, ?_⟩
  simpa using hp

theorem subexp_of_mem_ratRing_zero {r : PowerSeries ℂ} (hr : r ∈ ratRing 0) : r ∈ SubexpPS := by
  obtain ⟨p, rfl⟩ := mem_ratRing_zero hr
  exact polynomial_mem_subexpPS p

/-- `x = (1 + u)⁻¹ = Σ (−u)ⁿ`. -/
theorem psEval_geom_neg_one {u : ℂ} (hu : ‖u‖ < 1) : psEval (geom (-1)) u = (1 + u)⁻¹ := by
  unfold psEval geom
  have h : ‖-u‖ < 1 := by rwa [norm_neg]
  rw [← sub_neg_eq_add, ← tsum_geometric_of_norm_lt_one h]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_mk, neg_pow (u) n]

theorem geom_neg_one_mem : geom (-1) ∈ SubexpPS := mk_pow_mem_subexpPS (by simp)

/-- **Polynomials in `x` are convergent power series in `u`**: `r(x)` with `x = (1 + u)⁻¹`. -/
theorem exists_subexp_of_mem_ratRing_zero {r : PowerSeries ℂ} (hr : r ∈ ratRing 0) :
    ∃ c ∈ SubexpPS, ∀ u : ℂ, ‖u‖ < 1 → psEval c u = psEval r (1 + u)⁻¹ := by
  obtain ⟨p, rfl⟩ := mem_ratRing_zero hr
  refine ⟨∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • geom (-1) ^ k,
    SubexpPS.sum_mem fun k _ => SubexpPS.smul_mem (SubexpPS.pow_mem geom_neg_one_mem k) _,
    fun u hu => ?_⟩
  rw [psEval_sum _ (fun k _ => SubexpPS.smul_mem (SubexpPS.pow_mem geom_neg_one_mem k) _) hu,
    psEval_coe, Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [psEval_smul, psEval_pow geom_neg_one_mem hu, psEval_geom_neg_one hu]

end Eval

/-! ## `d/dt` at the iterate point -/

section Deriv

theorem thetaShift_zero_eq (Z : PowerSeries ℂ) : thetaShift 0 Z = VOA.theta Z := by
  ext n; simp [coeff_thetaShift]

/-- `d/dτ Z(e^τ) = (θZ)(e^τ)` on `Re τ < 0`. -/
theorem hasDerivAt_psEval_exp {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) {τ : ℂ}
    (hτ : τ ∈ halfPlane) :
    HasDerivAt (fun τ => psEval Z (Complex.exp τ)) (psEval (VOA.theta Z) (Complex.exp τ)) τ := by
  have h := FrobeniusLog.hasDerivAt_logFun (FrobeniusLog.logGood_const hZ) 0 hτ
  have e1 : (fun τ => psEval Z (Complex.exp τ))
      = logFun 0 (fun n => Polynomial.C (PowerSeries.coeff n Z)) :=
    funext fun τ => FrobeniusLog.psEval_exp_eq_logFun Z τ
  rw [e1, FrobeniusLog.psEval_exp_eq_logFun]
  convert h using 2
  funext n
  have := thetaL_iterate_const 0 Z 1 n
  simp only [Function.iterate_one] at this
  rw [this, thetaShift_zero_eq]

/-- `x(t) = (1 + e^t)⁻¹ = z₂/z₁` at `z₂ = 1`, `z₁ = 1 + e^t`. -/
noncomputable def xt (t : ℂ) : ℂ := (1 + Complex.exp t)⁻¹

/-- `Ev κ σ Z t = e^{−σt} (1 + e^t)^{−κ} Z(x(t))`. -/
noncomputable def Ev (κ σ : ℂ) (Z : PowerSeries ℂ) (t : ℂ) : ℂ :=
  Complex.exp (-(σ * t)) * ((1 + Complex.exp t) ^ (-κ) * psEval Z (xt t))

theorem norm_xt_lt_one {t : ℂ} (ht : t ∈ overlapDomain) : ‖xt t‖ < 1 := by
  rw [xt, norm_inv]
  exact inv_lt_one_of_one_lt₀ (one_lt_norm ht)

theorem DOp_mem (κ σ : ℂ) {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) : DOp κ σ Z ∈ SubexpPS := by
  rw [DOp_apply]
  exact SubexpPS.sub_mem (SubexpPS.neg_mem (SubexpPS.mul_mem one_sub_X_mem_subexp
    (SubexpPS.add_mem (theta_mem_subexpPS hZ) (SubexpPS.mul_mem (C_mem_subexp κ) hZ))))
    (SubexpPS.mul_mem (C_mem_subexp σ) hZ)

theorem DOp_iterate_mem (κ σ : ℂ) {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) (i : ℕ) :
    (DOp κ σ)^[i] Z ∈ SubexpPS := by
  induction i with
  | zero => simpa using hZ
  | succ i ih => rw [Function.iterate_succ_apply']; exact DOp_mem κ σ ih

theorem psEval_DOp (κ σ : ℂ) {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) {y : ℂ} (hy : ‖y‖ < 1) :
    psEval (DOp κ σ Z) y
      = -((1 - y) * (psEval (VOA.theta Z) y + κ * psEval Z y)) - σ * psEval Z y := by
  have hθ := theta_mem_subexpPS hZ
  have hκ := SubexpPS.mul_mem (C_mem_subexp κ) hZ
  rw [DOp_apply, psEval_sub (SubexpPS.neg_mem (SubexpPS.mul_mem one_sub_X_mem_subexp
      (SubexpPS.add_mem hθ hκ))) (SubexpPS.mul_mem (C_mem_subexp σ) hZ) hy, psEval_neg,
    psEval_mul one_sub_X_mem_subexp (SubexpPS.add_mem hθ hκ) hy,
    psEval_add hθ hκ hy, psEval_C_mul, psEval_C_mul,
    psEval_sub SubexpPS.one_mem X_mem_subexp hy, psEval_one, psEval_X]

/-- **`d/dt ∘ Ev = Ev ∘ DOp`** on the overlap domain. -/
theorem hasDerivAt_Ev (κ σ : ℂ) {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) {t : ℂ}
    (ht : t ∈ overlapDomain) : HasDerivAt (Ev κ σ Z) (Ev κ σ (DOp κ σ Z) t) t := by
  have hz : 1 + Complex.exp t ≠ 0 := one_add_exp_ne_zero ht
  have h1 : HasDerivAt (fun t => Complex.exp (-(σ * t))) (Complex.exp (-(σ * t)) * (-(σ * 1)))
      t := ((hasDerivAt_id t).const_mul σ).neg.cexp
  have hd : HasDerivAt (fun t => 1 + Complex.exp t) (Complex.exp t) t := by
    simpa using (Complex.hasDerivAt_exp t).const_add 1
  have h2 : HasDerivAt (fun t => (1 + Complex.exp t) ^ (-κ))
      ((-κ) * (1 + Complex.exp t) ^ (-κ - 1) * Complex.exp t) t :=
    hd.cpow_const (one_add_exp_mem_slitPlane ht)
  have hinv : HasDerivAt (fun t => (1 + Complex.exp t)⁻¹)
      (-(Complex.exp t) / (1 + Complex.exp t) ^ 2) t := hd.inv hz
  have hlog : HasDerivAt (fun t => Complex.log ((1 + Complex.exp t)⁻¹))
      ((-(Complex.exp t) / (1 + Complex.exp t) ^ 2) / (1 + Complex.exp t)⁻¹) t :=
    hinv.clog (inv_mem_slitPlane ht)
  have hg := hasDerivAt_psEval_exp hZ (log_inv_mem_halfPlane ht)
  have h3 := hg.comp t hlog
  have heq : (fun t => psEval Z (xt t))
      =ᶠ[𝓝 t] (fun τ => psEval Z (Complex.exp τ)) ∘
        (fun t => Complex.log ((1 + Complex.exp t)⁻¹)) := by
    filter_upwards [isOpen_overlapDomain.mem_nhds ht] with y hy
    simp only [Function.comp, xt]
    rw [Complex.exp_log (inv_ne_zero (one_add_exp_ne_zero hy))]
  have h3' := h3.congr_of_eventuallyEq heq
  have hE := h1.mul (h2.mul h3')
  have hy := norm_xt_lt_one ht
  rw [Complex.exp_log (inv_ne_zero hz)] at hE
  convert hE using 1
  simp only [Pi.mul_apply]
  rw [Ev, psEval_DOp κ σ hZ hy, Complex.cpow_sub _ _ hz, Complex.cpow_one]
  simp only [xt]
  field_simp
  ring

theorem iteratedDeriv_Ev (κ σ : ℂ) {Z : PowerSeries ℂ} (hZ : Z ∈ SubexpPS) (i : ℕ) :
    ∀ t ∈ overlapDomain, iteratedDeriv i (Ev κ σ Z) t = Ev κ σ ((DOp κ σ)^[i] Z) t := by
  induction i with
  | zero => intro t _; simp
  | succ i ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv i (Ev κ σ Z) =ᶠ[𝓝 t] Ev κ σ ((DOp κ σ)^[i] Z) :=
      Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht) fun y hy => ih y hy
    rw [hev.deriv_eq, (hasDerivAt_Ev κ σ (DOp_iterate_mem κ σ hZ i) ht).deriv,
      Function.iterate_succ_apply']

theorem Ev_sum_mul (κ σ : ℂ) (S : Finset ℕ) {r Z : ℕ → PowerSeries ℂ}
    (hr : ∀ k ∈ S, r k ∈ SubexpPS) (hZ : ∀ k ∈ S, Z k ∈ SubexpPS) {t : ℂ}
    (ht : t ∈ overlapDomain) :
    Ev κ σ (∑ k ∈ S, r k * Z k) t = ∑ k ∈ S, psEval (r k) (xt t) * Ev κ σ (Z k) t := by
  have hy := norm_xt_lt_one ht
  rw [Ev, psEval_sum S (fun k hk => SubexpPS.mul_mem (hr k hk) (hZ k hk)) hy, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [psEval_mul (hr k hk) (hZ k hk) hy, Ev]
  ring

end Deriv

/-! ## The product as `Ev` -/

section Assembly

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ M₂ M₃ M₄ M₅ : Type u}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup M₄] [Module ℂ M₄]
  [AddCommGroup M₅] [Module ℂ M₅]

/-- The product at `z₂ = 1`, `z₁ = 1 + e^t` is `Ev κ b ((1 − x)^b x^K G)` for
`κ = σ − ν₀ + 1 − b − K`. -/
theorem prodFun_eq_Ev (Y₁ : IntertwiningModes M₁ M₅ M₄) (Y₂ : IntertwiningModes M₂ M₃ M₅)
    (f : M₄ →ₗ[ℂ] ℂ) (w₁ : M₁) (w₂ : M₂) (w₃ : M₃) (σ ν₀ : ℂ) (b K : ℕ)
    (hG : prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ∈ SubexpPS) {t : ℂ} (ht : t ∈ overlapDomain) :
    prodFun Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ t
      = Ev (σ - ν₀ + 1 - b - K) b ((1 - PowerSeries.X) ^ b *
          (PowerSeries.X ^ K * prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀)) t := by
  have hz := one_add_exp_ne_zero ht
  have hy := norm_xt_lt_one ht
  set G := prodSeries Y₁ Y₂ f w₁ w₂ w₃ σ ν₀
  rw [prodFun_eq Y₁ Y₂ f w₁ w₂ w₃ σ ν₀ ht, Ev,
    psEval_mul (SubexpPS.pow_mem one_sub_X_mem_subexp b)
      (SubexpPS.mul_mem (SubexpPS.pow_mem X_mem_subexp K) hG) hy,
    psEval_mul (SubexpPS.pow_mem X_mem_subexp K) hG hy,
    psEval_pow one_sub_X_mem_subexp hy, psEval_pow X_mem_subexp hy,
    psEval_sub SubexpPS.one_mem X_mem_subexp hy, psEval_one, psEval_X]
  set e := Complex.exp t with he
  set z := 1 + e with hzdef
  have h1x : 1 - xt t = e * xt t := by
    simp only [xt]; rw [← hzdef]; field_simp; rw [hzdef]; ring
  have hexp : Complex.exp (-((b : ℂ) * t)) * e ^ b = 1 := by
    rw [he, ← Complex.exp_nat_mul, ← Complex.exp_add]; simp
  have hcp : z ^ (-(σ - ν₀) - 1) = z ^ (-(σ - ν₀ + 1 - b - K)) * (xt t) ^ (b + K) := by
    rw [show -(σ - ν₀) - 1 = -(σ - ν₀ + 1 - b - K) - ((b + K : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_sub _ _ hz, Complex.cpow_natCast, xt, ← hzdef, inv_pow, div_eq_mul_inv]
  rw [hcp, h1x, mul_pow, pow_add]
  calc z ^ (-(σ - ν₀ + 1 - ↑b - ↑K)) * (xt t ^ b * xt t ^ K) * psEval G (xt t)
      = (Complex.exp (-((b : ℂ) * t)) * e ^ b) * (z ^ (-(σ - ν₀ + 1 - ↑b - ↑K))
          * (xt t ^ b * xt t ^ K) * psEval G (xt t)) := by rw [hexp, one_mul]
    _ = _ := by simp only [xt]; ring

/-- **Huang's product equation at the iterate point** (Huang 2005, CCM 7, Thm 1.4 + Thm 2.3
at `z₂⁻¹(z₁ − z₂) = 0`, for products), unconditional for strongly rational `W`: at `z₂ = 1`,
`z₁ = 1 + e^t`, the product solves a monic linear equation in `d/dt = θ_u` (`u = z₁ − z₂ = e^t`)
whose coefficients are power series in `u` converging on `|u| < 1`. -/
theorem productODEAtIterPoint_holds (hV : StronglyRational W) : ProductODEAtIterPoint W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf
  have h2 := VOA.Huang.BuhlSpanning.moduleC2Input_holds.{u}
  have hC : ModuleC1Data W := VOA.Huang.HuangODEC1.moduleC1Data_of_C2 (fun P hP => h2 𝒱 W hV P hP)
    (VOA.Huang.HuangODEDual.moduleDualC1Data_of_contragredientC2
      (VOA.Huang.HuangODEContra.contragredientC2Data_of_moduleC2Input h2 hV))
  obtain ⟨B₁, c₁⟩ := (hC P₁ i₁).1
  obtain ⟨B₂, c₂⟩ := (hC P₂ i₂).1
  obtain ⟨B₃, c₃⟩ := (hC P₃ i₃).1
  obtain ⟨B₄, d₄⟩ := (hC P₄ i₄).2
  have hb := isBase_canonical Q hY₂ h₂ h₃
  obtain ⟨b, K, hrel⟩ := exists_dop_relation_prodSeries hY₁ hY₂ P₁.isLow P₂.isLow P₃.isLow
    P₄.isLow c₁ c₂ c₃ d₄ f h₁ h₂ h₃ (h₄' := h₄) hb
  have hG := prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf
  set G := prodSeries Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) with hGdef
  set κ : ℂ := (α₁ + α₂ + α₃ - h₄ - 2) - (α₂ + α₃ - 1 - Q.h) + 1 - b - K with hκ
  set H := (1 - PowerSeries.X) ^ b * (PowerSeries.X ^ K * G) with hHdef
  have hH : H ∈ SubexpPS :=
    SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp b)
      (SubexpPS.mul_mem (SubexpPS.pow_mem X_mem_subexp K) hG)
  obtain ⟨m, r, hr, hm⟩ := hrel κ b
  -- a relation of order `≥ 1`
  obtain ⟨m', r', hr', hm'1, hrel'⟩ : ∃ (m' : ℕ) (r' : ℕ → PowerSeries ℂ),
      (∀ k, r' k ∈ ratRing 0) ∧ 1 ≤ m' ∧
      (DOp κ b)^[m'] H = ∑ k ∈ Finset.range m', r' k * (DOp κ b)^[k] H := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · have H0 : H = 0 := by simpa using hm
      exact ⟨1, fun _ => 0, fun _ => Subalgebra.zero_mem _, le_rfl, by simp [H0]⟩
    · exact ⟨m, r, hr, hpos, hm⟩
  choose c hc hcev using fun k => exists_subexp_of_mem_ratRing_zero (hr' k)
  refine ⟨m', hm'1, fun k => -c k, fun i _ => SubexpPS.neg_mem (hc i), fun t ht => ?_⟩
  have hFE : prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h)
      =ᶠ[𝓝 t] Ev κ b H :=
    Filter.eventually_of_mem (isOpen_overlapDomain.mem_nhds ht) fun y hy =>
      prodFun_eq_Ev Y₁ Y₂ f w₁ w₂ w₃ _ _ b K hG hy
  have hu : ‖Complex.exp t‖ < 1 := by
    rw [Complex.norm_exp]; exact Real.exp_lt_one_iff.mpr ht.1
  rw [hFE.iteratedDeriv_eq, Finset.sum_congr rfl fun i _ => by rw [hFE.iteratedDeriv_eq],
    iteratedDeriv_Ev κ b hH m' t ht, hrel',
    Ev_sum_mul κ b _ (fun k _ => subexp_of_mem_ratRing_zero (hr' k))
      (fun k _ => DOp_iterate_mem κ b hH k) ht, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [iteratedDeriv_Ev κ b hH k t ht, psEval_neg, hcev k _ hu]
  simp only [xt]
  ring

/-- **Huang's expansion (3.3) of a product at the iterate point, unconditional** for strongly
rational `V`: on the overlap domain the product is a finite sum of log-Frobenius functions. -/
theorem prod_frobenius_expansion_holds (hV : StronglyRational W)
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
      (∀ j, (FrobeniusLog.indicial s c).IsRoot (lam j)) ∧
      ∀ t ∈ overlapDomain,
        prodFun Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
          = ∑ j, a j * logFun (lam j) (p j) t :=
  prod_frobenius_expansion hV (productODEAtIterPoint_holds hV) i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃ hf

/-- The same on the real overlap `u = z₁ − z₂ ∈ (0, 1)`, `z₂ = 1`, unconditional:
`⟨f, 𝒴₁(w₁, 1+u)𝒴₂(w₂, 1)w₃⟩ = Σⱼ aⱼ u^{λⱼ} Σₙ uⁿ pⱼₙ(log u)`. -/
theorem prod_frobenius_expansion_real_holds (hV : StronglyRational W)
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
          = ∑ j, a j * logFun (lam j) (p j) (Real.log x) :=
  prod_frobenius_expansion_real hV (productODEAtIterPoint_holds hV) i₁ i₂ i₃ i₄ iQ hY₁ hY₂
    h₁ h₂ h₃ hf

end Assembly

end VOA.Huang.HuangODEIterPoint
