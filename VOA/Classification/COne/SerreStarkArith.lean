/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Serre–Stark S5-7b: arithmetic functions supported on prime powers

* `sqPowAF p a`: the arithmetic function `p^{2k} ↦ a k` (zero elsewhere); `LSeries_sqPowAF`.
* `prod_apply_ne_zero_prime`, `prod_apply_prod_pow`: a Dirichlet product of functions supported
  on powers of distinct primes is evaluated factorwise at `∏ qᵢ^{kᵢ}`.
-/

open ArithmeticFunction

noncomputable section

namespace VOA.Classification.COne

namespace SSHecke

/-- The arithmetic function `p^{2k} ↦ a k`, zero off even powers of `p`. -/
def sqPowAF (p : ℕ) (a : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if p ^ (2 * (n.factorization p / 2)) = n then a (n.factorization p / 2) else 0, by
    simp⟩

theorem sqPowAF_apply (p : ℕ) (a : ℕ → ℂ) (n : ℕ) :
    sqPowAF p a n =
      if p ^ (2 * (n.factorization p / 2)) = n then a (n.factorization p / 2) else 0 := rfl

theorem sqPowAF_apply_pow {p : ℕ} (hp : p.Prime) (a : ℕ → ℂ) (k : ℕ) :
    sqPowAF p a (p ^ (2 * k)) = a k := by
  rw [sqPowAF_apply, hp.factorization_pow, Finsupp.single_eq_same,
    show 2 * k / 2 = k by omega, if_pos rfl]

theorem sqPowAF_support {p : ℕ} (a : ℕ → ℂ) {n : ℕ} (h : sqPowAF p a n ≠ 0) :
    ∃ k, n = p ^ k := by
  rw [sqPowAF_apply] at h
  split_ifs at h with h1
  · exact ⟨_, h1.symm⟩
  · exact absurd rfl h

/-! ## Products of functions supported on powers of distinct primes -/

section Prod

variable {ι' : Type*} [DecidableEq ι'] (q : ι' → ℕ) (hq : ∀ i, (q i).Prime)
  (hinj : Function.Injective q)

include hq in
/-- Support of a product: every prime factor of a point of the support is one of the `q i`. -/
theorem prod_apply_ne_zero_prime (s : Finset ι') (F : ι' → ArithmeticFunction ℂ)
    (hF : ∀ i n, F i n ≠ 0 → ∃ k, n = q i ^ k) {n : ℕ} (hn : (∏ i ∈ s, F i) n ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) : ∃ i ∈ s, ℓ = q i := by
  induction s using Finset.induction_on generalizing n with
  | empty =>
    simp only [Finset.prod_empty, ArithmeticFunction.one_apply] at hn
    split_ifs at hn with h1
    · subst h1; exact absurd (Nat.le_of_dvd one_pos hℓn) (by have := hℓ.two_le; omega)
    · exact absurd rfl hn
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ArithmeticFunction.mul_apply] at hn
    obtain ⟨⟨d, e⟩, hde, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [Nat.mem_divisorsAntidiagonal] at hde
    have hd : F a d ≠ 0 := left_ne_zero_of_mul hne
    have he : (∏ i ∈ s, F i) e ≠ 0 := right_ne_zero_of_mul hne
    rw [← hde.1] at hℓn
    rcases (Nat.Prime.dvd_mul hℓ).1 hℓn with h | h
    · obtain ⟨k, rfl⟩ := hF a d hd
      exact ⟨a, Finset.mem_insert_self a s, (Nat.prime_dvd_prime_iff_eq hℓ (hq a)).1
        (hℓ.dvd_of_dvd_pow h)⟩
    · obtain ⟨i, hi, rfl⟩ := ih he h
      exact ⟨i, Finset.mem_insert_of_mem hi, rfl⟩

include hq hinj in
/-- **Factorwise evaluation.** `(∏ F_i)(∏ q_i^{k_i}) = ∏ F_i(q_i^{k_i})`. -/
theorem prod_apply_prod_pow (s : Finset ι') (F : ι' → ArithmeticFunction ℂ)
    (hF : ∀ i n, F i n ≠ 0 → ∃ k, n = q i ^ k) (k : ι' → ℕ) :
    (∏ i ∈ s, F i) (∏ i ∈ s, q i ^ k i) = ∏ i ∈ s, F i (q i ^ k i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      ArithmeticFunction.mul_apply, ← ih]
    set m := ∏ i ∈ s, q i ^ k i with hm
    have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hq i).ne_zero
    have hqa0 : q a ^ k a ≠ 0 := pow_ne_zero _ (hq a).ne_zero
    -- `q a ∤ m`
    have hqm : ¬ q a ∣ m := by
      intro h
      obtain ⟨i, hi, hia⟩ := (Prime.dvd_finsetProd_iff (hq a).prime _).1 h
      have := (Nat.prime_dvd_prime_iff_eq (hq a) (hq i)).1 ((hq a).dvd_of_dvd_pow hia)
      exact ha (hinj this ▸ hi)
    refine Finset.sum_eq_single (q a ^ k a, m) (fun ⟨d, e⟩ hde hne => ?_) (fun h => ?_)
    · rw [Nat.mem_divisorsAntidiagonal] at hde
      by_contra hprod
      have hd : F a d ≠ 0 := left_ne_zero_of_mul hprod
      have he : (∏ i ∈ s, F i) e ≠ 0 := right_ne_zero_of_mul hprod
      obtain ⟨b, rfl⟩ := hF a d hd
      -- `q a ∤ e`
      have hqe : ¬ q a ∣ e := by
        intro h
        obtain ⟨i, hi, hia⟩ := prod_apply_ne_zero_prime q hq s F hF he (hq a) h
        exact ha (hinj hia ▸ hi)
      have he0 : e ≠ 0 := by
        rintro rfl
        have := hde.1
        rw [mul_zero] at this
        exact mul_ne_zero hqa0 hm0 this.symm
      -- compare `q a`-adic valuations
      have hv := congrArg (fun n => n.factorization (q a)) hde.1
      simp only at hv
      rw [Nat.factorization_mul (pow_ne_zero _ (hq a).ne_zero) he0,
        Nat.factorization_mul hqa0 hm0, Finsupp.add_apply, Finsupp.add_apply,
        (hq a).factorization_pow, (hq a).factorization_pow, Finsupp.single_eq_same,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hqe,
        Nat.factorization_eq_zero_of_not_dvd hqm] at hv
      simp only [add_zero] at hv
      subst hv
      have : e = m := Nat.eq_of_mul_eq_mul_left (pos_of_ne_zero hqa0) hde.1
      exact hne (by rw [this])
    · exfalso; apply h
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨rfl, mul_ne_zero hqa0 hm0⟩

end Prod

/-! ## L-series of the special arithmetic functions -/

theorem term_sqPowAF_pow {p : ℕ} (hp : p.Prime) (a : ℕ → ℂ) (z : ℂ) (k : ℕ) :
    LSeries.term (sqPowAF p a) z (p ^ (2 * k)) = a k * ((p : ℂ) ^ (-(2 * z))) ^ k := by
  have hpk : p ^ (2 * k) ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hpk, sqPowAF_apply_pow hp]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  rw [div_eq_mul_inv]
  congr 1
  rw [← Complex.cpow_nat_mul, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
    ← Complex.cpow_neg]
  congr 1
  push_cast; ring

/-- The L-series of `sqPowAF p a` is the power series `Σ_k a_k (p^{−2z})^k`. -/
theorem LSeriesHasSum_sqPowAF {p : ℕ} (hp : p.Prime) (a : ℕ → ℂ) (z : ℂ) {A : ℂ}
    (hA : HasSum (fun k => a k * ((p : ℂ) ^ (-(2 * z))) ^ k) A) :
    LSeriesHasSum (sqPowAF p a) z A := by
  have hinj : Function.Injective fun k : ℕ => p ^ (2 * k) := fun x y h => by
    have := Nat.pow_right_injective hp.two_le h
    omega
  unfold LSeriesHasSum
  rw [← hinj.hasSum_iff]
  · convert hA using 1
    funext k
    exact term_sqPowAF_pow hp a z k
  · intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0.ne']
      rw [sqPowAF_apply, if_neg, zero_div]
      intro h
      exact hn ⟨_, h⟩

/-- The arithmetic function `v² ↦ χ(v)`. -/
def sqAF (χ : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ≠ 0 ∧ Nat.sqrt n ^ 2 = n then χ (Nat.sqrt n) else 0, by simp⟩

theorem sqAF_apply_sq (χ : ℕ → ℂ) {v : ℕ} (hv : v ≠ 0) : sqAF χ (v ^ 2) = χ v := by
  have h : Nat.sqrt (v ^ 2) = v := by rw [sq, Nat.sqrt_eq]
  simp [sqAF, h, hv]

theorem sqAF_support (χ : ℕ → ℂ) {n : ℕ} (h : sqAF χ n ≠ 0) :
    ∃ v, v ≠ 0 ∧ n = v ^ 2 ∧ sqAF χ n = χ v := by
  simp only [sqAF, ArithmeticFunction.coe_mk] at h ⊢
  split_ifs at h ⊢ with h1
  · refine ⟨Nat.sqrt n, fun h0 => h1.1 ?_, h1.2.symm, rfl⟩
    rw [← h1.2, h0]; rfl
  · exact absurd rfl h

theorem LSeries_sqAF (χ : ℕ → ℂ) (z : ℂ) : LSeries (sqAF χ) z = LSeries χ (2 * z) := by
  have hinj : Function.Injective fun v : ℕ => v ^ 2 := Nat.pow_left_injective two_ne_zero
  rw [LSeries, ← hinj.tsum_eq, LSeries]
  · refine tsum_congr fun v => ?_
    rcases Nat.eq_zero_or_pos v with h0 | h0
    · subst h0; simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero (pow_ne_zero _ h0.ne'), LSeries.term_of_ne_zero h0.ne',
        sqAF_apply_sq χ h0.ne', Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
      push_cast; rfl
  · intro n hn
    by_contra hc
    apply hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0.ne']
      by_cases h : sqAF χ n = 0
      · rw [h, zero_div]
      · obtain ⟨v, -, rfl, -⟩ := sqAF_support χ h
        exact absurd ⟨v, rfl⟩ hc

/-- Dilation `n ↦ f(n/D)` (zero unless `D ∣ n`). -/
def dil (D : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := if D ∣ n then f (n / D) else 0

theorem LSeries_dil {D : ℕ} (hD : 0 < D) (f : ℕ → ℂ) (z : ℂ) :
    LSeries (dil D f) z = (D : ℂ) ^ (-z) * LSeries f z := by
  have hinj : Function.Injective fun m : ℕ => D * m := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hD h
  rw [LSeries, ← hinj.tsum_eq, LSeries, ← tsum_mul_left]
  · refine tsum_congr fun m => ?_
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp [LSeries.term_zero]
    · have hDm : D * m ≠ 0 := Nat.mul_ne_zero hD.ne' h0.ne'
      rw [LSeries.term_of_ne_zero hDm, LSeries.term_of_ne_zero h0.ne', dil, if_pos (Dvd.intro m rfl),
        Nat.mul_div_cancel_left _ hD, Nat.cast_mul, Complex.natCast_mul_natCast_cpow,
        Complex.cpow_neg]
      have h1 : (D : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hD.ne'))
      have h2 : (m : ℂ) ^ z ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 h0.ne'))
      field_simp
  · intro n hn
    by_contra hc
    apply hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0.ne', dil, if_neg, zero_div]
      rintro ⟨m, rfl⟩; exact hc ⟨m, rfl⟩

/-- Twist by `n^{−i}`: `L(twI f, x) = L(f, x + i)`. -/
def twI (f : ℕ → ℂ) (n : ℕ) : ℂ := f n * (n : ℂ) ^ (-Complex.I)

theorem LSeries_twI (f : ℕ → ℂ) (x : ℂ) : LSeries (twI f) x = LSeries f (x + Complex.I) := by
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [LSeries.term_zero]
  · have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [LSeries.term_of_ne_zero h0.ne', LSeries.term_of_ne_zero h0.ne', twI,
      Complex.cpow_add _ _ hn, Complex.cpow_neg]
    have h1 : (n : ℂ) ^ x ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn)
    have h2 : (n : ℂ) ^ Complex.I ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn)
    field_simp


theorem coe_one_AF : ⇑(1 : ArithmeticFunction ℂ) = LSeries.delta := by
  funext n; simp [ArithmeticFunction.one_apply, LSeries.delta]

theorem LSeriesSummable_one_AF (z : ℂ) : LSeriesSummable ⇑(1 : ArithmeticFunction ℂ) z := by
  rw [coe_one_AF]
  unfold LSeriesSummable
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  rw [LSeries.term_delta, if_neg (by simpa using hn)]

/-- The L-series of a finite Dirichlet product is the product of the L-series. -/
theorem LSeries_prod_AF {ι' : Type*} [DecidableEq ι'] (s : Finset ι')
    (F : ι' → ArithmeticFunction ℂ) (z : ℂ) (hF : ∀ i ∈ s, LSeriesSummable ⇑(F i) z) :
    LSeriesSummable ⇑(∏ i ∈ s, F i) z ∧
      LSeries ⇑(∏ i ∈ s, F i) z = ∏ i ∈ s, LSeries ⇑(F i) z := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using LSeriesSummable_one_AF z, ?_⟩
    rw [Finset.prod_empty, Finset.prod_empty, coe_one_AF, LSeries_delta, Pi.one_apply]
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have ha' := hF a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨LSeriesSummable_mul ha' h1, by rw [LSeries_mul' ha' h1, h2]⟩


theorem term_sqAF_sq (χ : ℕ → ℂ) (z : ℂ) (v : ℕ) :
    LSeries.term (sqAF χ) z (v ^ 2) = LSeries.term χ (2 * z) v := by
  rcases Nat.eq_zero_or_pos v with h0 | h0
  · subst h0; simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero (pow_ne_zero _ h0.ne'), LSeries.term_of_ne_zero h0.ne',
      sqAF_apply_sq χ h0.ne', Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    push_cast; rfl

theorem LSeriesSummable_sqAF {χ : ℕ → ℂ} {z : ℂ} (h : LSeriesSummable χ (2 * z)) :
    LSeriesSummable (sqAF χ) z := by
  have hinj : Function.Injective fun v : ℕ => v ^ 2 := Nat.pow_left_injective two_ne_zero
  unfold LSeriesSummable at h ⊢
  refine (hinj.summable_iff (f := LSeries.term (sqAF χ) z) fun n hn => ?_).1 ?_
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0.ne']
      by_cases hs : sqAF χ n = 0
      · rw [hs, zero_div]
      · obtain ⟨v, -, rfl, -⟩ := sqAF_support χ hs
        exact absurd ⟨v, rfl⟩ hn
  · convert h using 1
    funext v
    exact term_sqAF_sq χ z v

/-- At an `N`-smooth `n`, convolution with `sqAF χ` (for `χ` supported on integers prime to `N`,
`χ 1 = 1`) does nothing. -/
theorem mul_sqAF_smooth {χ : ℕ → ℂ} {N : ℕ} (hχ1 : χ 1 = 1)
    (hχ : ∀ v, χ v ≠ 0 → v.Coprime N) (F : ArithmeticFunction ℂ) {n : ℕ} (hn : n ≠ 0)
    (hsm : ∀ ℓ, ℓ.Prime → ℓ ∣ n → ℓ ∣ N) : (F * sqAF χ) n = F n := by
  rw [ArithmeticFunction.mul_apply]
  rw [Finset.sum_eq_single (n, 1)]
  · simp only
    rw [show (1 : ℕ) = 1 ^ 2 by norm_num, sqAF_apply_sq χ one_ne_zero, hχ1, mul_one]
  · rintro ⟨d, e⟩ hde hne
    rw [Nat.mem_divisorsAntidiagonal] at hde
    by_contra hprod
    have he : sqAF χ e ≠ 0 := right_ne_zero_of_mul hprod
    obtain ⟨v, hv0, rfl, hval⟩ := sqAF_support χ he
    have hcop := hχ v (by rw [← hval]; exact he)
    have hv1 : v = 1 := by
      by_contra hv1
      obtain ⟨ℓ, hℓ, hℓv⟩ := Nat.exists_prime_and_dvd hv1
      have hℓn : ℓ ∣ n := by
        rw [← hde.1]; exact Dvd.dvd.mul_left (Dvd.dvd.pow hℓv two_ne_zero) _
      exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 (Nat.Coprime.coprime_dvd_left hℓv hcop)
        (hsm ℓ hℓ hℓn)
    subst hv1
    apply hne
    have : d = n := by simpa using hde.1
    rw [this]; rfl
  · intro h
    exfalso; apply h
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨mul_one n, hn⟩


theorem term_twI (f : ℕ → ℂ) (x : ℂ) (n : ℕ) :
    LSeries.term (twI f) x n = LSeries.term f (x + Complex.I) n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp [LSeries.term_zero]
  · have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h0.ne'
    rw [LSeries.term_of_ne_zero h0.ne', LSeries.term_of_ne_zero h0.ne', twI,
      Complex.cpow_add _ _ hn, Complex.cpow_neg]
    have h1 : (n : ℂ) ^ x ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn)
    have h2 : (n : ℂ) ^ Complex.I ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hn)
    field_simp

theorem LSeriesSummable_twI {f : ℕ → ℂ} {x : ℂ} :
    LSeriesSummable (twI f) x ↔ LSeriesSummable f (x + Complex.I) := by
  unfold LSeriesSummable
  rw [show LSeries.term (twI f) x = LSeries.term f (x + Complex.I) from
    funext (term_twI f x)]

theorem LSeriesSummable_dil {D : ℕ} (hD : 0 < D) {f : ℕ → ℂ} {z : ℂ}
    (hf : LSeriesSummable f z) : LSeriesSummable (dil D f) z := by
  have hinj : Function.Injective fun m : ℕ => D * m := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hD h
  unfold LSeriesSummable at hf ⊢
  refine (hinj.summable_iff (f := LSeries.term (dil D f) z) fun n hn => ?_).1 ?_
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0.ne', dil, if_neg, zero_div]
      rintro ⟨m, rfl⟩; exact hn ⟨m, rfl⟩
  · have : (LSeries.term (dil D f) z ∘ fun m => D * m) =
        fun m => (D : ℂ) ^ (-z) * LSeries.term f z m := by
      funext m
      simp only [Function.comp_apply]
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp [LSeries.term_zero]
      · have hDm : D * m ≠ 0 := Nat.mul_ne_zero hD.ne' h0.ne'
        rw [LSeries.term_of_ne_zero hDm, LSeries.term_of_ne_zero h0.ne', dil,
          if_pos (Dvd.intro m rfl), Nat.mul_div_cancel_left _ hD, Nat.cast_mul,
          Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
        have h1 : (D : ℂ) ^ z ≠ 0 :=
          Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hD.ne'))
        have h2 : (m : ℂ) ^ z ≠ 0 :=
          Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 h0.ne'))
        field_simp
    rw [this]
    exact hf.mul_left _


end SSHecke

end VOA.Classification.COne
