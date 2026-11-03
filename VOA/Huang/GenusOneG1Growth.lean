import VOA.Huang.GenusOneWardMixedFormal
import VOA.Modularity.SubexpClosure
import VOA.Modularity.OnePointDescent

/-!
# Two-variable subexponential series and Euler systems in `ℂ⟦u⟧⟦t⟧`

`Geo2 f`: the coefficients of `f ∈ ℂ⟦u⟧⟦t⟧` are `O(a^{n+k})` for EVERY `a > 1`.
These series form a `ℂ`-subalgebra `Sub2` containing the genus-one kernels `eis j`
(Eisenstein series in `q = ut`) and `piK m` (the spatial kernels).

The analytic core is `geo2_of_euler_system`: if finitely many series `f_i` satisfy
`Θ_λ f_i = Σ_l C_{il} f_l` (where `Θ_λ` multiplies the coefficient of `u^n t^k` by
`λ + n`) with `C_{il} ∈ Sub2`, and every fixed-`n` row of every `f_i` is
`O(b^k)` for every `b > 1`, then every `f_i ∈ Sub2`. The proof is a sup-majorant
over the outer level with a self-improving bound: for `n` large the operator
`(λ + n)^{-1} C` is a contraction on the weighted sup norm of the level-`n` row,
including the coefficients of `C` of outer degree zero (which mix the level-`n`
row with itself). No ODE theory, no matrix inversion and no analytic continuation
is used.
-/
noncomputable section
namespace VOA.Huang.GenusOneWard
open VOA PowerSeries
open scoped BigOperators

/-- Coefficients `O(a^{n+k})` for every `a > 1`. -/
def Geo2 (f : R2) : Prop :=
  ∀ a : ℝ, 1 < a → ∃ C : ℝ, ∀ n k : ℕ, ‖c2 f n k‖ ≤ C * a ^ (n + k)

theorem Geo2.const_nonneg {f : R2} {a C : ℝ} (h : ∀ n k : ℕ, ‖c2 f n k‖ ≤ C * a ^ (n + k)) :
    0 ≤ C := by
  have := h 0 0
  simp only [add_zero, pow_zero, mul_one] at this
  exact le_trans (norm_nonneg _) this

/-- `(n+1)(k+1) ≤ E b^{n+k}` for every `b > 1`. -/
theorem exists_sq_le_pow {b : ℝ} (hb : 1 < b) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n k : ℕ, ((n : ℝ) + 1) * ((k : ℝ) + 1) ≤ E * b ^ (n + k) := by
  have hs : Subexponential (fun N : ℕ => (N : ℝ) ^ 2 + 2 * (N : ℝ) ^ 1 + 1) :=
    ((subexponential_pow 2).add ((subexponential_pow 1).const_mul (by norm_num))).add
      (subexponential_const 1)
  obtain ⟨E, hE⟩ := hs b hb
  have hE0 : 0 ≤ E := by
    have := hE 0
    simp at this
    linarith
  refine ⟨E, hE0, fun n k => ?_⟩
  have h := hE (n + k)
  push_cast at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem geo2_zero : Geo2 0 := fun a _ => ⟨0, fun n k => by simp⟩

theorem Geo2.add {f g : R2} (hf : Geo2 f) (hg : Geo2 g) : Geo2 (f + g) := fun a ha => by
  obtain ⟨C, hC⟩ := hf a ha
  obtain ⟨D, hD⟩ := hg a ha
  exact ⟨C + D, fun n k => by
    rw [c2_add]
    calc ‖c2 f n k + c2 g n k‖ ≤ ‖c2 f n k‖ + ‖c2 g n k‖ := norm_add_le _ _
      _ ≤ C * a ^ (n + k) + D * a ^ (n + k) := add_le_add (hC n k) (hD n k)
      _ = (C + D) * a ^ (n + k) := by ring⟩

theorem Geo2.smul {f : R2} (hf : Geo2 f) (c : ℂ) : Geo2 (c • f) := fun a ha => by
  obtain ⟨C, hC⟩ := hf a ha
  exact ⟨‖c‖ * C, fun n k => by
    rw [c2_smul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC n k) (norm_nonneg c)⟩

theorem geo2_algebraMap (c : ℂ) : Geo2 (algebraMap ℂ R2 c) := fun a ha =>
  ⟨‖c‖, fun n k => by
    rw [c2_algebraMap]
    have h1 : (1 : ℝ) ≤ a ^ (n + k) := one_le_pow₀ ha.le
    split_ifs
    · nlinarith [norm_nonneg c]
    · rw [norm_zero]; positivity⟩

theorem sum_antidiagonal_pow_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, ρ ^ p.1 ≤ (1 - ρ)⁻¹ := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc ∑ i ∈ Finset.range (n + 1), ρ ^ i ≤ ∑' i : ℕ, ρ ^ i :=
        (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun i _ => pow_nonneg h0 i)
    _ = (1 - ρ)⁻¹ := tsum_geometric_of_lt_one h0 h1

theorem Geo2.mul {f g : R2} (hf : Geo2 f) (hg : Geo2 g) : Geo2 (f * g) := by
  intro a ha
  set b := Real.sqrt a with hbdef
  have hb : 1 < b := by
    rw [hbdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one ha
  have hbb : b * b = a := Real.mul_self_sqrt (by linarith)
  obtain ⟨C, hC⟩ := hf b hb
  obtain ⟨D, hD⟩ := hg b hb
  have hC0 := Geo2.const_nonneg hC
  have hD0 := Geo2.const_nonneg hD
  obtain ⟨E, hE0, hE⟩ := exists_sq_le_pow hb
  refine ⟨C * D * E, fun n k => ?_⟩
  rw [c2_mul]
  have hterm : ∀ p ∈ Finset.antidiagonal n, ∀ r ∈ Finset.antidiagonal k,
      ‖c2 f p.1 r.1 * c2 g p.2 r.2‖ ≤ C * D * b ^ (n + k) := by
    intro p hp r hr
    rw [Finset.mem_antidiagonal] at hp hr
    rw [norm_mul]
    calc ‖c2 f p.1 r.1‖ * ‖c2 g p.2 r.2‖
        ≤ (C * b ^ (p.1 + r.1)) * (D * b ^ (p.2 + r.2)) :=
          mul_le_mul (hC _ _) (hD _ _) (norm_nonneg _) (by positivity)
      _ = C * D * b ^ (n + k) := by
          rw [← hp, ← hr, show p.1 + p.2 + (r.1 + r.2) = (p.1 + r.1) + (p.2 + r.2) by ring,
            pow_add]
          ring
  calc ‖∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k, c2 f p.1 r.1 * c2 g p.2 r.2‖
      ≤ ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k,
          ‖c2 f p.1 r.1 * c2 g p.2 r.2‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k, C * D * b ^ (n + k) :=
        Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun r hr => hterm p hp r hr
    _ = ((n : ℝ) + 1) * ((k : ℝ) + 1) * (C * D * b ^ (n + k)) := by
        simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (E * b ^ (n + k)) * (C * D * b ^ (n + k)) :=
        mul_le_mul_of_nonneg_right (hE n k) (by positivity)
    _ = C * D * E * a ^ (n + k) := by
        rw [← hbb, mul_pow]; ring

/-- The subalgebra of two-variable subexponential series. -/
def Sub2 : Subalgebra ℂ R2 where
  carrier := {f | Geo2 f}
  mul_mem' := fun hf hg => Geo2.mul hf hg
  one_mem' := by
    have h := geo2_algebraMap 1
    rwa [map_one] at h
  add_mem' := fun hf hg => Geo2.add hf hg
  zero_mem' := geo2_zero
  algebraMap_mem' := geo2_algebraMap

@[simp] theorem mem_Sub2 {f : R2} : f ∈ Sub2 ↔ Geo2 f := Iff.rfl

/-- A polynomial bound in the total degree suffices. -/
theorem geo2_of_poly {f : R2} (C : ℝ) (p : ℕ)
    (h : ∀ n k : ℕ, ‖c2 f n k‖ ≤ C * ((n + k : ℕ) : ℝ) ^ p + C) : Geo2 f := by
  intro a ha
  have hs : Subexponential (fun N : ℕ => C * (N : ℝ) ^ p + C) := by
    have h0 : 0 ≤ max C 0 := le_max_right _ _
    refine Subexponential.of_le (b := fun N : ℕ => max C 0 * (N : ℝ) ^ p + max C 0)
      (fun N => ?_) (((subexponential_pow p).const_mul h0).add (subexponential_const _))
    have : C * (N : ℝ) ^ p ≤ max C 0 * (N : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith [le_max_left C 0]
  obtain ⟨D, hD⟩ := hs a ha
  exact ⟨D, fun n k => (h n k).trans (hD (n + k))⟩

theorem eis_mem_Sub2 (j : ℕ) : eis j ∈ Sub2 := by
  intro a ha
  obtain ⟨C, hC⟩ := subexponential_zhuG j a ha
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨C, fun n k => ?_⟩
  simp only [eis, c2_mk2]
  split_ifs with h
  · subst h
    calc ‖zhuG j n‖ ≤ C * a ^ n := hC n
      _ ≤ C * a ^ (n + n) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ha.le (by omega)) hC0
  · rw [norm_zero]; positivity

theorem piK_mem_Sub2 (m : ℕ) : piK m ∈ Sub2 := by
  apply geo2_of_poly 2 m
  intro n k
  rw [c2_piK]
  have hpow : ∀ d : ℕ, d ≤ n + k → ‖((d : ℂ)) ^ m / (m.factorial : ℂ)‖ ≤
      ((n + k : ℕ) : ℝ) ^ m := by
    intro d hd
    rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    have hf : (1 : ℝ) ≤ m.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    calc (d : ℝ) ^ m / (m.factorial : ℝ) ≤ (d : ℝ) ^ m := div_le_self (by positivity) hf
      _ ≤ ((n + k : ℕ) : ℝ) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hd) m
  have hpow' : ∀ d : ℕ, d ≤ n + k → ‖(-((d : ℂ))) ^ m / (m.factorial : ℂ)‖ ≤
      ((n + k : ℕ) : ℝ) ^ m := by
    intro d hd
    rw [neg_pow, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hpow d hd
  have h1 : ‖(if n < k ∧ (k - n) ∣ n then (((k - n : ℕ) : ℂ) ^ m / (m.factorial : ℂ))
      else 0)‖ ≤ ((n + k : ℕ) : ℝ) ^ m := by
    split_ifs
    · exact hpow _ (by omega)
    · rw [norm_zero]; positivity
  have h2 : ‖(if k < n ∧ (n - k) ∣ k then ((-((n - k : ℕ) : ℂ)) ^ m / (m.factorial : ℂ))
      else 0)‖ ≤ ((n + k : ℕ) : ℝ) ^ m := by
    split_ifs
    · exact hpow' _ (by omega)
    · rw [norm_zero]; positivity
  have h0 : (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) ^ m := by positivity
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ ((n + k : ℕ) : ℝ) ^ m + ((n + k : ℕ) : ℝ) ^ m := add_le_add h1 h2
    _ ≤ 2 * ((n + k : ℕ) : ℝ) ^ m + 2 := by linarith

/-! ## The Euler-system majorant -/

section System
variable {ι : Type*} [Fintype ι]

/-- One contraction step of the majorant at a fixed outer level `n`. -/
theorem euler_step {lam : ℂ} {f : ι → R2} {Cm : ι → ι → R2}
    (hsys : ∀ i, thetaR2 lam (f i) = ∑ l, Cm i l * f l)
    {a ρ D X M : ℝ} (ha : 1 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hD0 : 0 ≤ D)
    (hCm : ∀ i l p q, ‖c2 (Cm i l) p q‖ ≤ D * (ρ * a) ^ (p + q))
    (hM0 : 0 ≤ M) (hMX : M ≤ X) (n : ℕ)
    (hlow : ∀ m < n, ∀ i k, ‖c2 (f i) m k‖ ≤ M * a ^ (m + k))
    (hX : ∀ i k, ‖c2 (f i) n k‖ ≤ X * a ^ (n + k))
    (hn : 2 * (Fintype.card ι * D * ((1 - ρ)⁻¹ * (1 - ρ)⁻¹)) + 1 ≤ ‖lam + n‖) :
    ∀ i k, ‖c2 (f i) n k‖ ≤ X / 2 * a ^ (n + k) := by
  intro i k
  have ha0 : 0 < a := by linarith
  have hX0 : 0 ≤ X := le_trans hM0 hMX
  set G := (1 - ρ)⁻¹ with hG
  have hG0 : 0 ≤ G := inv_nonneg.mpr (by linarith)
  have heq : (lam + n) * c2 (f i) n k = ∑ l, ∑ p ∈ Finset.antidiagonal n,
      ∑ r ∈ Finset.antidiagonal k, c2 (Cm i l) p.1 r.1 * c2 (f l) p.2 r.2 := by
    have h := congrArg (fun g => c2 g n k) (hsys i)
    simp only [thetaR2, c2_mk2, c2_sum, c2_mul] at h
    exact h
  have hterm : ∀ l, ∀ p ∈ Finset.antidiagonal n, ∀ r ∈ Finset.antidiagonal k,
      ‖c2 (Cm i l) p.1 r.1 * c2 (f l) p.2 r.2‖ ≤
        (D * X * a ^ (n + k)) * (ρ ^ p.1 * ρ ^ r.1) := by
    intro l p hp r hr
    rw [Finset.mem_antidiagonal] at hp hr
    have hf : ‖c2 (f l) p.2 r.2‖ ≤ X * a ^ (p.2 + r.2) := by
      by_cases h2 : p.2 = n
      · rw [h2]; exact hX l r.2
      · exact (hlow p.2 (by omega) l r.2).trans
          (mul_le_mul_of_nonneg_right hMX (by positivity))
    rw [norm_mul]
    calc ‖c2 (Cm i l) p.1 r.1‖ * ‖c2 (f l) p.2 r.2‖
        ≤ (D * (ρ * a) ^ (p.1 + r.1)) * (X * a ^ (p.2 + r.2)) :=
          mul_le_mul (hCm i l _ _) hf (norm_nonneg _) (by positivity)
      _ = (D * X * a ^ (n + k)) * (ρ ^ p.1 * ρ ^ r.1) := by
          rw [← hp, ← hr, mul_pow, pow_add, pow_add, pow_add, pow_add]
          ring
  have hbound : ‖(lam + n) * c2 (f i) n k‖ ≤
      (Fintype.card ι * D * (G * G)) * (X * a ^ (n + k)) := by
    rw [heq]
    calc ‖∑ l, ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k,
          c2 (Cm i l) p.1 r.1 * c2 (f l) p.2 r.2‖
        ≤ ∑ l, ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k,
          ‖c2 (Cm i l) p.1 r.1 * c2 (f l) p.2 r.2‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
      _ ≤ ∑ l : ι, ∑ p ∈ Finset.antidiagonal n, ∑ r ∈ Finset.antidiagonal k,
          (D * X * a ^ (n + k)) * (ρ ^ p.1 * ρ ^ r.1) :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun p hp =>
            Finset.sum_le_sum fun r hr => hterm l p hp r hr
      _ = ∑ l : ι, (D * X * a ^ (n + k)) * ((∑ p ∈ Finset.antidiagonal n, ρ ^ p.1) *
          (∑ r ∈ Finset.antidiagonal k, ρ ^ r.1)) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ l : ι, (D * X * a ^ (n + k)) * (G * G) := by
          refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul (sum_antidiagonal_pow_le hρ0 hρ1 n)
            (sum_antidiagonal_pow_le hρ0 hρ1 k)
            (Finset.sum_nonneg fun r _ => pow_nonneg hρ0 _) hG0
      _ = (Fintype.card ι * D * (G * G)) * (X * a ^ (n + k)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  rw [norm_mul] at hbound
  have hA0 : 0 ≤ Fintype.card ι * D * (G * G) := by positivity
  have hY0 : 0 ≤ X * a ^ (n + k) := by positivity
  have hc0 := norm_nonneg (c2 (f i) n k)
  have : ‖c2 (f i) n k‖ * (2 * (Fintype.card ι * D * (G * G)) + 1) ≤
      (Fintype.card ι * D * (G * G)) * (X * a ^ (n + k)) := by
    calc ‖c2 (f i) n k‖ * (2 * (Fintype.card ι * D * (G * G)) + 1)
        ≤ ‖c2 (f i) n k‖ * ‖lam + n‖ := mul_le_mul_of_nonneg_left hn hc0
      _ = ‖lam + n‖ * ‖c2 (f i) n k‖ := mul_comm _ _
      _ ≤ _ := hbound
  nlinarith

/-- **Euler systems with `Sub2` coefficients have `Sub2` solutions**, given
fixed-level row bounds. -/
theorem geo2_of_euler_system {lam : ℂ} {f : ι → R2} {Cm : ι → ι → R2}
    (hC : ∀ i l, Cm i l ∈ Sub2)
    (hsys : ∀ i, thetaR2 lam (f i) = ∑ l, Cm i l * f l)
    (hrow : ∀ i n, ∀ b : ℝ, 1 < b → ∃ B : ℝ, ∀ k, ‖c2 (f i) n k‖ ≤ B * b ^ k) :
    ∀ i, f i ∈ Sub2 := by
  intro i₀ a ha
  have ha0 : 0 < a := by linarith
  set b := Real.sqrt a with hbdef
  have hb : 1 < b := by
    rw [hbdef, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt zero_le_one ha
  have hb0 : 0 < b := by linarith
  have hbb : b * b = a := Real.mul_self_sqrt (by linarith)
  set ρ := b⁻¹ with hρdef
  have hρ0 : 0 ≤ ρ := inv_nonneg.mpr hb0.le
  have hρ1 : ρ < 1 := inv_lt_one_of_one_lt₀ hb
  have hρa : ρ * a = b := by rw [hρdef, ← hbb]; field_simp
  -- uniform coefficient constant
  choose Dil hDil using fun il : ι × ι => hC il.1 il.2 b hb
  set D := ∑ il : ι × ι, max (Dil il) 0 with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun il _ => le_max_right _ _
  have hCm : ∀ i l p q, ‖c2 (Cm i l) p q‖ ≤ D * (ρ * a) ^ (p + q) := by
    intro i l p q
    rw [hρa]
    refine (hDil (i, l) p q).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun il : ι × ι => max (Dil il) 0)
      (fun il _ => le_max_right _ _) (Finset.mem_univ (i, l)))
  set Abar := Fintype.card ι * D * ((1 - ρ)⁻¹ * (1 - ρ)⁻¹) with hAbar
  -- the threshold level
  set N₀ : ℕ := ⌈2 * Abar + 1 + ‖lam‖⌉₊ with hN₀
  have hthr : ∀ n : ℕ, N₀ ≤ n → 2 * Abar + 1 ≤ ‖lam + n‖ := by
    intro n hn
    have h1 : (2 * Abar + 1 + ‖lam‖) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : (n : ℝ) - ‖lam‖ ≤ ‖lam + n‖ := by
      have := norm_sub_norm_le ((n : ℂ)) (-lam)
      rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add, add_comm] at this
      exact this
    linarith
  -- row constants
  choose B hB using fun (p : ι × ℕ) => hrow p.1 p.2 a ha
  set M := ∑ p ∈ (Finset.univ : Finset ι) ×ˢ Finset.range N₀, max (B p) 0 with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => le_max_right _ _
  have hrowM : ∀ n < N₀, ∀ i k, ‖c2 (f i) n k‖ ≤ M * a ^ (n + k) := by
    intro n hn i k
    have hle : B (i, n) ≤ M := (le_max_left _ _).trans
      (Finset.single_le_sum (f := fun p : ι × ℕ => max (B p) 0)
        (fun p _ => le_max_right _ _)
        (Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_range.mpr hn⟩))
    calc ‖c2 (f i) n k‖ ≤ B (i, n) * a ^ k := hB (i, n) k
      _ ≤ M * a ^ k := mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ M * a ^ (n + k) := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ha.le (by omega)) hM0
  have hall : ∀ n : ℕ, ∀ i k, ‖c2 (f i) n k‖ ≤ M * a ^ (n + k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < N₀
      · exact hrowM n hn
      push Not at hn
      -- a crude bound at level n from the rows
      set B' := ∑ i : ι, max (B (i, n)) 0 with hB'
      have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun i _ => le_max_right _ _
      have hcrude : ∀ i k, ‖c2 (f i) n k‖ ≤ (M + B') * a ^ (n + k) := by
        intro i k
        have hle : B (i, n) ≤ M + B' := by
          have : B (i, n) ≤ B' := (le_max_left _ _).trans
            (Finset.single_le_sum (f := fun i : ι => max (B (i, n)) 0)
              (fun i _ => le_max_right _ _) (Finset.mem_univ i))
          linarith
        calc ‖c2 (f i) n k‖ ≤ B (i, n) * a ^ k := hB (i, n) k
          _ ≤ (M + B') * a ^ k := mul_le_mul_of_nonneg_right hle (by positivity)
          _ ≤ (M + B') * a ^ (n + k) := mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ ha.le (by omega)) (by linarith)
      -- iterate the contraction
      have hiter : ∀ j : ℕ, ∀ i k, ‖c2 (f i) n k‖ ≤ (M + B' / 2 ^ j) * a ^ (n + k) := by
        intro j
        induction j with
        | zero => simpa using hcrude
        | succ j ihj =>
          intro i k
          have hstep := euler_step hsys ha hρ0 hρ1 hD0 hCm hM0
            (le_add_of_nonneg_right (by positivity)) n ih ihj (hthr n hn) i k
          refine hstep.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
          rw [pow_succ]
          have h2j : (0 : ℝ) < 2 ^ j := by positivity
          rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
          have : B' / (2 ^ j * 2) * 2 = B' / 2 ^ j := by field_simp
          nlinarith [div_nonneg hB'0 h2j.le]
      intro i k
      have hlim : Filter.Tendsto (fun j : ℕ => (M + B' / 2 ^ j) * a ^ (n + k))
          Filter.atTop (nhds ((M + 0) * a ^ (n + k))) := by
        refine (tendsto_const_nhds.add ?_).mul_const _
        have : Filter.Tendsto (fun j : ℕ => B' * ((1 : ℝ) / 2) ^ j) Filter.atTop
            (nhds (B' * 0)) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul B'
        rw [mul_zero] at this
        refine this.congr fun j => ?_
        rw [one_div, inv_pow, div_eq_mul_inv]
      rw [add_zero] at hlim
      exact ge_of_tendsto' hlim fun j => hiter j i k
  exact ⟨M, fun n k => hall n i₀ k⟩

end System

end VOA.Huang.GenusOneWard
