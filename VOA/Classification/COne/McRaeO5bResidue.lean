/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import Mathlib
import VOA.Foundations.IotaZExpansion

/-! # O5b, formal part: the residue identity for the three expansions of a rational function

Let `R(ζ) = Σ_k c_k ζ^k (ζ - 1)^B` (finitely many `k`) be a rational function with poles only at
`0, 1, ∞`. It has three Laurent expansions: at `∞` (`|ζ| > 1`), at `0` (`0 < |ζ| < 1`) and at `1`
(in `r = ζ - 1`). For the monomial `ζ^A (ζ-1)^B` their coefficients are

* `einf A B n = (-1)^{A+B-n} C(B, A+B-n)` (at `∞`),
* `ezero A B n = (-1)^{B+n-A} C(B, n-A)` (at `0`),
* `eone A B m = C(A, m-B)` (at `1`).

For `a, ℓ ∈ ℤ` the residue functionals `resInf a ℓ`, `resZero a ℓ`, `resOne a ℓ` extract the
coefficient of `ζ^{-1}` (resp. `r^{-1}`) of `ζ^a (ζ-1)^ℓ` times the expansion. The residue
theorem on the sphere says `resInf - resZero = resOne` (`residue_E`); it is exactly the
Jacobi identity of vertex algebra theory, coefficient by coefficient
(`Σ_i (-1)^i C(ℓ,i) (u_{ℓ+m-i} v_{n+i} - (-1)^ℓ v_{ℓ+n-i} u_{m+i}) = Σ_i C(m,i) (u_{ℓ+i}v)_{m+n-i}`
read with `a = m`).

Proof: Vandermonde (`cbz_mul_vandermonde`) reduces the functionals on monomials to the residue
of one monomial (`resInf_einf`, `resZero_ezero`, `resOne_eone`), and the monomial identity
(`residue_mono`) follows from Pascal's rule in both exponents.

Pure combinatorics. No `sorry`, no new axioms.
-/

noncomputable section
namespace VOA.Classification.COne.McRaeO5b
open VOA
open scoped BigOperators

/-! ## Signs -/

theorem negOnePow_eq_zpow (n : ℤ) : negOnePow n = (-1 : ℂ) ^ n := by
  induction n using Int.induction_on with
  | zero => simp [negOnePow]
  | succ k ih => rw [negOnePow_succ, ih, zpow_add_one₀ (by norm_num)]; ring
  | pred k ih =>
      have h := negOnePow_succ (-(k : ℤ) - 1)
      rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih] at h
      rw [zpow_sub_one₀ (by norm_num)]
      linear_combination h

theorem negOnePow_add'' (a b : ℤ) : negOnePow (a + b) = negOnePow a * negOnePow b := by
  rw [negOnePow_eq_zpow, negOnePow_eq_zpow, negOnePow_eq_zpow, zpow_add₀ (by norm_num)]

theorem negOnePow_sub'' (a b : ℤ) : negOnePow (a - b) = negOnePow a * negOnePow b := by
  rw [negOnePow_eq_zpow, negOnePow_eq_zpow, negOnePow_eq_zpow, zpow_sub₀ (by norm_num)]
  have h : ((-1 : ℂ) ^ b)⁻¹ = (-1 : ℂ) ^ b := by
    rw [← zpow_neg, ← negOnePow_eq_zpow, ← negOnePow_eq_zpow]
    rw [negOnePow_eq_zpow, negOnePow_eq_zpow, zpow_neg]
    have h2 : ((-1 : ℂ) ^ b) * ((-1 : ℂ) ^ b) = 1 := by
      rw [← negOnePow_eq_zpow]; exact negOnePow_mul_self b
    exact inv_eq_of_mul_eq_one_right h2
  rw [div_eq_mul_inv, h]

theorem negOnePow_zero'' : negOnePow 0 = 1 := by simp [negOnePow]

/-! ## Binomial facts -/

theorem cbz_nat_of_lt (n : ℕ) {k : ℤ} (hk : (n : ℤ) < k) : cbz n k = 0 := by
  rw [cbz_apply_nonneg _ (by omega), gBinom]
  rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by simp), zero_div]

theorem cbz_zero_left' (k : ℤ) : cbz 0 k = if k = 0 then 1 else 0 := cbz_zero_left k

/-! ## The three expansions of a monomial -/

/-- Coefficient of `ζ^n` in the expansion at `∞` of `ζ^A (ζ-1)^B`. -/
def einf (A B n : ℤ) : ℂ := negOnePow (A + B - n) * cbz B (A + B - n)

/-- Coefficient of `ζ^n` in the expansion at `0` of `ζ^A (ζ-1)^B`. -/
def ezero (A B n : ℤ) : ℂ := negOnePow (B + n - A) * cbz B (n - A)

/-- Coefficient of `r^m` in the expansion at `ζ = 1` (`ζ = 1 + r`) of `ζ^A (ζ-1)^B`. -/
def eone (A B m : ℤ) : ℂ := cbz A (m - B)

theorem einf_pascal (A B n : ℤ) : einf A (B + 1) n = einf (A + 1) B n - einf A B n := by
  unfold einf
  rw [show A + (B + 1) - n = (A + B - n) + 1 by ring, show A + 1 + B - n = (A + B - n) + 1 by ring,
    cbz_pascal_up, negOnePow_succ, show A + B - n + 1 - 1 = A + B - n by ring]
  ring

theorem ezero_pascal (A B n : ℤ) : ezero A (B + 1) n = ezero (A + 1) B n - ezero A B n := by
  unfold ezero
  rw [show B + 1 + n - A = (B + n - A) + 1 by ring, cbz_pascal_up,
    show n - (A + 1) = n - A - 1 by ring, show B + n - (A + 1) = (B + n - A + 1) - 2 by ring,
    negOnePow_sub'', negOnePow_succ]
  have h2 : negOnePow 2 = 1 := by rw [negOnePow_eq_zpow]; norm_num
  rw [h2]
  ring

theorem eone_pascal (A B m : ℤ) : eone A (B + 1) m = eone (A + 1) B m - eone A B m := by
  unfold eone
  rw [cbz_pascal_up, show m - (B + 1) = m - B - 1 by ring]
  ring

/-- **The residue theorem for one monomial** `ζ^A (ζ-1)^B`. -/
theorem residue_mono (A B : ℤ) : einf A B (-1) - ezero A B (-1) = eone A B (-1) := by
  set D : ℤ → ℤ → ℂ := fun A B => einf A B (-1) - ezero A B (-1) - eone A B (-1) with hD
  have hrec : ∀ A B, D A (B + 1) = D (A + 1) B - D A B := by
    intro A B
    simp only [hD, einf_pascal, ezero_pascal, eone_pascal]
    ring
  have hA0 : ∀ A, D A 0 = 0 := by
    intro A
    simp only [hD, einf, ezero, eone, add_zero, cbz_zero_left']
    rw [cbz_apply_neg A (by norm_num : (-1 : ℤ) - 0 < 0)]
    by_cases h : A = -1
    · subst h; simp [negOnePow_zero'']
    · rw [if_neg (by omega), if_neg (by omega)]; ring
  have h0B : ∀ B, D 0 B = 0 := by
    intro B
    simp only [hD, einf, ezero, eone, zero_add, cbz_zero_left']
    rw [cbz_apply_neg B (by norm_num : (-1 : ℤ) - 0 < 0)]
    rcases lt_trichotomy B (-1) with h | h | h
    · rw [cbz_apply_neg B (by omega), if_neg (by omega)]; ring
    · subst h; simp [negOnePow_zero'']
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, B = n := ⟨B.toNat, by omega⟩
      rw [cbz_nat_of_lt n (by omega), if_neg (by omega)]; ring
  have hpos : ∀ n : ℕ, ∀ B, D n B = 0 := by
    intro n
    induction n with
    | zero => exact h0B
    | succ n ih =>
        intro B
        have h := hrec n B
        rw [ih (B + 1), ih B] at h
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
        linear_combination -h
  have hneg : ∀ n : ℕ, ∀ B, D (-(n : ℤ) - 1) B = 0 := by
    intro n
    induction n with
    | zero =>
        intro B
        have hup : ∀ B, D (-1) (B + 1) = -D (-1) B := by
          intro B
          have h := hrec (-1) B
          rw [show (-1 : ℤ) + 1 = 0 by ring, h0B] at h
          linear_combination h
        induction B using Int.induction_on with
        | zero => simpa using hA0 (-1)
        | succ k ih =>
            push_cast
            rw [hup, show -((0 : ℕ) : ℤ) - 1 = -1 by simp] at *
            rw [ih, neg_zero]
        | pred k ih =>
            push_cast at ih ⊢
            have h := hup (-(k : ℤ) - 1)
            rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih] at h
            linear_combination h
    | succ n ih =>
        intro B
        set A := -((n + 1 : ℕ) : ℤ) - 1 with hA
        have hA1 : A + 1 = -(n : ℤ) - 1 := by rw [hA]; push_cast; ring
        have hup : ∀ B, D A (B + 1) = -D A B := by
          intro B
          have h := hrec A B
          rw [hA1, ih] at h
          linear_combination h
        induction B using Int.induction_on with
        | zero => exact hA0 A
        | succ k ih' => rw [hup, ih', neg_zero]
        | pred k ih' =>
            have h := hup (-(k : ℤ) - 1)
            rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring, ih'] at h
            linear_combination h
  have hall : D A B = 0 := by
    rcases le_or_gt 0 A with h | h
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, A = n := ⟨A.toNat, by omega⟩
      exact hpos n B
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, A = -(n : ℤ) - 1 := ⟨(-A - 1).toNat, by omega⟩
      exact hneg n B
  have : einf A B (-1) - ezero A B (-1) - eone A B (-1) = 0 := hall
  linear_combination this

/-! ## The residue functionals -/

/-- The residue at `∞`: coefficient of `ζ^{-1}` in `ζ^a (ζ-1)^ℓ Σ_n s_n ζ^n` (at `∞`). -/
def resInf (a ℓ : ℤ) (s : ℤ → ℂ) : ℂ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * s (i - 1 - a - ℓ)

/-- The residue at `0`: coefficient of `ζ^{-1}` in `ζ^a (ζ-1)^ℓ Σ_n t_n ζ^n` (at `0`). -/
def resZero (a ℓ : ℤ) (t : ℤ → ℂ) : ℂ :=
  negOnePow ℓ * ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * t (-1 - a - i)

/-- The residue at `1`: coefficient of `r^{-1}` in `(1+r)^a r^ℓ Σ_m q_m r^m`. -/
def resOne (a ℓ : ℤ) (q : ℤ → ℂ) : ℂ :=
  ∑ᶠ j : ℤ, cbz a j * q (-1 - ℓ - j)

theorem resInf_einf (a ℓ A B : ℤ) : resInf a ℓ (einf A B) = einf (A + a) (B + ℓ) (-1) := by
  unfold resInf einf
  set K := A + a + B + ℓ + 1 with hK
  have e : ∀ i : ℤ, (negOnePow i * cbz ℓ i) *
      (negOnePow (A + B - (i - 1 - a - ℓ)) * cbz B (A + B - (i - 1 - a - ℓ))) =
      negOnePow K * (cbz ℓ i * cbz B (K - i)) := by
    intro i
    rw [show A + B - (i - 1 - a - ℓ) = K - i by rw [hK]; ring, negOnePow_sub'']
    have := negOnePow_mul_self i
    linear_combination (negOnePow K * cbz ℓ i * cbz B (K - i)) * this
  rw [finsum_congr e, ← mul_finsum, cbz_mul_vandermonde,
    show A + a + (B + ℓ) - -1 = K by rw [hK]; ring, show ℓ + B = B + ℓ by ring]

theorem resZero_ezero (a ℓ A B : ℤ) : resZero a ℓ (ezero A B) = ezero (A + a) (B + ℓ) (-1) := by
  unfold resZero ezero
  set K := -1 - a - A with hK
  have e : ∀ i : ℤ, (negOnePow i * cbz ℓ i) *
      (negOnePow (B + (-1 - a - i) - A) * cbz B (-1 - a - i - A)) =
      negOnePow (B + K) * (cbz ℓ i * cbz B (K - i)) := by
    intro i
    rw [show B + (-1 - a - i) - A = (B + K) - i by rw [hK]; ring, negOnePow_sub'',
      show -1 - a - i - A = K - i by rw [hK]; ring]
    have := negOnePow_mul_self i
    linear_combination (negOnePow (B + K) * cbz ℓ i * cbz B (K - i)) * this
  rw [finsum_congr e, ← mul_finsum, cbz_mul_vandermonde, ← mul_assoc, ← negOnePow_add'',
    show ℓ + (B + K) = B + ℓ + -1 - (A + a) by rw [hK]; ring,
    show K = -1 - (A + a) by rw [hK]; ring, show ℓ + B = B + ℓ by ring]

theorem resOne_eone (a ℓ A B : ℤ) : resOne a ℓ (eone A B) = eone (A + a) (B + ℓ) (-1) := by
  unfold resOne eone
  have e : ∀ j : ℤ, cbz a j * cbz A (-1 - ℓ - j - B) = cbz a j * cbz A ((-1 - ℓ - B) - j) :=
    fun j => by rw [show -1 - ℓ - j - B = (-1 - ℓ - B) - j by ring]
  rw [finsum_congr e, cbz_mul_vandermonde, show a + A = A + a by ring,
    show -1 - (B + ℓ) = -1 - ℓ - B by ring]

/-! ## Linear combinations -/

/-- The expansion at `∞` of `Σ_{k ∈ S} c_k ζ^k (ζ-1)^B`. -/
def Einf (S : Finset ℤ) (c : ℤ → ℂ) (B n : ℤ) : ℂ := ∑ k ∈ S, c k * einf k B n

/-- The expansion at `0` of `Σ_{k ∈ S} c_k ζ^k (ζ-1)^B`. -/
def Ezero (S : Finset ℤ) (c : ℤ → ℂ) (B n : ℤ) : ℂ := ∑ k ∈ S, c k * ezero k B n

/-- The expansion at `1` of `Σ_{k ∈ S} c_k ζ^k (ζ-1)^B`. -/
def Eone (S : Finset ℤ) (c : ℤ → ℂ) (B m : ℤ) : ℂ := ∑ k ∈ S, c k * eone k B m

theorem einf_eq_zero {A B n : ℤ} (h : A + B < n) : einf A B n = 0 := by
  unfold einf; rw [cbz_apply_neg B (by omega), mul_zero]

theorem ezero_eq_zero {A B n : ℤ} (h : n < A) : ezero A B n = 0 := by
  unfold ezero; rw [cbz_apply_neg B (by omega), mul_zero]

theorem eone_eq_zero {A B m : ℤ} (h : m < B) : eone A B m = 0 := by
  unfold eone; rw [cbz_apply_neg A (by omega)]

theorem resInf_Einf (S : Finset ℤ) (c : ℤ → ℂ) (B a ℓ : ℤ) :
    resInf a ℓ (Einf S c B) = ∑ k ∈ S, c k * einf (k + a) (B + ℓ) (-1) := by
  unfold resInf Einf
  have e : ∀ i : ℤ, (negOnePow i * cbz ℓ i) * ∑ k ∈ S, c k * einf k B (i - 1 - a - ℓ) =
      ∑ k ∈ S, c k * ((negOnePow i * cbz ℓ i) * einf k B (i - 1 - a - ℓ)) := by
    intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_finsum]
    congr 1
    exact resInf_einf a ℓ k B
  · intro k _
    apply Set.Finite.subset (Set.finite_Icc 0 (k + B + 1 + a + ℓ))
    intro i hi
    rw [Function.mem_support] at hi
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg ℓ h]; ring
    · rw [einf_eq_zero (by omega)]; ring

theorem resZero_Ezero (S : Finset ℤ) (c : ℤ → ℂ) (B a ℓ : ℤ) :
    resZero a ℓ (Ezero S c B) = ∑ k ∈ S, c k * ezero (k + a) (B + ℓ) (-1) := by
  unfold resZero Ezero
  have e : ∀ i : ℤ, (negOnePow i * cbz ℓ i) * ∑ k ∈ S, c k * ezero k B (-1 - a - i) =
      ∑ k ∈ S, c k * ((negOnePow i * cbz ℓ i) * ezero k B (-1 - a - i)) := by
    intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [finsum_congr e, finsum_sum_comm, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_finsum]
    have := resZero_ezero a ℓ k B
    unfold resZero at this
    rw [← this]
    ring
  · intro k _
    apply Set.Finite.subset (Set.finite_Icc 0 (-1 - a - k))
    intro i hi
    rw [Function.mem_support] at hi
    refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
    · rw [cbz_apply_neg ℓ h]; ring
    · rw [ezero_eq_zero (by omega)]; ring

theorem resOne_Eone (S : Finset ℤ) (c : ℤ → ℂ) (B a ℓ : ℤ) :
    resOne a ℓ (Eone S c B) = ∑ k ∈ S, c k * eone (k + a) (B + ℓ) (-1) := by
  unfold resOne Eone
  have e : ∀ j : ℤ, cbz a j * ∑ k ∈ S, c k * eone k B (-1 - ℓ - j) =
      ∑ k ∈ S, c k * (cbz a j * eone k B (-1 - ℓ - j)) := by
    intro j; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [finsum_congr e, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_finsum]
    congr 1
    have := resOne_eone a ℓ k B
    unfold resOne at this
    rw [← this]
  · intro k _
    apply Set.Finite.subset (Set.finite_Icc 0 (-1 - ℓ - B))
    intro j hj
    rw [Function.mem_support] at hj
    refine ⟨not_lt.mp fun h => hj ?_, not_lt.mp fun h => hj ?_⟩
    · rw [cbz_apply_neg a h]; ring
    · rw [eone_eq_zero (by omega)]; ring

/-- **The residue theorem for `Σ_{k ∈ S} c_k ζ^k (ζ-1)^B`.** -/
theorem residue_E (S : Finset ℤ) (c : ℤ → ℂ) (B a ℓ : ℤ) :
    resInf a ℓ (Einf S c B) - resZero a ℓ (Ezero S c B) = resOne a ℓ (Eone S c B) := by
  rw [resInf_Einf, resZero_Ezero, resOne_Eone, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_sub, residue_mono]

end VOA.Classification.COne.McRaeO5b
