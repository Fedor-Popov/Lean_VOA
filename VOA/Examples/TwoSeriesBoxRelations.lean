/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.TwoSeriesMembershipEndpoint

/-!
# Truncated-product relations in `R_n`, and the reversed monomial map

The box count `BoxCount n r` concerns the image in `R_n = ℂ[T_j]/(jets of Tⁿ)` of the polynomials
in the first `N` jets `T_0, …, T_{N-1}`.  The relations of `R_n` that act inside this box come
from **truncated products**: with `T_{≤M}(x) = Σ_{j ≤ M} T_j x^j`,

  `[x^k] Π_i T_{≤M_i}(x) = 0` in `R_n` whenever `k < Σ_{i ∉ S} (M_i + 1)` for every set `S`
  of fewer than `n` factors                                        (`coeff_prod_trR_eq_zero`).

(Write `T_{≤M} = T - x^{M+1} U` and expand: a product containing `n` copies of `T` vanishes since
`Tⁿ = 0` in `R_n[[x]]`, and the other products start at `x^{Σ_{i ∉ S}(M_i+1)}`.)

These relations are conveniently packaged with the **reversed monomial map**
`Psi n N m : ℂ[y_1, …, y_m] → R_n`, `y^β ↦ Π_i T_{N-1-β_i}` (zero if some `β_i ≥ N`): the box
monomials of `T`-degree `m` are exactly the images of the monomials, `Psi` is invariant under
permutations of the variables (`Psi_rename`), and with the complete homogeneous symmetric
polynomials `hh m q = Σ_{|α| = q} y^α`:

* `Psi_hh_mul_eq_zero` — `Psi (hh m q * g) = 0` for every `g` whenever `(n-1) N < q + m`.

Everything is proved outright.
-/

namespace VOA.TwoSeries.StrictModel

open MvPolynomial

noncomputable section

/-! ### The series `T(x)` over `R_n` and its truncations -/

/-- `T(x) = Σ_j T_j x^j` over `R_n`. -/
def tR (n : ℕ) : PowerSeries (Rn n) := PowerSeries.mk (tn n)

theorem tR_eq_map (n : ℕ) : tR n = PowerSeries.map (Ideal.Quotient.mk (jetIdealT n)) tSer := by
  ext j
  simp [tR, tSer, tn, PowerSeries.coeff_map]

/-- `T(x)ⁿ = 0` in `R_n[[x]]`. -/
theorem tR_pow (n : ℕ) : tR n ^ n = 0 := by
  rw [tR_eq_map, ← map_pow]
  ext j
  rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨j, rfl⟩

/-- The truncation `T_{≤M}(x) = Σ_{j ≤ M} T_j x^j`. -/
def trR (n M : ℕ) : PowerSeries (Rn n) := PowerSeries.mk fun j => if j ≤ M then tn n j else 0

/-- The tail `Σ_j T_{j+M+1} x^j`. -/
def tlR (n M : ℕ) : PowerSeries (Rn n) := PowerSeries.mk fun j => tn n (j + (M + 1))

theorem trR_eq (n M : ℕ) : trR n M = tR n - PowerSeries.X ^ (M + 1) * tlR n M := by
  ext j
  rw [map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [trR, tR, tlR, PowerSeries.coeff_mk]
  split_ifs with h1 h2 h2
  · omega
  · simp
  · rw [Nat.sub_add_cancel h2, sub_self]
  · omega

/-- **Truncated-product relations**: `[x^k] Π_i T_{≤M_i}(x) = 0` in `R_n` as soon as
`k < Σ_{i ∉ S} (M_i + 1)` for every set `S` of fewer than `n` factors. -/
theorem coeff_prod_trR_eq_zero {n m : ℕ} (M : Fin m → ℕ) (k : ℕ)
    (hk : ∀ S : Finset (Fin m), S.card < n → k < ∑ i ∈ Finset.univ \ S, (M i + 1)) :
    PowerSeries.coeff k (∏ i, trR n (M i)) = 0 := by
  classical
  simp_rw [trR_eq, sub_eq_add_neg]
  rw [Finset.prod_add, map_sum]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [Finset.prod_const]
  by_cases hS : n ≤ S.card
  · rw [← Nat.add_sub_cancel' hS, pow_add, tR_pow, zero_mul, zero_mul, map_zero]
  · push Not at hS
    have h : ∏ i ∈ Finset.univ \ S, -(PowerSeries.X ^ (M i + 1) * tlR n (M i)) =
        PowerSeries.X ^ (∑ i ∈ Finset.univ \ S, (M i + 1)) *
          ∏ i ∈ Finset.univ \ S, -(tlR n (M i)) := by
      simp_rw [← mul_neg]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [h, mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (not_le.mpr (hk S hS))]

/-! ### Reversal of a product of bounded series -/

theorem sum_filter_le_eq {R : Type*} [CommSemiring R] {m : ℕ} (M : Fin m → ℕ)
    (g : Fin m → ℕ → R) (s : Finset (Fin m →₀ ℕ)) :
    ∑ l ∈ s, ∏ i, (if l i ≤ M i then g i (l i) else 0) =
      ∑ l ∈ s.filter (fun l => ∀ i, l i ≤ M i), ∏ i, (if l i ≤ M i then g i (l i) else 0) := by
  classical
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra hle
  push Not at hle
  obtain ⟨i, hi⟩ := hle
  exact hl (Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_le.mpr hi)))

theorem sum_tsub_add {m : ℕ} (M : Fin m → ℕ) (l : Fin m →₀ ℕ) (hle : ∀ i, l i ≤ M i) :
    ∑ i, (M i - l i) + ∑ i, l i = ∑ i, M i := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)

/-- Reversing every factor of a product of series of bounded degrees reverses the product. -/
theorem sum_finsuppAntidiag_reverse {R : Type*} [CommSemiring R] {m : ℕ} (M : Fin m → ℕ)
    (f : Fin m → ℕ → R) (q : ℕ) (hq : q ≤ ∑ i, M i) :
    ∑ l ∈ (Finset.univ : Finset (Fin m)).finsuppAntidiag q,
        ∏ i, (if l i ≤ M i then f i (l i) else 0) =
      ∑ l ∈ (Finset.univ : Finset (Fin m)).finsuppAntidiag ((∑ i, M i) - q),
        ∏ i, (if l i ≤ M i then f i (M i - l i) else 0) := by
  classical
  let Mf : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm M
  have hMf : ∀ i, Mf i = M i := fun i => rfl
  have hsub : ∀ l : Fin m →₀ ℕ, ∀ i, (Mf - l) i = M i - l i := fun l i => by
    rw [Finsupp.tsub_apply, hMf]
  rw [sum_filter_le_eq M f, sum_filter_le_eq M (fun i a => f i (M i - a))]
  refine Finset.sum_nbij' (fun l => Mf - l) (fun l => Mf - l) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.subset_univ,
      and_true] at hl ⊢
    obtain ⟨hs, hle⟩ := hl
    refine ⟨?_, fun i => by rw [hsub]; exact Nat.sub_le _ _⟩
    have h2 := sum_tsub_add M l hle
    simp only [hsub]
    have hs' : ∑ i, l i = q := hs
    omega
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.subset_univ,
      and_true] at hl ⊢
    obtain ⟨hs, hle⟩ := hl
    refine ⟨?_, fun i => by rw [hsub]; exact Nat.sub_le _ _⟩
    have h2 := sum_tsub_add M l hle
    simp only [hsub]
    have hs' : ∑ i, l i = (∑ i, M i) - q := hs
    omega
  · intro l hl
    simp only [Finset.mem_filter] at hl
    ext i
    rw [hsub, hsub, Nat.sub_sub_self (hl.2 i)]
  · intro l hl
    simp only [Finset.mem_filter] at hl
    ext i
    rw [hsub, hsub, Nat.sub_sub_self (hl.2 i)]
  · intro l hl
    simp only [Finset.mem_filter] at hl
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_pos (hl.2 i), hsub, if_pos (Nat.sub_le _ _), Nat.sub_sub_self (hl.2 i)]

/-! ### The reversed monomial map `Psi` -/

/-- The image of the monomial `y^β`: `Π_i T_{N-1-β_i}`, zero if some `β_i ≥ N`. -/
def psiMono (n N : ℕ) {m : ℕ} (β : Fin m →₀ ℕ) : Rn n :=
  ∏ i, if β i < N then tn n (N - 1 - β i) else 0

/-- The reversed monomial map `ℂ[y_1, …, y_m] → R_n`, `y^β ↦ Π_i T_{N-1-β_i}`. -/
def Psi (n N m : ℕ) : MvPolynomial (Fin m) ℂ →ₗ[ℂ] Rn n :=
  Finsupp.linearCombination ℂ (psiMono n N)

theorem Psi_monomial (n N : ℕ) {m : ℕ} (β : Fin m →₀ ℕ) (c : ℂ) :
    Psi n N m (monomial β c) = c • psiMono n N β :=
  Finsupp.linearCombination_single ℂ c β

theorem psiMono_mapDomain (n N : ℕ) {m : ℕ} (e : Equiv.Perm (Fin m)) (β : Fin m →₀ ℕ) :
    psiMono n N (Finsupp.mapDomain e β) = psiMono n N β := by
  unfold psiMono
  refine (Fintype.prod_equiv e _ _ fun i => ?_).symm
  rw [Finsupp.mapDomain_apply e.injective]

/-- `Psi` is invariant under permutations of the variables. -/
theorem Psi_rename (n N : ℕ) {m : ℕ} (e : Equiv.Perm (Fin m)) (p : MvPolynomial (Fin m) ℂ) :
    Psi n N m (rename e p) = Psi n N m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c => rw [rename_monomial, Psi_monomial, Psi_monomial, psiMono_mapDomain]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]

/-! ### Complete homogeneous symmetric polynomials -/

/-- The complete homogeneous symmetric polynomial `h_q(y_1, …, y_m)`. -/
def hh (m q : ℕ) : MvPolynomial (Fin m) ℂ :=
  PowerSeries.coeff q (∏ i : Fin m, PowerSeries.mk fun a => (X i : MvPolynomial (Fin m) ℂ) ^ a)

theorem prod_X_pow_eq_monomial {m : ℕ} (α : Fin m →₀ ℕ) :
    ∏ i, (X i : MvPolynomial (Fin m) ℂ) ^ α i = monomial α 1 := by
  rw [monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype]
  intro i; rw [pow_zero]

theorem hh_eq (m q : ℕ) :
    hh m q = ∑ α ∈ (Finset.univ : Finset (Fin m)).finsuppAntidiag q, monomial α 1 := by
  classical
  rw [hh, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [PowerSeries.coeff_mk]
  exact prod_X_pow_eq_monomial α

theorem Psi_hh_mul_monomial (n N : ℕ) {m : ℕ} (q : ℕ) (β : Fin m →₀ ℕ) :
    Psi n N m (hh m q * monomial β 1) =
      PowerSeries.coeff q (∏ i : Fin m, PowerSeries.mk fun a =>
        if a + β i < N then tn n (N - 1 - (a + β i)) else 0) := by
  classical
  rw [hh_eq, Finset.sum_mul, map_sum, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [monomial_mul, one_mul, Psi_monomial, one_smul, psiMono]
  simp only [PowerSeries.coeff_mk, Finsupp.add_apply]

/-- **`Psi` kills `h_q · y^β` for `(n-1) N < q + m`.** -/
theorem Psi_hh_mul_monomial_eq_zero {n N m : ℕ} (q : ℕ) (hq : (n - 1) * N < q + m)
    (β : Fin m →₀ ℕ) : Psi n N m (hh m q * monomial β 1) = 0 := by
  classical
  rw [Psi_hh_mul_monomial]
  by_cases hβ : ∃ j, N ≤ β j
  · obtain ⟨j, hj⟩ := hβ
    have h0 : (PowerSeries.mk fun a =>
        if a + β j < N then tn n (N - 1 - (a + β j)) else 0) = 0 := by
      ext a; rw [PowerSeries.coeff_mk, map_zero, if_neg (by omega)]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) h0, map_zero]
  push Not at hβ
  set M : Fin m → ℕ := fun i => N - 1 - β i with hM
  have hG : ∀ i, (PowerSeries.mk fun a => if a + β i < N then tn n (N - 1 - (a + β i)) else 0) =
      PowerSeries.mk fun a => if a ≤ M i then tn n (M i - a) else 0 := by
    intro i; ext a
    simp only [PowerSeries.coeff_mk, hM]
    have hb := hβ i
    by_cases h : a + β i < N
    · rw [if_pos h, if_pos (show a ≤ N - 1 - β i by omega)]
      congr 1
      omega
    · rw [if_neg h, if_neg (show ¬ a ≤ N - 1 - β i by omega)]
  simp_rw [hG]
  rw [PowerSeries.coeff_prod]
  simp only [PowerSeries.coeff_mk]
  by_cases hqM : q ≤ ∑ i, M i
  · rw [sum_finsuppAntidiag_reverse M (fun i a => tn n (M i - a)) q hqM]
    have hk := coeff_prod_trR_eq_zero (n := n) M ((∑ i, M i) - q) ?_
    · rw [PowerSeries.coeff_prod] at hk
      refine Eq.trans ?_ hk
      refine Finset.sum_congr rfl fun l _ => Finset.prod_congr rfl fun i _ => ?_
      simp only [trR, PowerSeries.coeff_mk]
      split_ifs with h
      · rw [Nat.sub_sub_self h]
      · rfl
    · intro S hS
      have hsplit : ∑ i ∈ Finset.univ \ S, (M i + 1) + ∑ i ∈ S, (M i + 1) = ∑ i, (M i + 1) :=
        Finset.sum_sdiff (Finset.subset_univ S)
      have hSle : ∑ i ∈ S, (M i + 1) ≤ S.card * N := by
        rw [← smul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun i _ => by simp only [hM]; have := hβ i; omega
      have hSn : S.card * N ≤ (n - 1) * N := Nat.mul_le_mul_right _ (by omega)
      have htot : ∑ i, (M i + 1) = ∑ i, M i + m := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one]
      omega
  · push Not at hqM
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_finsuppAntidiag] at hl
    obtain ⟨i, hi⟩ : ∃ i, M i < l i := by
      by_contra h
      push Not at h
      have : ∑ i, l i ≤ ∑ i, M i := Finset.sum_le_sum fun i _ => h i
      have hl1 : ∑ i, l i = q := hl.1
      omega
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_le.mpr hi))

/-- **`Psi (h_q · g) = 0` for every `g`, when `(n-1) N < q + m`.** -/
theorem Psi_hh_mul_eq_zero {n N m : ℕ} (q : ℕ) (hq : (n - 1) * N < q + m)
    (g : MvPolynomial (Fin m) ℂ) : Psi n N m (hh m q * g) = 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [show monomial β c = c • monomial β (1 : ℂ) by rw [smul_monomial, smul_eq_mul, mul_one],
      mul_smul_comm, map_smul, Psi_hh_mul_monomial_eq_zero q hq β, smul_zero]
  | add p r hp hr => rw [mul_add, map_add, hp, hr, add_zero]

end

end VOA.TwoSeries.StrictModel
