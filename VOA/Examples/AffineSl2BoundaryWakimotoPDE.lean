/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ScreeningCartan
import VOA.Examples.WakimotoJointEigenspaces
import VOA.Commutative.DerivativeLeadingCoefficient

/-!
# Charge-one highest polynomials in the Wakimoto realization

The actual Cartan equations give a triangular differential system for the
coefficients of the beta oscillators. Its highest ordinary-degree terms detect
a nonzero classical symbol.
-/
namespace VOA.Wak.BoundaryPDE
open MvPolynomial Screening
open scoped BigOperators
noncomputable section

/-- Gamma independence is stable under every oscillator derivative. -/
theorem gammaFree_pderiv (P : WakFock) (hP : P ∈ gammaFree) (v : Fin 3 × ℕ) :
    pderiv v P ∈ gammaFree := by
  intro j
  rw [pderiv_comm', hP j, map_zero]

private theorem gamma_exponent_zero (P : WakFock) (hP : P ∈ gammaFree)
    (d : Fin 3 × ℕ →₀ ℕ) (hd : coeff d P ≠ 0) (j : ℕ) : d (1,j) = 0 := by
  have h := coeff_X_mul_pderiv (1,j) d P
  rw [hP j, mul_zero, coeff_zero] at h
  exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hd)

private def betaCount (d : Fin 3 × ℕ →₀ ℕ) : ℕ :=
  d.sum (fun v n => if v.1 = 0 then n else 0)

private theorem charge_eq_betaCount (P : WakFock) (hP : P ∈ gammaFree)
    (d : Fin 3 × ℕ →₀ ℕ) (hd : coeff d P ≠ 0) :
    Finsupp.weight chFn d = (betaCount d : ℂ) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum, betaCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with ⟨a,j⟩
  fin_cases a
  · simp [chFn, nsmul_eq_mul]
  · simp [chFn, gamma_exponent_zero P hP d hd j]
  · simp [chFn]

/-- A gamma-independent polynomial of charge zero is independent of beta. -/
theorem beta_derivative_zero_of_charge_zero (P : WakFock) (hP : P ∈ gammaFree)
    (hch : Dch P = 0) (j : ℕ) : pderiv (0,j) P = 0 := by
  classical
  have hexp : ∀ d, coeff d P ≠ 0 → d (0,j) = 0 := by
    intro d hd
    have hc := congrArg (coeff d) hch
    rw [Dch, Charged.coeff_Eul, charge_eq_betaCount P hP d hd, coeff_zero] at hc
    have hb : betaCount d = 0 := Nat.cast_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hd)
    by_cases hmem : (0,j) ∈ d.support
    · have hle : d (0,j) ≤ betaCount d := by
        simpa [betaCount, Finsupp.sum] using
          (Finset.single_le_sum (f := fun v => if v.1 = 0 then d v else 0)
            (fun v _ => Nat.zero_le _) hmem)
      omega
    · exact Finsupp.notMem_support_iff.mp hmem
  ext d
  rw [VOA.VirasoroScreening.screening_pderiv_coeff, coeff_zero]
  by_cases hd : coeff (d + Finsupp.single (0,j) 1) P = 0
  · simp [hd]
  · have hh := hexp _ hd
    simp at hh

/-- A charge-one gamma-independent polynomial is linear in all beta variables. -/
theorem beta_second_derivative_zero (P : WakFock) (hP : P ∈ gammaFree)
    (hch : Dch P = P) (i j : ℕ) : pderiv (0,i) (pderiv (0,j) P) = 0 := by
  apply beta_derivative_zero_of_charge_zero _ (gammaFree_pderiv P hP _)
  have h := Eul_pderiv chFn (0,j) P
  change Dch (pderiv (0,j) P) - pderiv (0,j) (Dch P) = _ at h
  rw [hch, chFn_b, neg_smul, one_smul] at h
  linear_combination h

/-- Differentiating the actual positive Cartan equation gives a recurrence
between beta coefficients. -/
theorem beta_coefficient_cartan (k : ℂ) (P : WakFock) (hP : P ∈ gammaFree)
    (hch : Dch P = P) (hH : ∀ n : ℕ, 0 < n → Hcur k (n : ℤ) P = 0)
    (j n : ℕ) (hn : 0 < n) :
    ((k + 2) * (n : ℂ)) • pderiv (2,n-1) (pderiv (0,j) P) =
      -pderiv (0,j+n) P := by
  classical
  let D := max j (NB P).toNat
  have hj : j ∈ Finset.range (D+1) := by simp [D]
  have hD : ∀ i, D < i → pderiv (0,i) P = 0 := by
    intro i hi
    apply pderiv_eq_zero_of_NB_le
    dsimp [D] at hi
    have := two_le_NB P
    omega
  have hc := H_positive_explicit_cutoff k 0 P hP n D hn hD
  have hHz : Charged.H k 0 (n : ℤ) P = 0 := by
    simpa [Charged.H] using hH n hn
  rw [hHz] at hc
  have hc' := congrArg (pderiv (0,j)) hc
  simp only [map_zero, map_add, Derivation.map_smul, map_sum] at hc'
  have hsum : (∑ i ∈ Finset.range (D+1),
      pderiv (0,j) (X (0,i) * pderiv (0,i+n) P)) = pderiv (0,j+n) P := by
    simp only [pderiv_mul, beta_second_derivative_zero P hP hch, mul_zero, add_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      rw [pderiv_X_of_ne (by simpa using hij), zero_mul]
    · exact fun hnot => (hnot hj).elim
  rw [hsum, pderiv_comm'] at hc'
  have hc2 := congrArg (fun x : WakFock => (1/2 : ℂ) • x) hc'
  simp only [smul_zero, smul_add, smul_smul] at hc2
  norm_num at hc2
  have he : (1/2 : ℂ) * (2 * (k + 2) * (n : ℂ)) = (k+2)*(n : ℂ) := by ring
  rw [he] at hc2
  exact eq_neg_of_add_eq_zero_right hc2.symm

/-- Every beta coefficient is determined by the zeroth one through the first
positive Cartan equation. -/
theorem beta_coefficient_iterate (k : ℂ) (P : WakFock) (hP : P ∈ gammaFree)
    (hch : Dch P = P) (hH : ∀ n : ℕ, 0 < n → Hcur k (n : ℤ) P = 0)
    (j : ℕ) :
    pderiv (0,j) P = (-(k+2))^j • ((pderiv (2,0))^[j] (pderiv (0,0) P)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := beta_coefficient_cartan k P hP hch hH j 1 (by omega)
    simp only [Nat.cast_one, mul_one, Nat.sub_self] at h
    have he : pderiv (0,j+1) P = -(k+2) • pderiv (2,0) (pderiv (0,j) P) := by
      rw [neg_smul, h, neg_neg]
    rw [he, ih, Derivation.map_smul, smul_smul, Function.iterate_succ_apply', pow_succ']

/-- A nonzero charge-one highest polynomial has a nonzero zeroth beta
coefficient. -/
theorem beta_zero_ne_zero (k : ℂ) (P : WakFock) (hP : P ∈ gammaFree)
    (hch : Dch P = P) (hH : ∀ n : ℕ, 0 < n → Hcur k (n : ℤ) P = 0)
    (hne : P ≠ 0) : pderiv (0,0) P ≠ 0 := by
  intro hz
  have hall : ∀ j, pderiv (0,j) P = 0 := by
    intro j
    rw [beta_coefficient_iterate k P hP hch hH j, hz]
    have hi : (pderiv (2,0))^[j] (0 : WakFock) = 0 := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, map_zero]
    rw [hi, smul_zero]
  apply hne
  rw [← hch]
  ext d
  rw [Dch, Charged.coeff_Eul, coeff_zero]
  by_cases hd : coeff d P = 0
  · simp [hd]
  have hb : ∀ j, d (0,j) = 0 := by
    intro j
    have h := coeff_X_mul_pderiv (0,j) d P
    rw [hall j, mul_zero, coeff_zero] at h
    exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hd)
  have hc : Finsupp.weight chFn d = 0 := by
    classical
    rw [Finsupp.weight_apply, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro v hv
    rcases v with ⟨a,j⟩
    fin_cases a
    · simp [chFn, hb j]
    · simp [chFn, gamma_exponent_zero P hP d hd j]
    · simp [chFn]
  rw [hc, zero_mul]

/-- The zeroth beta coefficient satisfies the triangular derivative equations
in all variables other than the zeroth boson oscillator. -/
theorem beta_zero_triangular (k : ℂ) (hk : k+2 ≠ 0) (P : WakFock)
    (hP : P ∈ gammaFree) (hch : Dch P = P)
    (hH : ∀ n : ℕ, 0 < n → Hcur k (n : ℤ) P = 0)
    (v : Fin 3 × ℕ) (hv : v ≠ (2,0)) :
    ∃ (r : ℕ) (c : ℂ), 2 ≤ r ∧
      pderiv v (pderiv (0,0) P) =
        c • ((pderiv (2,0))^[r] (pderiv (0,0) P)) := by
  rcases v with ⟨a,j⟩
  fin_cases a
  · exact ⟨2, 0, le_rfl, by simpa only [zero_smul] using beta_second_derivative_zero P hP hch j 0⟩
  · exact ⟨2, 0, le_rfl, by simpa only [zero_smul] using (gammaFree_pderiv P hP (0,0)) j⟩
  · have hj : 0 < j := by
      by_contra hh
      have hj0 : j = 0 := by omega
      subst j
      exact hv rfl
    let s : ℂ := (k+2) * ((j+1 : ℕ) : ℂ)
    have hs : s ≠ 0 := mul_ne_zero hk (Nat.cast_ne_zero.mpr (by omega))
    refine ⟨j+1, -(s⁻¹ * (-(k+2))^(j+1)), by omega, ?_⟩
    have h := beta_coefficient_cartan k P hP hch hH 0 (j+1) (by omega)
    simp only [Nat.add_sub_cancel, zero_add] at h
    rw [beta_coefficient_iterate k P hP hch hH (j+1)] at h
    have hh := congrArg (fun x : WakFock => s⁻¹ • x) h
    change s⁻¹ • (s • _) = _ at hh
    simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul, smul_neg, neg_smul] using hh

/-- A nonzero gamma-independent charge-one polynomial killed by actual positive
Cartan modes contains a nonzero beta-zero, boson-zero monomial. -/
theorem exists_depth_zero_coefficient (k : ℂ) (hk : k+2 ≠ 0) (P : WakFock)
    (hP : P ∈ gammaFree) (hch : Dch P = P)
    (hH : ∀ n : ℕ, 0 < n → Hcur k (n : ℤ) P = 0) (hne : P ≠ 0) :
    ∃ d : ℕ, coeff (Finsupp.single (2,0) d + Finsupp.single (0,0) 1) P ≠ 0 := by
  obtain ⟨d, hd⟩ := DerivativeLeadingCoefficient.exists_pure_coefficient_ne_zero
    (pderiv (0,0) P) (2,0) (beta_zero_ne_zero k P hP hch hH hne)
    (beta_zero_triangular k hk P hP hch hH)
  rw [VOA.VirasoroScreening.screening_pderiv_coeff] at hd
  exact ⟨d, (mul_ne_zero_iff.mp hd).2⟩

end
end VOA.Wak.BoundaryPDE
