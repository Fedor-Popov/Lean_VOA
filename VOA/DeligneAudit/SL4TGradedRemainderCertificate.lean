import VOA.DeligneAudit.SL4THomogeneousIdealExpansion

/-! # Graded level certificates for the top-row remainder ideal -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {σ A : Type*} [CommRing A]

/-- Replacing one row changes a minor's homogeneous degree by the opposite row displacement. -/
theorem remainderMinorDegree_update (N j : ℕ) (rows cols : Fin j → ℕ)
    (b : Fin j) (l : ℕ) :
    remainderMinorDegree N j (Function.update rows b l) cols =
      remainderMinorDegree N j rows cols + rows b - l := by
  classical
  have he : (fun a => (Function.update rows b l a : ℤ)) =
      Function.update (fun a => (rows a : ℤ)) b l := by
    funext a
    by_cases ha : a = b
    · subst a
      simp only [Function.update_self]
    · rw [Function.update_of_ne ha, Function.update_of_ne ha]
  unfold remainderMinorDegree
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ b)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hs := Finset.add_sum_erase Finset.univ (fun a => (rows a : ℤ))
    (Finset.mem_univ b)
  rw [← hs]
  ring

/-- The explicit lower-power correction associated to a top-row minor. -/
def remainderTopCorrection {R : Type*} [CommRing R] (xs : List R) (N j : ℕ)
    (cols : Fin j → ℕ) (hj : 0 < j) : Polynomial R :=
  remainderCramerPolynomial xs N j cols ⟨0, hj⟩ -
    Polynomial.C (remainderTopMinor xs N j cols) * Polynomial.X ^ (xs.length - j)

/-- Each lower coefficient has its precise increased degree in the coefficient ring. -/
theorem remainderTopCorrection_homogeneous (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (cols : Fin j → ℕ) (hj : 0 < j) (hjr : j ≤ xs.length) (l : ℕ) :
    ((remainderTopCorrection xs N j cols hj).coeff l).IsWeightedHomogeneous w
      (remainderMinorDegree N j (fun a => xs.length - j + a.val) cols +
        (xs.length - j : ℕ) - l) := by
  classical
  by_cases hl : l < xs.length - j
  · have hc : (remainderTopCorrection xs N j cols hj).coeff l =
        remainderRowMinor xs N j
          (Function.update (fun a => xs.length - j + a.val) ⟨0, hj⟩ l) cols := by
      rw [remainderTopCorrection, Polynomial.coeff_sub, remainderCramerPolynomial_coeff,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero,
        sub_zero]
    rw [hc]
    have h := remainderRowMinor_homogeneous w xs hxs N j
      (Function.update (fun a => xs.length - j + a.val) ⟨0, hj⟩ l) cols
    simpa only [remainderMinorDegree_update, Nat.add_zero] using h
  · have hz := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (remainderCramerPolynomial_correction_degree xs N j cols hj hjr)
        (by exact_mod_cast (show xs.length - j ≤ l by omega)))
    change (remainderTopCorrection xs N j cols hj).coeff l = 0 at hz
    rw [hz]
    exact MvPolynomial.isWeightedHomogeneous_zero A w _

/-- A nonzero correction coefficient has strictly larger homogeneous degree than its minor. -/
theorem remainderTopCorrection_degree_increases {R : Type*} [CommRing R]
    (xs : List R) (N j : ℕ) (cols : Fin j → ℕ) (hj : 0 < j)
    (hjr : j ≤ xs.length) (l : ℕ)
    (hl : (remainderTopCorrection xs N j cols hj).coeff l ≠ 0) :
    remainderMinorDegree N j (fun a => xs.length - j + a.val) cols <
      remainderMinorDegree N j (fun a => xs.length - j + a.val) cols +
        (xs.length - j : ℕ) - l := by
  have hd := remainderCramerPolynomial_correction_degree xs N j cols hj hjr
  have hc := Polynomial.le_degree_of_ne_zero hl
  have hlt : l < xs.length - j := by exact_mod_cast lt_of_le_of_lt hc hd
  omega

/-- The graded Cramer certificate for a generator of the top-row ideal. -/
theorem remainderTopMinor_graded_certificate (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (cols : Fin j → ℕ) (hj : 0 < j) (hjr : j ≤ xs.length) :
    ∃ p : Polynomial (MvPolynomial σ A),
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N j) ∧
      (∀ l, (p.coeff l).IsWeightedHomogeneous w
        (remainderMinorDegree N j (fun a => xs.length - j + a.val) cols +
          (xs.length - j : ℕ) - l)) ∧
      Polynomial.C (remainderTopMinor xs N j cols) * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  refine ⟨remainderTopCorrection xs N j cols hj,
    remainderCramerPolynomial_correction_degree xs N j cols hj hjr, ?_,
    remainderTopCorrection_homogeneous w xs hxs N j cols hj hjr, ?_⟩
  · intro l
    rw [← remainderAllIdeal_eq_topIdeal xs N j hjr]
    simpa only [Nat.add_zero] using
      remainderCramerPolynomial_correction_coeff_mem xs N j cols ⟨0, hj⟩ l
  · have he : Polynomial.C (remainderTopMinor xs N j cols) *
        Polynomial.X ^ (xs.length - j) + remainderTopCorrection xs N j cols hj =
        remainderCramerPolynomial xs N j cols ⟨0, hj⟩ := by
      unfold remainderTopCorrection
      ring
    rw [he]
    exact remainderCramerPolynomial_mem xs N j cols ⟨0, hj⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.remainderMinorDegree_update
#print axioms VOA.DeligneAudit.SL4T.remainderTopCorrection_homogeneous
#print axioms VOA.DeligneAudit.SL4T.remainderTopCorrection_degree_increases
#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_graded_certificate
