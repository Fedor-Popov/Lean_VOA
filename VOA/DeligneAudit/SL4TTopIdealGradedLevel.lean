import VOA.DeligneAudit.SL4TGradedRemainderCertificate

/-! # Graded truncation for every homogeneous element of the top-row ideal -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {σ A : Type*} [CommRing A]

/-- Every homogeneous element of the top-row ideal has a lower-power correction
in the same ideal, with the precise increase in coefficient degree. -/
theorem remainderTopIdeal_graded_certificate (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (hj : 0 < j) (hjr : j ≤ xs.length)
    (a : MvPolynomial σ A) (d : ℤ) (ha : a.IsWeightedHomogeneous w d)
    (hmem : a ∈ remainderTopIdeal xs N j) :
    ∃ p : Polynomial (MvPolynomial σ A),
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N j) ∧
      (∀ l, (p.coeff l).IsWeightedHomogeneous w (d + (xs.length - j : ℕ) - l)) ∧
      Polynomial.C a * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  classical
  let degree : (Fin j → ℕ) → ℤ :=
    fun cols => remainderMinorDegree N j (fun a => xs.length - j + a.val) cols
  obtain ⟨s, c, hc, hs⟩ := homogeneous_ideal_span_expansion w
    (remainderTopMinor xs N j) degree
    (fun cols => remainderRowMinor_homogeneous w xs hxs N j
      (fun a => xs.length - j + a.val) cols) a d ha hmem
  choose q hqdegree hqmem hqhom hqrel using fun cols =>
    remainderTopMinor_graded_certificate w xs hxs N j cols hj hjr
  let p := ∑ i ∈ s, Polynomial.C (c i) * q i
  have hpcoeff (l : ℕ) : p.coeff l = ∑ i ∈ s, c i * (q i).coeff l := by
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [Polynomial.degree_lt_iff_coeff_zero]
    intro l hl
    rw [hpcoeff]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le (hqdegree i) (by exact_mod_cast hl)), mul_zero]
  · intro l
    rw [hpcoeff]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (hqmem i l)
  · intro l
    rw [hpcoeff]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro i hi
    convert (hc i).mul (hqhom i l) using 1
    dsimp [degree]
    ring
  · have hsum := Ideal.sum_mem (t := s)
      (Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N})
      (fun i hi => Ideal.mul_mem_left _ (Polynomial.C (c i)) (hqrel i))
    have he : (∑ i ∈ s, Polynomial.C (c i) *
        (Polynomial.C (remainderTopMinor xs N j i) *
          Polynomial.X ^ (xs.length - j) + q i)) =
        Polynomial.C a * Polynomial.X ^ (xs.length - j) + p := by
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← map_mul,
        ← Finset.sum_mul, ← map_sum, hs, p]
    rw [he] at hsum
    exact hsum

/-- The coefficient-degree increase is strict wherever the correction is nonzero. -/
theorem remainderTopIdeal_strict_graded_certificate (w : σ → ℤ)
    (xs : List (MvPolynomial σ A)) (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1)
    (N j : ℕ) (hj : 0 < j) (hjr : j ≤ xs.length)
    (a : MvPolynomial σ A) (d : ℤ) (ha : a.IsWeightedHomogeneous w d)
    (hmem : a ∈ remainderTopIdeal xs N j) :
    ∃ p : Polynomial (MvPolynomial σ A),
      (∀ l, p.coeff l ∈ remainderTopIdeal xs N j) ∧
      (∀ l, p.coeff l ≠ 0 → ∃ e : ℤ, d < e ∧
        (p.coeff l).IsWeightedHomogeneous w e) ∧
      Polynomial.C a * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  obtain ⟨p, hpdegree, hpmem, hphom, hprel⟩ :=
    remainderTopIdeal_graded_certificate w xs hxs N j hj hjr a d ha hmem
  refine ⟨p, hpmem, ?_, hprel⟩
  intro l hl
  refine ⟨d + (xs.length - j : ℕ) - l, ?_, hphom l⟩
  have hlt : l < xs.length - j := by
    exact_mod_cast lt_of_le_of_lt (Polynomial.le_degree_of_ne_zero hl) hpdegree
  omega

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_graded_certificate
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_strict_graded_certificate
