import VOA.DeligneAudit.SL4TFullFlagStratumRank
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # Cramer witnesses for top-row remainder minors -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- A remainder minor with arbitrary row and column indices. -/
def remainderRowMinor (xs : List A) (N j : ℕ) (rows cols : Fin j → ℕ) : A :=
  Matrix.det fun a b : Fin j => alphabetPowerRemainder xs (N + cols b) (rows a)

/-- The ideal of all minors of the specified size in the remainder matrix. -/
def remainderAllIdeal (xs : List A) (N j : ℕ) : Ideal A :=
  Ideal.span {a | ∃ rows cols : Fin j → ℕ, remainderRowMinor xs N j rows cols = a}

theorem remainderRowMinor_mem (xs : List A) (N j : ℕ) (rows cols : Fin j → ℕ) :
    remainderRowMinor xs N j rows cols ∈ remainderAllIdeal xs N j :=
  Ideal.subset_span ⟨rows, cols, rfl⟩

/-- Every top-row minor is among the minors generating the all-row ideal. -/
theorem remainderTopIdeal_le_allIdeal (xs : List A) (N j : ℕ) :
    remainderTopIdeal xs N j ≤ remainderAllIdeal xs N j := by
  apply Ideal.span_le.mpr
  rintro a ⟨cols, rfl⟩
  exact remainderRowMinor_mem xs N j (fun a => xs.length - j + a.val) cols

/-- A row paired with the Cramer vector is the determinant with that row replaced. -/
theorem determinant_row_cramer {j : ℕ} (M : Matrix (Fin j) (Fin j) A)
    (v : Fin j → A) (b : Fin j) :
    (∑ c, v c * Matrix.cramer M (Pi.single b 1) c) = (M.updateRow b v).det := by
  classical
  rw [← Matrix.cramer_transpose_apply]
  simp only [Matrix.cramer_eq_adjugate_mulVec]
  rw [Matrix.mulVec_single_one, ← Matrix.adjugate_transpose]
  simp only [Matrix.col_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]

/-- The linear combination of remainder columns selected by Cramer's rule. -/
def remainderCramerPolynomial (xs : List A) (N j : ℕ) (cols : Fin j → ℕ)
    (b : Fin j) : Polynomial A :=
  let M : Matrix (Fin j) (Fin j) A := fun a c =>
    alphabetPowerRemainder xs (N + cols c) (xs.length - j + a.val)
  ∑ c, Polynomial.C (Matrix.cramer M (Pi.single b 1) c) *
    (Polynomial.X ^ (N + cols c) %ₘ alphabetCharacteristic xs)

/-- Every coefficient of the Cramer polynomial is the corresponding row-replacement minor. -/
theorem remainderCramerPolynomial_coeff (xs : List A) (N j : ℕ) (cols : Fin j → ℕ)
    (b : Fin j) (l : ℕ) :
    (remainderCramerPolynomial xs N j cols b).coeff l =
      remainderRowMinor xs N j (Function.update (fun a => xs.length - j + a.val) b l) cols := by
  classical
  let M : Matrix (Fin j) (Fin j) A := fun a c =>
    alphabetPowerRemainder xs (N + cols c) (xs.length - j + a.val)
  have hm : M.updateRow b (fun c => alphabetPowerRemainder xs (N + cols c) l) =
      (fun a c : Fin j => alphabetPowerRemainder xs (N + cols c)
        (Function.update (fun a => xs.length - j + a.val) b l a)) := by
    ext a c
    by_cases ha : a = b
    · subst a
      simp
    · simp only [Matrix.updateRow_ne ha, Function.update_of_ne ha, M]
  rw [remainderRowMinor, ← hm, ← determinant_row_cramer]
  simp only [remainderCramerPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, alphabetPowerRemainder, M, mul_comm]

/-- In the selected top rows the Cramer polynomial has exactly one nonzero coefficient. -/
theorem remainderCramerPolynomial_top_coeff (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (b a : Fin j) :
    (remainderCramerPolynomial xs N j cols b).coeff (xs.length - j + a.val) =
      if a = b then remainderTopMinor xs N j cols else 0 := by
  classical
  let M : Matrix (Fin j) (Fin j) A := fun a c =>
    alphabetPowerRemainder xs (N + cols c) (xs.length - j + a.val)
  have h := congrFun (Matrix.mulVec_cramer M (Pi.single b 1)) a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    mul_ite, mul_one, mul_zero] at h
  simpa only [remainderCramerPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C, alphabetPowerRemainder, remainderTopMinor, M, mul_comm] using h

/-- Cramer uses only polynomial multiples of the characteristic and of the cutoff power. -/
theorem remainderCramerPolynomial_mem (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (b : Fin j) :
    remainderCramerPolynomial xs N j cols b ∈
      Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  classical
  unfold remainderCramerPolynomial
  apply Ideal.sum_mem
  intro c hc
  apply Ideal.mul_mem_left
  rw [Polynomial.modByMonic_eq_sub_mul_div]
  apply Ideal.sub_mem
  · rw [pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- No coefficient at or above the characteristic degree survives in the Cramer polynomial. -/
theorem remainderCramerPolynomial_coeff_of_large (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (b : Fin j) (l : ℕ) (hl : xs.length ≤ l) :
    (remainderCramerPolynomial xs N j cols b).coeff l = 0 := by
  nontriviality A
  simp only [remainderCramerPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro c hc
  have hd := Polynomial.degree_modByMonic_lt (Polynomial.X ^ (N + cols c))
    (alphabetCharacteristic_monic xs)
  rw [Polynomial.degree_eq_natDegree (alphabetCharacteristic_monic xs).ne_zero,
    alphabetCharacteristic_natDegree] at hd
  have hl' : (xs.length : WithBot ℕ) ≤ (l : WithBot ℕ) := by exact_mod_cast hl
  rw [Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hd hl'), mul_zero]

/-- The correction to the top monomial has coefficients in the all-row minor ideal. -/
theorem remainderCramerPolynomial_correction_coeff_mem (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (b : Fin j) (l : ℕ) :
    (remainderCramerPolynomial xs N j cols b -
      Polynomial.C (remainderTopMinor xs N j cols) *
        Polynomial.X ^ (xs.length - j + b.val)).coeff l ∈ remainderAllIdeal xs N j := by
  rw [Polynomial.coeff_sub, remainderCramerPolynomial_coeff, Polynomial.coeff_C_mul]
  apply (remainderAllIdeal xs N j).sub_mem (remainderRowMinor_mem _ _ _ _ _)
  exact Ideal.mul_mem_right _ _
    (remainderTopIdeal_le_allIdeal xs N j (remainderTopMinor_mem xs N j cols))

/-- Subtracting the first top-row monomial leaves only strictly lower powers. -/
theorem remainderCramerPolynomial_correction_degree (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (hj : 0 < j) (hjr : j ≤ xs.length) :
    (remainderCramerPolynomial xs N j cols ⟨0, hj⟩ -
      Polynomial.C (remainderTopMinor xs N j cols) *
        Polynomial.X ^ (xs.length - j)).degree < (xs.length - j : WithBot ℕ) := by
  classical
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro l hl
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hlr : l < xs.length
  · let a : Fin j := ⟨l - (xs.length - j), by omega⟩
    have ha : xs.length - j + a.val = l := by dsimp [a]; omega
    rw [← ha, remainderCramerPolynomial_top_coeff]
    by_cases haz : a = (⟨0, hj⟩ : Fin j)
    · subst a
      simp
    · have hne : xs.length - j + a.val ≠ xs.length - j := by
        have hv : a.val ≠ 0 := fun h => haz (Fin.ext h)
        omega
      simp only [if_neg haz, if_neg hne, mul_zero, sub_self]
  · rw [remainderCramerPolynomial_coeff_of_large xs N j cols ⟨0, hj⟩ l (by omega)]
    have hne : l ≠ xs.length - j := by omega
    simp only [if_neg hne, mul_zero, sub_self]

/-- Cramer produces a lower-power correction in the all-row ideal modulo the two relations. -/
theorem remainderTopMinor_cramer_certificate (xs : List A) (N j : ℕ)
    (cols : Fin j → ℕ) (hj : 0 < j) (hjr : j ≤ xs.length) :
    ∃ p : Polynomial A,
      p.degree < (xs.length - j : WithBot ℕ) ∧
      (∀ l, p.coeff l ∈ remainderAllIdeal xs N j) ∧
      Polynomial.C (remainderTopMinor xs N j cols) * Polynomial.X ^ (xs.length - j) + p ∈
        Ideal.span {alphabetCharacteristic xs, Polynomial.X ^ N} := by
  let p := remainderCramerPolynomial xs N j cols ⟨0, hj⟩ -
    Polynomial.C (remainderTopMinor xs N j cols) * Polynomial.X ^ (xs.length - j)
  refine ⟨p, remainderCramerPolynomial_correction_degree xs N j cols hj hjr, ?_, ?_⟩
  · intro l
    simpa only [Fin.val_zero, Nat.add_zero] using
      remainderCramerPolynomial_correction_coeff_mem xs N j cols ⟨0, hj⟩ l
  · have he : Polynomial.C (remainderTopMinor xs N j cols) *
        Polynomial.X ^ (xs.length - j) + p =
        remainderCramerPolynomial xs N j cols ⟨0, hj⟩ := by dsimp [p]; ring
    rw [he]
    exact remainderCramerPolynomial_mem xs N j cols ⟨0, hj⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_mem
#print axioms VOA.DeligneAudit.SL4T.remainderTopIdeal_le_allIdeal
#print axioms VOA.DeligneAudit.SL4T.determinant_row_cramer
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_coeff
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_top_coeff
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_mem
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_coeff_of_large
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_correction_coeff_mem
#print axioms VOA.DeligneAudit.SL4T.remainderCramerPolynomial_correction_degree

#print axioms VOA.DeligneAudit.SL4T.remainderTopMinor_cramer_certificate
