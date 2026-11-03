import VOA.DeligneAudit.D4CharLeviPoly

/-! The all-n total of the degree-wise D4 Levi sum: (L3). -/

namespace VOA.DeligneAudit.D4Char

open Polynomial VOA.DeligneGaussian
open scoped BigOperators

noncomputable section

def qmultiPoly (t : Fin 4 → ℕ) : ℚ[X] :=
  qbinom X (∑ i, t i) (t 3) * qbinom X (t 0 + t 1 + t 2) (t 2) *
    qbinom X (t 0 + t 1) (t 0)

def d4LeviPoly (n : ℕ) : ℚ[X] :=
  ∑ t ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 4)) n,
    qmultiPoly t * gl4Poly (2 * t 0 + (t 1 + t 2)) (t 0 + (t 1 + t 2)) (t 0) 0

theorem coeff_qmultiPoly (t : Fin 4 → ℕ) (N : ℕ) :
    (qmultiPoly t).coeff N = (qmultiCoeff t N : ℚ) :=
  A2.coeff_mul_eq_convQ
    (fun M => A2.coeff_mul_eq_convQ
      (A2.coeff_qbinom_X _ _) (A2.coeff_qbinom_X _ _) M)
    (A2.coeff_qbinom_X _ _) N

theorem coeff_d4LeviPoly (n N : ℕ) :
    (d4LeviPoly n).coeff N = (d4LeviHilb n N : ℚ) := by
  simp only [d4LeviPoly, d4LeviHilb, finsetSum_coeff, Nat.cast_sum]
  exact Finset.sum_congr rfl fun t _ =>
    A2.coeff_mul_eq_convQ (coeff_qmultiPoly t) (coeff_gl4Poly _ _ _ _) N

/-- Evaluation of the Gaussian multinomial is the ordinary multinomial. -/
theorem qmultiPoly_eval_one (t : Fin 4 → ℕ) :
    (qmultiPoly t).eval 1 = (Nat.multinomial Finset.univ t : ℚ) := by
  have hm : Nat.multinomial (Finset.univ : Finset (Fin 4)) t =
      (t 0 + t 1 + t 2 + t 3).choose (t 3) *
        (t 0 + t 1 + t 2).choose (t 2) * (t 0 + t 1).choose (t 0) := by
    rw [show (Finset.univ : Finset (Fin 4)) =
      insert 3 (insert 2 (insert 0 {1})) by decide]
    rw [Nat.multinomial_insert (by decide), Nat.multinomial_insert (by decide),
      Nat.multinomial_insert (by decide)]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton,
      Nat.multinomial_singleton, mul_one]
    rw [show t 3 + (t 2 + (t 0 + t 1)) = t 0 + t 1 + t 2 + t 3 by omega,
      show t 2 + (t 0 + t 1) = t 0 + t 1 + t 2 by omega]
    ring
  simp only [qmultiPoly, eval_mul, A2.eval_one_qbinom, hm, Nat.cast_mul]
  congr 3
  simp [Fin.sum_univ_succ, add_assoc]

/-- Weights of the four multiplicity classes. -/
def classValue : Fin 4 → ℚ := ![16, 6, 6, 1]

theorem gl4Poly_class_eval (t : Fin 4 → ℕ) :
    (gl4Poly (2 * t 0 + (t 1 + t 2)) (t 0 + (t 1 + t 2)) (t 0) 0).eval 1 =
      ∏ i : Fin 4, classValue i ^ t i := by
  rw [gl4Poly_eval_one _ _ _ _ (by omega) (by omega) (by omega)]
  rw [show 2 * t 0 + (t 1 + t 2) - (t 0 + (t 1 + t 2)) = t 0 by omega,
    show t 0 + (t 1 + t 2) - t 0 = t 1 + t 2 by omega, Nat.sub_zero]
  simp only [classValue, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one, one_pow, pow_add]
  change (4 : ℚ) ^ t 0 * (6 ^ t 1 * 6 ^ t 2) * 4 ^ t 0 =
    16 ^ t 0 * (6 ^ t 1 * 6 ^ t 2)
  have hp : (4 : ℚ) ^ t 0 * 4 ^ t 0 = 16 ^ t 0 := by rw [← mul_pow]; norm_num
  linear_combination (6 ^ t 1 * 6 ^ t 2) * hp

/-- The total GL4 Levi polynomial is `29^n` at `q = 1`, for every n. -/
theorem d4LeviPoly_eval_one (n : ℕ) : (d4LeviPoly n).eval 1 = 29 ^ n := by
  simp only [d4LeviPoly, eval_finsetSum, eval_mul, qmultiPoly_eval_one,
    gl4Poly_class_eval]
  rw [← Finset.sum_pow_eq_sum_piAntidiag]
  congr 1
  norm_num [classValue, Fin.sum_univ_succ]

theorem sum_d4LeviHilb (n B : ℕ) (hB : (d4LeviPoly n).natDegree < B) :
    ∑ N ∈ Finset.range B, d4LeviHilb n N = 29 ^ n := by
  have h := d4LeviPoly_eval_one n
  rw [eval_eq_sum_range' hB] at h
  simp only [one_pow, mul_one, coeff_d4LeviPoly] at h
  exact_mod_cast h

/-- (L3): finite support and exact total `29^n`, with no bound on n. -/
theorem d4LeviHilb_sum (n : ℕ) :
    ∃ B : ℕ, (∀ N, B ≤ N → d4LeviHilb n N = 0) ∧
      ∑ N ∈ Finset.range B, d4LeviHilb n N = 29 ^ n := by
  refine ⟨(d4LeviPoly n).natDegree + 1, ?_, sum_d4LeviHilb n _ (by omega)⟩
  intro N hN
  have h := coeff_eq_zero_of_natDegree_lt (p := d4LeviPoly n) (n := N) (by omega)
  rw [coeff_d4LeviPoly] at h
  exact_mod_cast h

theorem leviTotalCount : LeviTotalCount := d4LeviHilb_sum

/-- (L3) in infinite-sum notation; finite support was proved above. -/
theorem d4LeviHilb_tsum (n : ℕ) : (∑' N : ℕ, d4LeviHilb n N) = 29 ^ n := by
  obtain ⟨B, hzero, hsum⟩ := d4LeviHilb_sum n
  rw [← hsum]
  apply tsum_eq_sum
  intro N hN
  exact hzero N (by simpa using hN)

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.coeff_qmultiPoly
#print axioms VOA.DeligneAudit.D4Char.coeff_d4LeviPoly
#print axioms VOA.DeligneAudit.D4Char.qmultiPoly_eval_one
#print axioms VOA.DeligneAudit.D4Char.gl4Poly_class_eval
#print axioms VOA.DeligneAudit.D4Char.d4LeviPoly_eval_one
#print axioms VOA.DeligneAudit.D4Char.sum_d4LeviHilb
#print axioms VOA.DeligneAudit.D4Char.d4LeviHilb_sum
#print axioms VOA.DeligneAudit.D4Char.leviTotalCount
#print axioms VOA.DeligneAudit.D4Char.d4LeviHilb_tsum
