import VOA.DeligneAudit.SL4TThomPolynomial

/-! Polynomial identities for removing two roots while lowering the current cutoff once. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {R : Type*} [CommRing R]

/-- Dividing a characteristic factorization by the variable gives the shortened cutoff. -/
theorem characteristic_complement_shortened (p q u : R[X]) (N : ℕ)
    (h : (p * q) * u = X ^ (N + 1)) :
    Polynomial.C (u.coeff 0) * (p * q).divX ∈ relationIdeal p q N := by
  have he := polynomial_complement_divX (p * q) u N h
  have hid : Polynomial.C (u.coeff 0) * (p * q).divX =
      X ^ N - u.divX * (p * q) := by linear_combination -he
  rw [hid]
  exact (relationIdeal p q N).sub_mem (relationIdeal_power p q N)
    ((relationIdeal p q N).mul_mem_left _ (relationIdeal_product p q N))

/-- Two distinct removed roots leave two boundary terms besides the divided characteristic. -/
theorem polynomial_two_distinct_removals (p q : R[X]) (z : R) :
    Polynomial.C z * X * p.divX * q.divX =
      Polynomial.C z * (p * q).divX -
        Polynomial.C (z * p.coeff 0) * q.divX -
          Polynomial.C (z * q.coeff 0) * p.divX := by
  rw [polynomial_divX_mul]
  have hq := X_mul_divX_add q
  simp only [map_mul]
  linear_combination Polynomial.C z * p.divX * hq

/-- The distinct-root term vanishes modulo the preceding cells and the shortened cutoff. -/
theorem polynomial_two_distinct_removals_mem (p q u : R[X]) (N : ℕ) (I : Ideal R)
    (h : (p * q) * u = X ^ (N + 1))
    (hp : u.coeff 0 * p.coeff 0 ∈ I) (hq : u.coeff 0 * q.coeff 0 ∈ I) :
    Polynomial.C (u.coeff 0) * X * p.divX * q.divX ∈
      relationIdeal p q N ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q N ⊔ I.map Polynomial.C
  have hA : relationIdeal p q N ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  rw [polynomial_two_distinct_removals]
  exact J.sub_mem (J.sub_mem (hA (characteristic_complement_shortened p q u N h))
    (J.mul_mem_right _ (hI (Ideal.mem_map_of_mem Polynomial.C hp))))
    (J.mul_mem_right _ (hI (Ideal.mem_map_of_mem Polynomial.C hq)))

/-- Removing two roots from the same factor leaves its constant and linear coefficients. -/
theorem polynomial_two_equal_removals (p q : R[X]) (z : R) :
    Polynomial.C z * X * p.divX.divX * q =
      Polynomial.C z * (p * q).divX -
        Polynomial.C (z * p.coeff 0) * q.divX -
          Polynomial.C (z * p.coeff 1) * q := by
  rw [polynomial_divX_mul]
  have hp := X_mul_divX_add p.divX
  rw [coeff_divX, Nat.zero_add] at hp
  simp only [map_mul]
  linear_combination Polynomial.C z * q * hp

/-- A repeated-root term is controlled by the constant boundary and the linear tail relation. -/
theorem polynomial_two_equal_removals_mem (p q u : R[X]) (N : ℕ) (I : Ideal R) (v : R)
    (h : (p * q) * u = X ^ (N + 1))
    (hp : v * u.coeff 0 * p.coeff 0 ∈ I)
    (hlinear : v * u.coeff 0 * p.coeff 1 ∈ I) :
    Polynomial.C (v * u.coeff 0) * X * p.divX.divX * q ∈
      relationIdeal p q N ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q N ⊔ I.map Polynomial.C
  have hA : relationIdeal p q N ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  have hmain : Polynomial.C (v * u.coeff 0) * (p * q).divX ∈ J := by
    rw [map_mul, mul_assoc]
    exact J.mul_mem_left _ (hA (characteristic_complement_shortened p q u N h))
  rw [polynomial_two_equal_removals]
  exact J.sub_mem (J.sub_mem hmain
    (J.mul_mem_right _ (hI (Ideal.mem_map_of_mem Polynomial.C hp))))
    (J.mul_mem_right _ (hI (Ideal.mem_map_of_mem Polynomial.C hlinear)))

/-- If neither removed root is retained, the old cutoff term is killed by the constant class. -/
theorem polynomial_no_retained_removal_mem (p q : R[X]) (n : ℕ) (v : R) :
    Polynomial.C (v * (p * q).coeff 0) * X ^ n ∈ relationIdeal p q (n + 1) := by
  rw [mul_coeff_zero, map_mul, mul_assoc]
  exact (relationIdeal p q (n + 1)).mul_mem_left _ (polynomial_nn_mem p q n)

/-- A single retained root only needs its ordinary boundary relation. -/
theorem polynomial_one_retained_removal_mem (p q : R[X]) (N : ℕ) (I : Ideal R)
    (v : R) (hp : v * p.coeff 0 ∈ I) :
    Polynomial.C v * X * p.divX * q ∈ relationIdeal p q N ⊔ I.map Polynomial.C := by
  let J := relationIdeal p q N ⊔ I.map Polynomial.C
  have hA : relationIdeal p q N ≤ J := le_sup_left
  have hI : I.map Polynomial.C ≤ J := le_sup_right
  have he : Polynomial.C v * X * p.divX * q =
      Polynomial.C v * (p * q) - Polynomial.C (v * p.coeff 0) * q := by
    have hp := X_mul_divX_add p
    rw [map_mul]
    linear_combination Polynomial.C v * q * hp
  rw [he]
  exact J.sub_mem (J.mul_mem_left _ (hA (relationIdeal_product p q N)))
    (J.mul_mem_right _ (hI (Ideal.mem_map_of_mem Polynomial.C hp)))

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.characteristic_complement_shortened
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_distinct_removals
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_distinct_removals_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_equal_removals
#print axioms VOA.DeligneAudit.SL4T.polynomial_two_equal_removals_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_no_retained_removal_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_one_retained_removal_mem
