import VOA.DeligneAudit.SL4TMomentMinorSpan

/-! # Polynomial changes of rows in moment determinants -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Rowwise finite linear combinations preserve membership of determinants in an ideal. -/
theorem determinant_row_sum_mem {j : ℕ} {ι : Type*} (I : Ideal A)
    (s : Fin j → Finset ι) (c : Fin j → ι → A) (v : ι → Fin j → A)
    (hv : ∀ d : Fin j → ι, Matrix.det (fun a b => v (d a) b) ∈ I) :
    Matrix.det (fun a b => ∑ n ∈ s a, c a n * v n b) ∈ I := by
  classical
  have he : (fun a b => ∑ n ∈ s a, c a n * v n b) =
      (fun a => ∑ n ∈ s a, c a n • v n) := by
    ext a b
    simp
  rw [he]
  change Matrix.detRowAlternating.toMultilinearMap _ ∈ I
  rw [MultilinearMap.map_sum_finset]
  apply I.sum_mem
  intro d hd
  change Matrix.det (fun a b => c a (d a) * v (d a) b) ∈ I
  have hdet := Matrix.det_mul_column (fun a => c a (d a)) (fun a b => v (d a) b)
  change Matrix.det (fun a b => c a (d a) * v (d a) b) = _ at hdet
  rw [hdet]
  exact I.mul_mem_left _ (hv d)

/-- Passing from a family of columns to its linear span does not enlarge the minor ideal. -/
theorem determinant_columns_span_mem {j : ℕ} {ι : Type*} (I : Ideal A)
    (v : ι → Fin j → A)
    (hv : ∀ d : Fin j → ι, Matrix.det (fun a b => v (d b) a) ∈ I)
    (p : Fin j → Fin j → A) (hp : ∀ b, p b ∈ Submodule.span A (Set.range v)) :
    Matrix.det (fun a b => p b a) ∈ I := by
  classical
  choose c hc using fun b => Finsupp.mem_span_range_iff_exists_finsupp.mp (hp b)
  have he : p = fun b => ∑ n ∈ (c b).support, c b n • v n := by
    funext b
    exact (hc b).symm
  rw [← Matrix.det_transpose]
  change Matrix.det p ∈ I
  rw [he]
  have h := determinant_row_sum_mem I (fun b => (c b).support) (fun b n => c b n) v
    (fun d => by
      have h := hv d
      rw [← Matrix.det_transpose] at h
      exact h)
  convert h using 1
  congr 1
  ext a b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Consecutive translated powers control determinants of arbitrary polynomial rows. -/
theorem polynomial_functional_determinant_mem {j : ℕ}
    (L : Fin j → Polynomial A →ₗ[A] A) (I : Ideal A)
    (hI : ∀ d : Fin j → ℕ,
      Matrix.det (fun a b : Fin j => L b (Polynomial.X ^ (d b + a.val))) ∈ I)
    (q : Fin j → Polynomial A) : Matrix.det (fun a b => L b (q a)) ∈ I := by
  classical
  have he (a b : Fin j) : L b (q a) =
      ∑ n ∈ (q a).support, (q a).coeff n * L b (Polynomial.X ^ n) := by
    conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq (q a)]
    simp only [Polynomial.sum, map_sum, ← Polynomial.smul_eq_C_mul,
      map_smul, smul_eq_mul]
  simp_rw [he]
  apply determinant_row_sum_mem
  intro rows
  exact moment_determinant_mem_of_consecutive
    (fun b n => L b (Polynomial.X ^ n)) I hI rows

/-- Replacing consecutive powers by monic polynomials of the same degrees
does not change a determinant of linear functionals. -/
theorem polynomial_functional_determinant_monic {j : ℕ}
    (L : Fin j → Polynomial A →ₗ[A] A) (q : Fin j → Polynomial A)
    (hq : ∀ a, (q a).Monic) (hd : ∀ a, (q a).natDegree = a.val) :
    Matrix.det (fun a b => L b (q a)) =
      Matrix.det (fun a b : Fin j => L b (Polynomial.X ^ a.val)) := by
  classical
  let C : Matrix (Fin j) (Fin j) A := fun a d => (q a).coeff d.val
  let M : Matrix (Fin j) (Fin j) A := fun d b => L b (Polynomial.X ^ d.val)
  have hC : C.det = 1 := by
    rw [← Matrix.det_transpose]
    exact Matrix.det_matrixOfPolynomials q hd hq
  have he : (fun a b => L b (q a)) = C * M := by
    ext a b
    rw [Matrix.mul_apply]
    have hp := Polynomial.as_sum_range_C_mul_X_pow' (q a)
      (show (q a).natDegree < j by rw [hd]; exact a.isLt)
    rw [hp]
    simp only [map_sum, ← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  rw [he, Matrix.det_mul, hC, one_mul]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.determinant_row_sum_mem
#print axioms VOA.DeligneAudit.SL4T.determinant_columns_span_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_functional_determinant_mem
#print axioms VOA.DeligneAudit.SL4T.polynomial_functional_determinant_monic
