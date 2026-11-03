import VOA.DeligneAudit.SL4TRemainderCramer
import Mathlib.LinearAlgebra.Vandermonde

/-! # Integral factorization of polynomial alternants

Division by the monic polynomial with the evaluation points as roots factors every
evaluation determinant through the power evaluation matrix. This works over arbitrary
commutative rings, including rings with torsion and zero divisors.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Evaluating a polynomial at a root is unchanged by monic reduction. -/
theorem polynomial_eval_remainder_at_root (p P : Polynomial A) (x : A)
    (hx : P.eval x = 0) : (p %ₘ P).eval x = p.eval x := by
  simpa only [Polynomial.eval₂_id] using
    Polynomial.eval₂_modByMonic_eq_self_of_root (f := RingHom.id A) hx

/-- Every polynomial evaluation determinant is divisible by the power determinant.
The quotient is the determinant of the coefficients of the monic remainders. -/
theorem polynomial_evaluation_determinant_factor (j : ℕ)
    (q : Fin j → Polynomial A) (x : Fin j → A) :
    ∃ a : A, Matrix.det (fun i b : Fin j => (q i).eval (x b)) =
      a * Matrix.det (fun i b : Fin j => x b ^ i.val) := by
  classical
  let P : Polynomial A := ∏ b : Fin j, (Polynomial.X - Polynomial.C (x b))
  have hP : P.Monic := Polynomial.monic_prod_of_monic _ _
    (fun b _ => Polynomial.monic_X_sub_C (x b))
  have hd : P.degree ≤ (j : WithBot ℕ) := by
    nontriviality A
    rw [Polynomial.degree_eq_natDegree hP.ne_zero]
    have hn : P.natDegree = j := by
      dsimp [P]
      rw [Polynomial.natDegree_prod_of_monic _ _
        (fun b _ => Polynomial.monic_X_sub_C (x b))]
      simp
    rw [hn]
  have hx (b : Fin j) : P.eval (x b) = 0 := by
    simp only [P, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (sub_self _)
  let C : Matrix (Fin j) (Fin j) A := fun i a => (q i %ₘ P).coeff a.val
  let V : Matrix (Fin j) (Fin j) A := fun a b => x b ^ a.val
  have hm : (fun i b : Fin j => (q i).eval (x b)) = C * V := by
    ext i b
    rw [Matrix.mul_apply]
    have he := congrArg (fun p : Polynomial A => p.eval (x b))
      (Polynomial.sum_modByMonic_coeff (p := q i) hP hd)
    simpa only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, C, V,
      polynomial_eval_remainder_at_root (q i) P (x b) (hx b)] using he.symm
  exact ⟨C.det, by rw [hm, Matrix.det_mul]⟩

/-- A polynomial alternant in free variables has an integral power-alternant factor. -/
theorem polynomial_alternant_factor (j : ℕ) (q : Fin j → Polynomial A) :
    ∃ s : MvPolynomial (Fin j) A,
      Matrix.det (fun i b : Fin j =>
        Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X b) (q i)) =
      s * Matrix.det (fun i b : Fin j => (MvPolynomial.X b) ^ i.val) := by
  obtain ⟨s, hs⟩ := polynomial_evaluation_determinant_factor j
    (fun i => (q i).map MvPolynomial.C) (fun b => MvPolynomial.X b)
  exact ⟨s, by simpa only [Polynomial.eval_map] using hs⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomial_eval_remainder_at_root
#print axioms VOA.DeligneAudit.SL4T.polynomial_evaluation_determinant_factor
#print axioms VOA.DeligneAudit.SL4T.polynomial_alternant_factor
