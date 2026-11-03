/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroKacSingularTransfer
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Actual Gram determinants on the Laurent Kac curve

Both charge and highest weight are Laurent polynomials in the Kac parameter.
Consequently an actual determinant that vanishes at infinitely many distinct
nonzero parameters vanishes identically on the curve. This needs no density,
continuity of chosen singular vectors, or evaluation of a fraction at a pole.
It does not construct the required infinite set of roots.
-/
namespace VOA.InverseDS.VirasoroVerma
open scoped LaurentPolynomial Classical

/-- Evaluate a Laurent polynomial at a nonzero parameter. The unit proof
makes the inverse parameter legitimate, rather than Lean's total inverse at zero. -/
noncomputable def kacLaurentEval (t : ℂ) (ht : t ≠ 0) : ℂ[T;T⁻¹] →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 t ht)

/-- Laurent evaluation agrees with ordinary polynomial evaluation. -/
theorem kacLaurentEval_polynomial (t : ℂ) (ht : t ≠ 0) (P : Polynomial ℂ) :
    kacLaurentEval t ht (Polynomial.toLaurent P) = P.eval t := by
  simp [kacLaurentEval,LaurentPolynomial.eval₂_toLaurent,Polynomial.eval₂_at_apply]

/-- A Laurent polynomial with infinitely many distinct nonzero roots is
zero. Multiplying by a power of T clears negative exponents; the ordinary
polynomial root theorem applies, and that power is a unit. -/
theorem kacLaurent_eq_zero_of_infinite (P : ℂ[T;T⁻¹]) (S : Set ℂ)
    (hS : S.Infinite) (hne : ∀ t ∈ S, t ≠ 0)
    (hz : ∀ t (ht : t ∈ S), kacLaurentEval t (hne t ht) P = 0) : P = 0 := by
  obtain ⟨n,Q,hQ⟩ := LaurentPolynomial.exists_T_pow P
  have hq : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro t ht
    change Q.eval t = 0
    rw [← kacLaurentEval_polynomial t (hne t ht),hQ,map_mul,hz t ht,zero_mul]
  rw [hq,map_zero] at hQ
  exact (LaurentPolynomial.isUnit_T (R := ℂ) (n:ℤ)).mul_right_eq_zero.mp (by simpa only [mul_comm] using hQ.symm)

/-- Central charge 13-6T-6/T as a genuine Laurent polynomial. -/
noncomputable def kacLaurentCharge : ℂ[T;T⁻¹] :=
  LaurentPolynomial.C 13 - LaurentPolynomial.C 6 * LaurentPolynomial.T 1 -
    LaurentPolynomial.C 6 * LaurentPolynomial.T (-1)

/-- The two-label highest weight written without division by a polynomial:
its numerator is multiplied by T inverse and the scalar one quarter. -/
noncomputable def kacLaurentWeight (r s : ℕ) : ℂ[T;T⁻¹] :=
  LaurentPolynomial.C (1/4) * LaurentPolynomial.T (-1) *
    ((LaurentPolynomial.C (r:ℂ) * LaurentPolynomial.T 1 - LaurentPolynomial.C (s:ℂ))^2 -
      (LaurentPolynomial.T 1 - 1)^2)

/-- Laurent charge evaluation is exactly the actual Kac charge. -/
theorem kacLaurentCharge_eval (t : ℂ) (ht : t ≠ 0) :
    kacLaurentEval t ht kacLaurentCharge = vermaBSACharge t := by
  simp [kacLaurentEval,kacLaurentCharge,vermaBSACharge,div_eq_mul_inv]

/-- Laurent weight evaluation is exactly the actual two-label weight. -/
theorem kacLaurentWeight_eval (r s : ℕ) (t : ℂ) (ht : t ≠ 0) :
    kacLaurentEval t ht (kacLaurentWeight r s) = fusionKacWeight r s t := by
  simp [kacLaurentEval,kacLaurentWeight,fusionKacWeight]
  field_simp
  <;> ring

/-- Substitute the Laurent charge and weight into the ACTUAL universal
Verma Gram determinant, at any level. This is not the conjectured Kac product. -/
noncomputable def kacGramLaurent (r s n : ℕ) : ℂ[T;T⁻¹] :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C
    (fun i : Fin 2 => if i=0 then kacLaurentCharge else kacLaurentWeight r s)
    (vermaGramPolynomial n).det

/-- Specializing the Laurent determinant gives the ACTUAL canonical Gram
determinant at that charge and highest weight, not merely a formal analogue. -/
theorem kacGramLaurent_eval (r s n : ℕ) (t : ℂ) (ht : t ≠ 0) :
    kacLaurentEval t ht (kacGramLaurent r s n) =
      (vermaGramMatrix (vermaBSACharge t) (fusionKacWeight r s t) n).det := by
  rw [kacGramLaurent,MvPolynomial.map_eval₂Hom]
  have hc : (kacLaurentEval t ht).comp LaurentPolynomial.C = RingHom.id ℂ := by
    ext a
    simp [kacLaurentEval]
  rw [hc]
  have hf : (fun i : Fin 2 => kacLaurentEval t ht
      (if i=0 then kacLaurentCharge else kacLaurentWeight r s)) =
      (fun i : Fin 2 => if i=0 then vermaBSACharge t else fusionKacWeight r s t) := by
    funext i
    split_ifs <;> simp only [kacLaurentCharge_eval,kacLaurentWeight_eval]
  rw [hf]
  exact vermaGramPolynomial_det_eval _ _ n

/-- Infinitely many actual Gram roots on a fixed Kac curve force a root at
every nonzero parameter. The sample set need not be dense or have a finite
accumulation point. Such roots are constructed in
`VirasoroScreening.infinite_integer_screening_roots`. -/
theorem kacGram_root_of_infinite (r s n : ℕ) (S : Set ℂ) (hS : S.Infinite)
    (hne : ∀ t ∈ S, t ≠ 0)
    (hz : ∀ t ∈ S, (vermaGramMatrix (vermaBSACharge t)
      (fusionKacWeight r s t) n).det = 0) (t : ℂ) (ht : t ≠ 0) :
    (vermaGramMatrix (vermaBSACharge t) (fusionKacWeight r s t) n).det = 0 := by
  have he : kacGramLaurent r s n = 0 := kacLaurent_eq_zero_of_infinite _ S hS hne
    (fun z hzS => (kacGramLaurent_eval r s n z (hne z hzS)).trans (hz z hzS))
  rw [← kacGramLaurent_eval r s n t ht,he,map_zero]

end VOA.InverseDS.VirasoroVerma
