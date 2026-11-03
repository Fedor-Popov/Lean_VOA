/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningVandermonde

/-!
# A nonzero finite integer-screening moment

The actual finite coefficient functional, with the Vandermonde weight and
uniform residue exponent, detects the product of all auxiliary variables.
Newton's identities give a homogeneous power-sum witness. Hence this is an
unconditional nonzero moment at all ranks and integer parameters, not an
assumed nonvanishing input. Constructing its Fock state and proving the Ward
identities are separate steps.
-/
namespace VOA.VirasoroScreening
open AddMonoidAlgebra
open scoped BigOperators

/-- Embed ordinary auxiliary-variable polynomials into finite Laurent
expressions by sending each variable to its unit exponent monomial. -/
noncomputable def auxiliaryLaurent (r : ℕ) :
    MvPolynomial (Fin r) ℚ →ₐ[ℚ] Laurent (Fin r → ℤ) :=
  MvPolynomial.aeval (fun i => single (unitExponent r i) 1)

/-- The finite residue functional of the proposed integer screening. It
extracts exponent (r-1)t+s in each variable after multiplication by Delta^(2t).
It is defined for every polynomial, with no infinite-series convention. -/
noncomputable def screeningMoment (r s t : ℕ) (P : MvPolynomial (Fin r) ℚ) : ℚ :=
  (vandermondeLaurent r^(2*t) * auxiliaryLaurent r P)
    (fun _ : Fin r => (((r-1)*t+s:ℕ):ℤ))

/-- The product of all auxiliary variables to power s becomes the single
Laurent monomial with exponent s in each coordinate. -/
theorem auxiliaryLaurent_product (r s : ℕ) :
    auxiliaryLaurent r ((∏ i : Fin r, (MvPolynomial.X i : MvPolynomial (Fin r) ℚ))^s) =
      single (fun _ : Fin r => (s:ℤ)) 1 := by
  classical
  simp only [auxiliaryLaurent,map_pow,map_prod,MvPolynomial.aeval_X]
  rw [AddMonoidAlgebra.prod_single,AddMonoidAlgebra.single_pow]
  simp only [Finset.prod_const_one,one_pow]
  congr 1
  funext k
  simp [unitExponent,Finset.sum_apply,Pi.single_apply]

/-- The product-variable test reduces the residue precisely to the middle
Vandermonde coefficient, with no normalization factor to be guessed. -/
theorem screeningMoment_product (r s t : ℕ) :
    screeningMoment r s t ((∏ i : Fin r,
      (MvPolynomial.X i : MvPolynomial (Fin r) ℚ))^s) =
      (vandermondeLaurent r^(2*t)) (fun _ : Fin r => (((r-1)*t:ℕ):ℤ)) := by
  rw [screeningMoment,auxiliaryLaurent_product,mul_single_apply,mul_one]
  congr 1
  funext k
  simp

/-- The residue functional is nonzero on the product-variable test for
all r,s,t. This is the finite sum-of-squares nonvanishing argument applied
to the exact proposed screening weight. -/
theorem screeningMoment_product_ne_zero (r s t : ℕ) :
    screeningMoment r s t ((∏ i : Fin r,
      (MvPolynomial.X i : MvPolynomial (Fin r) ℚ))^s) ≠ 0 := by
  rw [screeningMoment_product]
  exact vandermonde_central_coefficient_ne_zero r t

/-- At every rank and integer parameter the actual finite residue is
nonzero on some homogeneous expression in positive power sums of degree rs.
This combines the proved Newton witness with the exact Vandermonde moment.
It is not yet a Virasoro singular state or a Gram determinant root. -/
theorem screeningMoment_powerSum_witness (r s t : ℕ) :
    ∃ P : MvPolynomial ℕ ℚ,
      P.IsWeightedHomogeneous (fun i => i+1) (r*s) ∧
      screeningMoment r s t (powerSumSubstitution (Fin r) P) ≠ 0 := by
  obtain ⟨P,hP,hE⟩ := exists_weighted_product_witness r s
  exact ⟨P,hP,by rw [hE]; exact screeningMoment_product_ne_zero r s t⟩

end VOA.VirasoroScreening
