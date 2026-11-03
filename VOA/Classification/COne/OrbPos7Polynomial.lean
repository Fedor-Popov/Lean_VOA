import VOA.Classification.COne.OrbPos6Slice
import VOA.Moonshine.LatticeTwistedGeneralProduct

/-! # Polynomial-valued states evaluated as shifted ordinary fields -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open scoped TensorProduct

noncomputable def ordinaryLinear (j β : ℤ) : Osc →ₗ[ℂ] Fld Space where
  toFun p := ordinaryField j (latStateGen (latP 1) p β)
  map_add' p q := by apply Subtype.ext; simp [ordinaryField, latStateGen_add_boson]
  map_smul' c p := by apply Subtype.ext; simp [ordinaryField, latStateGen_smul_boson]

noncomputable def shiftLinear (k : ℤ) : Fld Space →ₗ[ℂ] Fld Space where
  toFun := fzmul k
  map_add' := fzmul_add k
  map_smul' c p := fzmul_smul k c p

/-- Evaluate `p_d w^d` as `z^(-d) Y_j(p_d e^β,z)`. -/
noncomputable def polynomialField (j β : ℤ) : Polynomial Osc →ₗ[ℂ] Fld Space :=
  (Finsupp.lsum ℂ fun d : ℕ => (shiftLinear (-(d : ℤ))).comp (ordinaryLinear j β)).comp
    ((Polynomial.toFinsuppIsoLinear Osc).restrictScalars ℂ).toLinearMap

@[simp] theorem polynomialField_monomial (j β : ℤ) (d : ℕ) (p : Osc) :
    polynomialField j β (Polynomial.monomial d p) =
      fzmul (-(d : ℤ)) (ordinaryField j (latStateGen (latP 1) p β)) := by
  change (Finsupp.lsum ℂ _) (Finsupp.single d p) = _
  rw [Finsupp.lsum_single]
  rfl

@[simp] theorem polynomialField_C (j β : ℤ) (p : Osc) :
    polynomialField j β (Polynomial.C p) = ordinaryField j (latStateGen (latP 1) p β) := by
  simpa using polynomialField_monomial j β 0 p

theorem polynomialField_X_mul (j β : ℤ) (k : ℕ) (P : Polynomial Osc) :
    polynomialField j β (Polynomial.X ^ k * P) =
      fzmul (-(k : ℤ)) (polynomialField j β P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, map_add, hp, hq, fzmul_add]
  | monomial d p =>
    rw [Polynomial.X_pow_mul_monomial, polynomialField_monomial,
      polynomialField_monomial, fzmul_fzmul]
    congr 1
    push_cast
    ring

theorem polynomialField_C_mul (j β : ℤ) (c : ℂ) (P : Polynomial Osc) :
    polynomialField j β (Polynomial.C (MvPolynomial.C c) * P) =
      c • polynomialField j β P := by
  rw [show Polynomial.C (MvPolynomial.C c) * P = c • P from (Algebra.smul_def c P).symm,
    map_smul]

/-- The finite polynomial substitution is exactly the compatible rescaled field. -/
theorem resc_sector_polynomial {n : ℕ} (hn : 0 < n) (a j β e : ℤ)
    (he : (e - a * β) % (n : ℤ) = 0) (p : Osc) :
    rescFld hn (shiftedY_truncation hn a j (latStateGen (latP 1) p β)) e =
      fzmul ((e-a*β)/(n : ℤ))
        (polynomialField j β (delta ((a : ℂ)/(2*n)) p)) := by
  apply Subtype.ext
  change rescaleLinear n e (shiftedY n a j (latStateGen (latP 1) p β)) = _
  rw [shiftedY_latState]
  change rescaleLinear n e ((Finsupp.lsum ℂ (coefficientField n a j β))
    (deltaCoeffs ((a : ℂ)/(2*n)) p)) = _
  change rescaleLinear n e ((Finsupp.lsum ℂ (coefficientField n a j β))
    (deltaCoeffs ((a : ℂ)/(2*n)) p)) =
    (fzmul ((e-a*β)/(n : ℤ)) ((Finsupp.lsum ℂ fun d : ℕ =>
      (shiftLinear (-(d : ℤ))).comp (ordinaryLinear j β))
        (deltaCoeffs ((a : ℂ)/(2*n)) p))).1
  generalize deltaCoeffs ((a : ℂ)/(2*n)) p = f
  induction f using Finsupp.induction_linear with
  | zero => simp [fzmul_zero]
  | add f g hf hg => simp only [map_add, hf, hg, fzmul_add, Fld.add_val]
  | single d p =>
    rw [Finsupp.lsum_single, Finsupp.lsum_single]
    change resc (coefficientField n a j β d p) n e = _
    rw [resc_coefficientField hn, if_pos he]
    change _ = (fzmul ((e-a*β)/(n : ℤ)) (fzmul (-(d : ℤ)) (ordinaryField j _))).1
    rw [fzmul_fzmul, sub_eq_add_neg]
    rfl

end VOA.Classification.COne.OrbPos7
