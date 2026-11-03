import VOA.Classification.COne.OrbPos7Polynomial

/-! # Creation recursion for the inner-shifted lattice fields -/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.OrbPos7
open VOA VOA.IntegralLattice VOA.LatGen VOA.LatGen.Triplet VOA.HeisenbergN
open OrbPos2 OrbPos3 OrbPos4 OrbPos5 OrbPos6 LatMod TwistedReduction
open Moonshine.LatticeTwisted
open scoped TensorProduct

noncomputable abbrev h : Space := hgen (latP 1) (a0 1)

noncomputable def shiftedCurrent (j : ℤ) (t : ℂ) : Fld Space :=
  ordinaryField j h + (-t * rootCoord) • fzmul (-1) Fld.one

theorem prod_inverse_z_neg (k : ℕ) (F : Fld Space) :
    Fld.prod (-(k : ℤ)-1) (fzmul (-1) Fld.one) F =
      (-1 : ℂ)^k • fzmul (-(k : ℤ)-1) F := by
  rw [prod_fzmul_left (local_one_left F) (-1) (-(k : ℤ)-1) (k+1) (fun i hi => by
    rw [Fld.prod_one_left_all, if_neg (by omega)])]
  rw [Finset.sum_eq_single k]
  · rw [Fld.prod_one_left_all, if_pos (by omega), VOA.gBinom_neg_one]
    congr 2; ring
  · intro i _ hik
    rw [Fld.prod_one_left_all, if_neg (by omega), fzmul_zero, smul_zero]
  · intro hk
    exact (hk (Finset.mem_range.mpr (by omega))).elim

theorem prod_inverse_z_nonneg (ℓ : ℤ) (hℓ : 0 ≤ ℓ) (F : Fld Space) :
    Fld.prod ℓ (fzmul (-1) Fld.one) F = 0 := by
  rw [prod_fzmul_left (local_one_left F) (-1) ℓ 0 (fun i _ => by
    rw [Fld.prod_one_left_all, if_neg (by omega)]), Finset.sum_range_zero]

theorem ordinary_current_creation (j β : ℤ) (k : ℕ) (p : Osc) :
    Fld.prod (-(k : ℤ)-1) (ordinaryField j h)
      (ordinaryField j (latStateGen (latP 1) p β)) =
    ordinaryField j (latStateGen (latP 1) (MvPolynomial.X (k, a0 1) * p) β) := by
  rw [ordinaryField_prod]
  congr 1
  change (latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)).smul
    (hgen (latP 1) (a0 1)) (-(k : ℤ)-1) (p ⊗ₜ[ℂ] eGen (latP 1) β) = _
  rw [smul_hgen_neg, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply]
  rfl

theorem polynomialField_creation (j β : ℤ) (k : ℕ) (P : Polynomial Osc) :
    polynomialField j β (Polynomial.C (MvPolynomial.X (k, a0 1)) * P) =
      Fld.prod (-(k : ℤ)-1) (ordinaryField j h) (polynomialField j β P) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, map_add, Fld.prod_add_right, hp, hq]
  | monomial d p =>
    rw [Polynomial.C_mul_monomial, polynomialField_monomial, polynomialField_monomial,
      prod_fzmul_right, ordinary_current_creation]

/-- Δ multiplication by any oscillator is precisely the shifted-current
creation product, on every oscillator polynomial and every charge sector. -/
theorem delta_creation (j β : ℤ) (t : ℂ) (k : ℕ) (p : Osc) :
    polynomialField j β (delta t (MvPolynomial.X (k, a0 1) * p)) =
      Fld.prod (-(k : ℤ)-1) (shiftedCurrent j t)
        (polynomialField j β (delta t p)) := by
  rw [map_mul, delta_X, add_mul, map_add, polynomialField_creation]
  rw [mul_assoc, polynomialField_C_mul, polynomialField_X_mul,
    shiftedCurrent, Fld.prod_add_left, Fld.prod_smul_left, prod_inverse_z_neg]
  simp only [smul_smul, Nat.cast_add, Nat.cast_one, neg_add_rev]
  congr 1
  congr 2; ring

/-- Exact current field, including its scalar zero-mode correction. -/
theorem resc_current {n : ℕ} (hn : 0 < n) (a j : ℤ) :
    rescFld hn (shiftedY_truncation hn a j h) 0 =
      shiftedCurrent j ((a : ℂ)/(2*n)) := by
  change rescFld hn (shiftedY_truncation hn a j
    (latStateGen (latP 1) (MvPolynomial.X (0, a0 1)) 0)) 0 = _
  trans fzmul ((0-a*0)/(n : ℤ))
    (polynomialField j 0 (delta ((a : ℂ)/(2*n)) (MvPolynomial.X (0, a0 1))))
  · exact resc_sector_polynomial hn a j 0 0 (by simp) (MvPolynomial.X (0, a0 1))
  rw [show (0-a*0)/(n : ℤ) = 0 by simp, fzmul_zero_shift, delta_X]
  simp only [pow_zero, mul_one, zero_add, pow_one, map_add]
  rw [show Polynomial.C (MvPolynomial.C (-((a : ℂ)/(2*n)) * rootCoord)) * Polynomial.X =
    Polynomial.monomial 1 (MvPolynomial.C (-((a : ℂ)/(2*n)) * rootCoord)) by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one], polynomialField_monomial,
    polynomialField_C]
  change ordinaryField j h + fzmul (-1) (ordinaryField j
    (latStateGen (latP 1) (MvPolynomial.C _) 0)) = _
  have hc (c : ℂ) : ordinaryField j (latStateGen (latP 1) (MvPolynomial.C c) 0) =
      c • Fld.one := by
    apply Subtype.ext
    change (latticeModule 1 le_rfl j).YM (latStateGen (latP 1) (MvPolynomial.C c) 0) = _
    rw [show MvPolynomial.C c = c • (1 : Osc) by simp [Algebra.smul_def],
      latStateGen_smul_boson, map_smul]
    change c • (latticeModule 1 le_rfl j).YM (V2m 1 le_rfl).vacuum = _
    rw [(latticeModule 1 le_rfl j).vacuum_YM]
    rfl
  rw [hc, fzmul_smul]
  rfl

end VOA.Classification.COne.OrbPos7
