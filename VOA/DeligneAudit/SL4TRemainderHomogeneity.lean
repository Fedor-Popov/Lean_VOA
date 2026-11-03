import VOA.DeligneAudit.SL4TRemainderTopCertificate
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous degrees of characteristic remainders

Integer degrees make the zero coefficients below their possible degree uniform.
Every root has degree one, while the polynomial variable also has degree one.
-/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {σ A : Type*} [CommRing A]

/-- A polynomial in a degree-one variable with homogeneous coefficient polynomials. -/
def polynomialCoefficientsHomogeneous (w : σ → ℤ)
    (p : Polynomial (MvPolynomial σ A)) (d : ℤ) : Prop :=
  ∀ l : ℕ, (p.coeff l).IsWeightedHomogeneous w (d - l)

theorem polynomialCoefficientsHomogeneous_constant (w : σ → ℤ)
    (a : MvPolynomial σ A) (d : ℤ) (ha : a.IsWeightedHomogeneous w d) :
    polynomialCoefficientsHomogeneous w (Polynomial.C a) d := by
  intro l
  by_cases hl : l = 0
  · subst l
    simpa only [Polynomial.coeff_C_zero, Nat.cast_zero, sub_zero] using ha
  · rw [Polynomial.coeff_C, if_neg hl]
    exact MvPolynomial.isWeightedHomogeneous_zero A w _

theorem polynomialCoefficientsHomogeneous_power (w : σ → ℤ) (m : ℕ) :
    polynomialCoefficientsHomogeneous w
      ((Polynomial.X : Polynomial (MvPolynomial σ A)) ^ m) m := by
  intro l
  rw [Polynomial.coeff_X_pow]
  by_cases hl : l = m
  · subst l
    simpa only [if_true, sub_self] using MvPolynomial.isWeightedHomogeneous_one A w
  · rw [if_neg hl]
    exact MvPolynomial.isWeightedHomogeneous_zero A w _

theorem polynomialCoefficientsHomogeneous_sub (w : σ → ℤ)
    (p q : Polynomial (MvPolynomial σ A)) (d : ℤ)
    (hp : polynomialCoefficientsHomogeneous w p d)
    (hq : polynomialCoefficientsHomogeneous w q d) :
    polynomialCoefficientsHomogeneous w (p - q) d := by
  intro l
  rw [Polynomial.coeff_sub]
  exact (MvPolynomial.weightedHomogeneousSubmodule A w (d - l)).sub_mem (hp l) (hq l)

theorem polynomialCoefficientsHomogeneous_mul (w : σ → ℤ)
    (p q : Polynomial (MvPolynomial σ A)) (d e : ℤ)
    (hp : polynomialCoefficientsHomogeneous w p d)
    (hq : polynomialCoefficientsHomogeneous w q e) :
    polynomialCoefficientsHomogeneous w (p * q) (d + e) := by
  intro l
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro ab hab
  have hab' := Finset.mem_antidiagonal.mp hab
  convert (hp ab.1).mul (hq ab.2) using 1
  have hc : (ab.1 : ℤ) + ab.2 = l := by exact_mod_cast hab'
  omega

/-- The characteristic polynomial is homogeneous when every root has degree one. -/
theorem alphabetCharacteristic_homogeneous (w : σ → ℤ) (xs : List (MvPolynomial σ A))
    (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1) :
    polynomialCoefficientsHomogeneous w (alphabetCharacteristic xs) xs.length := by
  induction xs with
  | nil =>
      simpa only [alphabetCharacteristic_product, List.map_nil, List.prod_nil,
        List.length_nil, Nat.cast_zero, pow_zero] using
        polynomialCoefficientsHomogeneous_power (A := A) w 0
  | cons x xs ih =>
      rw [show x :: xs = [x] ++ xs from rfl, alphabetCharacteristic_append,
        alphabetCharacteristic_singleton]
      have hx := polynomialCoefficientsHomogeneous_sub w Polynomial.X (Polynomial.C x) 1
        (by simpa only [pow_one, Nat.cast_one] using
          polynomialCoefficientsHomogeneous_power (A := A) w 1)
        (polynomialCoefficientsHomogeneous_constant w x 1 (hxs x (by simp)))
      convert polynomialCoefficientsHomogeneous_mul w _ _ 1 xs.length hx
        (ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))) using 1
      simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]

/-- Every remainder coefficient has the power degree minus its row number. -/
theorem alphabetPowerRemainder_homogeneous (w : σ → ℤ) (xs : List (MvPolynomial σ A))
    (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1) (m l : ℕ) :
    (alphabetPowerRemainder xs m l).IsWeightedHomogeneous w ((m : ℤ) - l) := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (alphabetPowerRemainder xs m l) 0]
    exact MvPolynomial.isWeightedHomogeneous_zero A w _
  by_cases hx : xs = []
  · subst xs
    simp only [alphabetPowerRemainder, alphabetCharacteristic_product, List.map_nil,
      List.prod_nil, Polynomial.modByMonic_one, Polynomial.coeff_zero]
    exact MvPolynomial.isWeightedHomogeneous_zero A w _
  have hr : 0 < xs.length := List.length_pos_iff.mpr hx
  let P := alphabetCharacteristic xs
  have hP : P.Monic := alphabetCharacteristic_monic xs
  have hd : P.natDegree = xs.length := alphabetCharacteristic_natDegree xs
  suffices h : polynomialCoefficientsHomogeneous w (Polynomial.X ^ m %ₘ P) m from h l
  induction m with
  | zero =>
      have he : (Polynomial.X ^ 0 : Polynomial (MvPolynomial σ A)) %ₘ P = 1 := by
        rw [pow_zero, (Polynomial.modByMonic_eq_self_iff hP).mpr]
        rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hP.ne_zero, hd]
        exact_mod_cast hr
      rw [he]
      simpa only [pow_zero] using polynomialCoefficientsHomogeneous_power (A := A) w 0
  | succ m ih =>
      have he : Polynomial.X ^ (m + 1) %ₘ P =
          Polynomial.X * (Polynomial.X ^ m %ₘ P) -
            Polynomial.C ((Polynomial.X ^ m %ₘ P).coeff (xs.length - 1)) * P := by
        rw [pow_succ']
        have hm : Polynomial.X * Polynomial.X ^ m %ₘ P =
            Polynomial.X * (Polynomial.X ^ m %ₘ P) %ₘ P := by
          apply Polynomial.modByMonic_eq_of_dvd_sub hP
          rw [← mul_sub, Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
          exact dvd_mul_of_dvd_right (dvd_mul_right P _) Polynomial.X
        rw [hm]
        apply monic_remainder_variable_mul P _ xs.length hP hd hr
        simpa only [Polynomial.degree_eq_natDegree hP.ne_zero, hd] using
          Polynomial.degree_modByMonic_lt (Polynomial.X ^ m) hP
      rw [he]
      apply polynomialCoefficientsHomogeneous_sub
      · convert polynomialCoefficientsHomogeneous_mul w Polynomial.X _ 1 m
          (by simpa only [pow_one, Nat.cast_one] using
            polynomialCoefficientsHomogeneous_power (A := A) w 1) ih using 1 <;> push_cast <;> ring
      · convert polynomialCoefficientsHomogeneous_mul w _ P
          ((m : ℤ) - (xs.length - 1 : ℕ)) xs.length
          (polynomialCoefficientsHomogeneous_constant w _ _ (ih (xs.length - 1)))
          (alphabetCharacteristic_homogeneous w xs hxs) using 1
        rw [Nat.cast_sub (by omega : 1 ≤ xs.length), Nat.cast_one, Nat.cast_add, Nat.cast_one]
        ring

/-- Weighted row and column degrees determine the degree of a determinant. -/
theorem determinant_homogeneous_row_column {j : ℕ} (w : σ → ℤ)
    (M : Matrix (Fin j) (Fin j) (MvPolynomial σ A)) (row col : Fin j → ℤ)
    (hM : ∀ a b, (M a b).IsWeightedHomogeneous w (col b - row a)) :
    M.det.IsWeightedHomogeneous w ((∑ b, col b) - ∑ a, row a) := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro e he
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun b => M (e b) b) (fun b => col b - row (e b)) (fun b _ => hM (e b) b)
  rw [Finset.sum_sub_distrib, Equiv.sum_comp e row] at hp
  simpa only [Units.smul_def] using
    ((MvPolynomial.weightedHomogeneousSubmodule A w _).restrictScalars ℤ).smul_mem
      (e.sign : ℤ) hp

/-- The total degree of a remainder minor is the sum of column degrees minus row indices. -/
def remainderMinorDegree (N j : ℕ) (rows cols : Fin j → ℕ) : ℤ :=
  (∑ b, ((N + cols b : ℕ) : ℤ)) - ∑ a, (rows a : ℤ)

theorem remainderRowMinor_homogeneous (w : σ → ℤ) (xs : List (MvPolynomial σ A))
    (hxs : ∀ x ∈ xs, x.IsWeightedHomogeneous w 1) (N j : ℕ)
    (rows cols : Fin j → ℕ) :
    (remainderRowMinor xs N j rows cols).IsWeightedHomogeneous w
      (remainderMinorDegree N j rows cols) :=
  determinant_homogeneous_row_column w
    (fun a b => alphabetPowerRemainder xs (N + cols b) (rows a))
    (fun a => (rows a : ℤ)) (fun b => ((N + cols b : ℕ) : ℤ))
    (fun a b => alphabetPowerRemainder_homogeneous w xs hxs _ _)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.polynomialCoefficientsHomogeneous_constant
#print axioms VOA.DeligneAudit.SL4T.polynomialCoefficientsHomogeneous_power
#print axioms VOA.DeligneAudit.SL4T.polynomialCoefficientsHomogeneous_sub
#print axioms VOA.DeligneAudit.SL4T.polynomialCoefficientsHomogeneous_mul
#print axioms VOA.DeligneAudit.SL4T.alphabetCharacteristic_homogeneous
#print axioms VOA.DeligneAudit.SL4T.alphabetPowerRemainder_homogeneous
#print axioms VOA.DeligneAudit.SL4T.determinant_homogeneous_row_column
#print axioms VOA.DeligneAudit.SL4T.remainderRowMinor_homogeneous
