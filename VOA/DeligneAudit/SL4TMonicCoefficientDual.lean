import VOA.DeligneAudit.SL4TPolynomialMinorSpan

/-! # Coefficient functionals in a monic polynomial quotient -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

variable {A : Type*} [CommRing A]

/-- Reduction after multiplication by the variable is the companion-matrix operation. -/
theorem monic_remainder_variable_mul (P p : Polynomial A) (r : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hrpos : 0 < r)
    (hp : p.degree < (r : WithBot ℕ)) :
    X * p %ₘ P = X * p - Polynomial.C (p.coeff (r - 1)) * P := by
  nontriviality A
  have hd : (X * p - Polynomial.C (p.coeff (r - 1)) * P).degree < P.degree := by
    rw [degree_eq_natDegree hP.ne_zero, hr, degree_lt_iff_coeff_zero]
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    rw [coeff_sub, coeff_X_mul, coeff_C_mul]
    by_cases he : m + 1 = r
    · have hc : P.coeff m.succ = 1 := by
        rw [show m.succ = r by omega, ← hr, coeff_natDegree, hP.leadingCoeff]
      rw [hc, mul_one, show m = r - 1 by omega, sub_self]
    · have hpz : p.coeff m = 0 := coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hp (by exact_mod_cast (show r ≤ m by omega)))
      have hPz : P.coeff m.succ = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hpz, hPz, mul_zero, sub_self]
  exact (div_modByMonic_unique (Polynomial.C (p.coeff (r - 1))) _ hP
    ⟨by ring, hd⟩).2

/-- The companion recurrence holds for every polynomial representative. -/
theorem monic_remainder_coefficient_shift (P p : Polynomial A) (r i : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hrpos : 0 < r) :
    (X * p %ₘ P).coeff (i + 1) =
      (p %ₘ P).coeff i - P.coeff (i + 1) * (p %ₘ P).coeff (r - 1) := by
  nontriviality A
  have hm : X * p %ₘ P = X * (p %ₘ P) %ₘ P := by
    apply modByMonic_eq_of_dvd_sub hP
    rw [← mul_sub, modByMonic_eq_sub_mul_div, sub_sub_cancel]
    exact dvd_mul_of_dvd_right (dvd_mul_right P _) X
  rw [hm, monic_remainder_variable_mul P (p %ₘ P) r hP hr hrpos]
  · simp only [coeff_sub, coeff_X_mul, coeff_C_mul, coeff_mul_C, mul_comm]
  · simpa only [degree_eq_natDegree hP.ne_zero, hr] using degree_modByMonic_lt p hP

/-- Monic polynomials representing the coefficient functionals from highest to lowest. -/
def monicCoefficientDual (P : Polynomial A) (r : ℕ) : ℕ → Polynomial A
  | 0 => 1
  | n + 1 => X * monicCoefficientDual P r n + Polynomial.C (P.coeff (r - 1 - n))

/-- Pairing with the highest coefficient after reduction modulo a monic polynomial. -/
def monicRemainderPairing (P : Polynomial A) (r : ℕ) (p : Polynomial A) :
    Polynomial A →ₗ[A] A :=
  (lcoeff A (r - 1)).comp ((modByMonicHom P).comp (LinearMap.mulRight A p))

theorem monicRemainderPairing_apply (P : Polynomial A) (r : ℕ) (p q : Polynomial A) :
    monicRemainderPairing P r p q = (q * p %ₘ P).coeff (r - 1) := rfl

/-- The dual polynomial of index `n` is monic of degree `n`. -/
theorem monicCoefficientDual_monic_degree [Nontrivial A] (P : Polynomial A) (r n : ℕ) :
    (monicCoefficientDual P r n).Monic ∧ (monicCoefficientDual P r n).natDegree = n := by
  induction n with
  | zero => simp only [monicCoefficientDual, monic_one, natDegree_one, and_self]
  | succ n ih =>
      have hd : (X * monicCoefficientDual P r n).natDegree = n + 1 := by
        rw [natDegree_X_mul ih.1.ne_zero, ih.2]
      have hc : (Polynomial.C (P.coeff (r - 1 - n))).degree <
          (X * monicCoefficientDual P r n).degree := by
        rw [degree_eq_natDegree (monic_X.mul ih.1).ne_zero, hd]
        exact lt_of_le_of_lt degree_C_le (by exact_mod_cast (show 0 < n + 1 by omega))
      refine ⟨(monic_X.mul ih.1).add_of_left hc, ?_⟩
      exact (natDegree_add_eq_left_of_degree_lt hc).trans hd

/-- Every coordinate is the highest coordinate paired with its dual polynomial. -/
theorem monicCoefficientDual_pairing (P p : Polynomial A) (r n : ℕ)
    (hP : P.Monic) (hr : P.natDegree = r) (hn : n < r) :
    monicRemainderPairing P r p (monicCoefficientDual P r n) =
      (p %ₘ P).coeff (r - 1 - n) := by
  induction n generalizing p with
  | zero => simp [monicCoefficientDual, monicRemainderPairing_apply]
  | succ n ih =>
      rw [monicCoefficientDual, map_add]
      have hx : monicRemainderPairing P r p (X * monicCoefficientDual P r n) =
          monicRemainderPairing P r (X * p) (monicCoefficientDual P r n) := by
        simp only [monicRemainderPairing_apply, mul_left_comm, mul_assoc]
      rw [hx, ih (X * p) (by omega)]
      have hc : monicRemainderPairing P r p (Polynomial.C (P.coeff (r - 1 - n))) =
          P.coeff (r - 1 - n) * (p %ₘ P).coeff (r - 1) := by
        change (Polynomial.C _ * p %ₘ P).coeff _ = _
        rw [← smul_eq_C_mul, smul_modByMonic]
        simp only [RingHom.id_apply, coeff_smul, smul_eq_mul]
      rw [hc, show r - 1 - n = (r - 1 - (n + 1)) + 1 by omega,
        monic_remainder_coefficient_shift P p r _ hP hr (by omega), sub_add_cancel]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.monic_remainder_variable_mul
#print axioms VOA.DeligneAudit.SL4T.monic_remainder_coefficient_shift
#print axioms VOA.DeligneAudit.SL4T.monicRemainderPairing_apply
#print axioms VOA.DeligneAudit.SL4T.monicCoefficientDual_monic_degree
#print axioms VOA.DeligneAudit.SL4T.monicCoefficientDual_pairing
