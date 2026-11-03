import VOA.DeligneAudit.DeligneFusionCVRectReflection

/-!
# Prescribed-degree reflection for three ordered currents

The coefficient identities hold over an arbitrary coefficient semiring,
including noncommutative endomorphisms. Fixed upper degree bounds preserve
zero padding and require no exact degree or nonzero leading coefficient.
-/

namespace VOA.DeligneAudit.A2.CVRectFiltered

open VOA.DeligneAudit.A2.CVRectReflection

noncomputable section

variable {A : Type*} [Semiring A]

theorem reflect_three (f g h : Polynomial A) (df dg dh p q r : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg) (hh : h.natDegree ≤ dh) :
    Polynomial.reflect (df * p + dg * q + dh * r) (f ^ p * g ^ q * h ^ r) =
      Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q *
        Polynomial.reflect dh h ^ r := by
  have hfg : (f ^ p * g ^ q).natDegree ≤ df * p + dg * q :=
    Polynomial.natDegree_mul_le.trans (add_le_add
      ((Polynomial.natDegree_pow_le_of_le p hf).trans_eq (Nat.mul_comm p df))
      ((Polynomial.natDegree_pow_le_of_le q hg).trans_eq (Nat.mul_comm q dg)))
  rw [Polynomial.reflect_mul _ _ hfg
      ((Polynomial.natDegree_pow_le_of_le r hh).trans_eq (Nat.mul_comm r dh)),
    reflect_pow_mul_pow f g df dg p q hf hg, reflect_pow_bound h dh hh]

theorem coeff_reflect_three (f g h : Polynomial A) (df dg dh p q r j : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg) (hh : h.natDegree ≤ dh)
    (hj : j ≤ df * p + dg * q + dh * r) :
    (Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q *
      Polynomial.reflect dh h ^ r).coeff j =
        (f ^ p * g ^ q * h ^ r).coeff (df * p + dg * q + dh * r - j) := by
  rw [← reflect_three f g h df dg dh p q r hf hg hh, Polynomial.coeff_reflect,
    Polynomial.revAt_le hj]

theorem coeff_reflect_three_high (f g h : Polynomial A) (df dg dh p q r j : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg) (hh : h.natDegree ≤ dh)
    (hj : df * p + dg * q + dh * r < j) :
    (Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q *
      Polynomial.reflect dh h ^ r).coeff j = 0 := by
  rw [← reflect_three f g h df dg dh p q r hf hg hh, Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt hj]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  apply lt_of_le_of_lt _ hj
  exact Polynomial.natDegree_mul_le.trans (add_le_add
    (Polynomial.natDegree_mul_le.trans (add_le_add
      ((Polynomial.natDegree_pow_le_of_le p hf).trans_eq (Nat.mul_comm p df))
      ((Polynomial.natDegree_pow_le_of_le q hg).trans_eq (Nat.mul_comm q dg))))
    ((Polynomial.natDegree_pow_le_of_le r hh).trans_eq (Nat.mul_comm r dh)))

end

end VOA.DeligneAudit.A2.CVRectFiltered

#print axioms VOA.DeligneAudit.A2.CVRectFiltered.coeff_reflect_three
#print axioms VOA.DeligneAudit.A2.CVRectFiltered.coeff_reflect_three_high
