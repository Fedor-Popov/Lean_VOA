import Mathlib.Algebra.Polynomial.Reverse

/-!
# Fixed-degree reflection of two-color polynomial currents

Reflecting with a prescribed degree bound keeps the padded zeros needed for
current coefficients. Powers and products use the sum of their prescribed
bounds, so coefficient reversal does not require an exact degree or a domain.
-/

namespace VOA.DeligneAudit.A2.CVRectReflection

noncomputable section

variable {A : Type*} [Semiring A]

/-- Reflect a power using its prescribed upper degree, including padded zeros. -/
theorem reflect_pow_bound (f : Polynomial A) (d : ℕ) (hf : f.natDegree ≤ d)
    (p : ℕ) :
    Polynomial.reflect (d * p) (f ^ p) = Polynomial.reflect d f ^ p := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [pow_succ, Nat.mul_succ,
        Polynomial.reflect_mul (f ^ p) f
          ((Polynomial.natDegree_pow_le_of_le p hf).trans_eq (Nat.mul_comm p d)) hf,
        ih, pow_succ]

/-- Two currents may have different prescribed degree bounds. -/
theorem reflect_pow_mul_pow (f g : Polynomial A) (df dg p q : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg) :
    Polynomial.reflect (df * p + dg * q) (f ^ p * g ^ q) =
      Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q := by
  rw [Polynomial.reflect_mul (f ^ p) (g ^ q)
    ((Polynomial.natDegree_pow_le_of_le p hf).trans_eq (Nat.mul_comm p df))
    ((Polynomial.natDegree_pow_le_of_le q hg).trans_eq (Nat.mul_comm q dg)),
    reflect_pow_bound f df hf, reflect_pow_bound g dg hg]

/-- The common-bound specialization used for equally truncated current colors. -/
theorem reflect_two_color (f g : Polynomial A) (d p q : ℕ)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) :
    Polynomial.reflect (d * (p + q)) (f ^ p * g ^ q) =
      Polynomial.reflect d f ^ p * Polynomial.reflect d g ^ q := by
  simpa only [Nat.mul_add] using reflect_pow_mul_pow f g d d p q hf hg

/-- Inside the prescribed bound, reversed and forward coefficients have complementary indices. -/
theorem coeff_reflect_pow_mul_pow (f g : Polynomial A) (df dg p q j : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg)
    (hj : j ≤ df * p + dg * q) :
    (Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q).coeff j =
      (f ^ p * g ^ q).coeff (df * p + dg * q - j) := by
  rw [← reflect_pow_mul_pow f g df dg p q hf hg, Polynomial.coeff_reflect,
    Polynomial.revAt_le hj]

/-- The reflected product has no coefficient beyond the prescribed total bound. -/
theorem coeff_reflect_pow_mul_pow_high (f g : Polynomial A) (df dg p q j : ℕ)
    (hf : f.natDegree ≤ df) (hg : g.natDegree ≤ dg)
    (hj : df * p + dg * q < j) :
    (Polynomial.reflect df f ^ p * Polynomial.reflect dg g ^ q).coeff j = 0 := by
  rw [← reflect_pow_mul_pow f g df dg p q hf hg, Polynomial.coeff_reflect,
    Polynomial.revAt_eq_self_of_lt hj]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  apply lt_of_le_of_lt _ hj
  exact Polynomial.natDegree_mul_le.trans
    (add_le_add
      ((Polynomial.natDegree_pow_le_of_le p hf).trans_eq (Nat.mul_comm p df))
      ((Polynomial.natDegree_pow_le_of_le q hg).trans_eq (Nat.mul_comm q dg)))

/-- Coefficient reversal for a common current-degree cutoff. -/
theorem coeff_two_color (f g : Polynomial A) (d p q j : ℕ)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hj : j ≤ d * (p + q)) :
    (Polynomial.reflect d f ^ p * Polynomial.reflect d g ^ q).coeff j =
      (f ^ p * g ^ q).coeff (d * (p + q) - j) := by
  simpa only [Nat.mul_add] using
    coeff_reflect_pow_mul_pow f g d d p q j hf hg (by simpa only [Nat.mul_add] using hj)

/-- High current coefficients vanish after reflection, also for a common cutoff. -/
theorem coeff_two_color_high (f g : Polynomial A) (d p q j : ℕ)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hj : d * (p + q) < j) :
    (Polynomial.reflect d f ^ p * Polynomial.reflect d g ^ q).coeff j = 0 := by
  exact coeff_reflect_pow_mul_pow_high f g d d p q j hf hg
    (by simpa only [Nat.mul_add] using hj)

end
end VOA.DeligneAudit.A2.CVRectReflection

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.CVRectReflection.reflect_pow_mul_pow
#print axioms VOA.DeligneAudit.A2.CVRectReflection.reflect_two_color
#print axioms VOA.DeligneAudit.A2.CVRectReflection.coeff_reflect_pow_mul_pow
#print axioms VOA.DeligneAudit.A2.CVRectReflection.coeff_reflect_pow_mul_pow_high
#print axioms VOA.DeligneAudit.A2.CVRectReflection.coeff_two_color
#print axioms VOA.DeligneAudit.A2.CVRectReflection.coeff_two_color_high
end AxiomAudit
