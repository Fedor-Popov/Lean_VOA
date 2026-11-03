/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.TripletWpStronglyFinite
import VOA.Modules.ZhuPolynomialSimplicity

/-!
# The Adamovic--Milas simplicity reduction for lattice W(2)

The generic Zhu-polynomial criterion constructs an ordinary module on every VOA ideal and applies
Zhu's algebra to its least occupied integral weight.  This file specializes that criterion to

f_2(X) = X^2 (X + 1/8) (X - 3/8) (X - 1).

The exact remaining model-specific certificate is one finite carrier statement: the state obtained
by evaluating the expanded f_2 with Zhu products belongs to O(W(2)).  This target is suitable
for a sparse certificate made from finitely many circle-product generators.  It is not assumed or
proved globally here; the public simplicity theorem keeps it as its sole hypothesis.

No equality with the lattice screening kernel and no relation to SympFerm.tripletW2 is used.
-/

namespace VOA

open VertexOperatorAlgebra

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ## The explicit f_2 Zhu representative -/

/-- Iterated left Zhu product by the conformal vector, before passing to A(W). -/
noncomputable def zhuOmegaPow (W : VertexOperatorAlgebra V) : ℕ → V
  | 0 => W.vacuum
  | n + 1 => zhuMul W W.conformalVector (zhuOmegaPow W n)

/-- The state-level representative of the expanded polynomial
X^5 - 5/4 X^4 + 13/64 X^3 + 3/64 X^2. -/
noncomputable def fTwoZhuRepresentative (W : VertexOperatorAlgebra V) : V :=
  zhuOmegaPow W 5
    - (5 / 4 : ℂ) • zhuOmegaPow W 4
    + (13 / 64 : ℂ) • zhuOmegaPow W 3
    + (3 / 64 : ℂ) • zhuOmegaPow W 2

/-- The polynomial in the p = 2 Adamovic--Milas simplicity argument, in the expanded form matched
by the literal Zhu-product representative. -/
noncomputable def fTwoPolynomial : Polynomial ℂ :=
  Polynomial.X ^ 5
    - Polynomial.C (5 / 4) * Polynomial.X ^ 4
    + Polynomial.C (13 / 64) * Polynomial.X ^ 3
    + Polynomial.C (3 / 64) * Polynomial.X ^ 2

/-- The scalar evaluation of fTwoPolynomial. -/
noncomputable def fTwoScalar (h : ℂ) : ℂ :=
  h ^ 2 * (h + 1 / 8) * (h - 3 / 8) * (h - 1)

theorem fTwoPolynomial_eval (h : ℂ) :
    fTwoPolynomial.eval h = fTwoScalar h := by
  simp only [fTwoPolynomial, fTwoScalar, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C]
  ring

/-- Iterated Zhu multiplication represents the corresponding power of [omega]. -/
theorem mk_zhuOmegaPow (W : VertexOperatorAlgebra V) (n : ℕ) :
    letI := instRingA W
    letI := instAlgebraA W
    mk W (zhuOmegaPow W n) = (mk W W.conformalVector) ^ n := by
  letI := instRingA W
  letI := instAlgebraA W
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [zhuOmegaPow, ← Amul_mk (zhuRingData_holds W), ← AsRing_mul_eq, ih, pow_succ']

/-- The literal state represents the polynomial evaluated at the conformal class. -/
theorem mk_fTwoZhuRepresentative (W : VertexOperatorAlgebra V) :
    letI := instRingA W
    letI := instAlgebraA W
    mk W (fTwoZhuRepresentative W) =
      Polynomial.aeval (mk W W.conformalVector) fTwoPolynomial := by
  letI := instRingA W
  letI := instAlgebraA W
  rw [fTwoZhuRepresentative, map_add, map_add, map_sub, map_smul, map_smul, map_smul,
    mk_zhuOmegaPow, mk_zhuOmegaPow, mk_zhuOmegaPow, mk_zhuOmegaPow]
  simp only [fTwoPolynomial, map_mul, map_pow, Polynomial.aeval_X, map_add, map_sub,
    Polynomial.aeval_C, Algebra.smul_def]

/-- The exact finite certificate needed from a lattice/free-field calculation. -/
def FTwoZhuCertificate (W : VertexOperatorAlgebra V) : Prop :=
  fTwoZhuRepresentative W ∈ O W

/-- The finite carrier membership is precisely the polynomial relation consumed by the generic
simplicity criterion. -/
theorem zhuPolynomialRelation_of_fTwoZhuCertificate (W : VertexOperatorAlgebra V)
    (hcert : FTwoZhuCertificate W) :
    ZhuPolynomialSimplicity.ZhuPolynomialRelation W fTwoPolynomial := by
  letI := instRingA W
  letI := instAlgebraA W
  rw [ZhuPolynomialSimplicity.ZhuPolynomialRelation]
  rw [← mk_fTwoZhuRepresentative W]
  exact (mk_eq_zero_iff W).2 hcert

/-! ## The integral root calculation -/

/-- Among nonnegative integral conformal weights, the roots of f_2 are exactly 0 and 1.
The other roots, -1/8 and 3/8, are nonintegral. -/
theorem fTwoScalar_natCast_eq_zero_iff (n : ℕ) :
    fTwoScalar (n : ℂ) = 0 ↔ n = 0 ∨ n = 1 := by
  constructor
  · intro h
    unfold fTwoScalar at h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left
          have hn : (n : ℂ) = 0 :=
            (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
          exact_mod_cast hn
        · have hr := congrArg Complex.re h
          norm_num at hr
          have : (0 : ℝ) < (n : ℝ) + 1 / 8 := by positivity
          linarith
      · have hr := congrArg Complex.re h
        norm_num at hr
        have hnlt : n < 1 := by exact_mod_cast (show (n : ℝ) < 1 by linarith)
        omega
    · right
      have hr := congrArg Complex.re h
      norm_num at hr
      have hnreal : (n : ℝ) = 1 := by linarith
      exact_mod_cast hnreal
  · rintro (rfl | rfl) <;> norm_num [fTwoScalar]

theorem fTwoPolynomial_natCast_root (n : ℕ)
    (h : fTwoPolynomial.eval (n : ℂ) = 0) : n = 0 ∨ n = 1 :=
  (fTwoScalar_natCast_eq_zero_iff n).mp (fTwoPolynomial_eval (n : ℂ) ▸ h)

namespace LatGen.Wp

open LatGen
open LatGen.Triplet

/-- The exact unproved finite Zhu target on the generated lattice carrier. -/
def FTwoZhuCertificateWp (hp : 1 ≤ 2) : Prop :=
  FTwoZhuCertificate (tripletWVOA 2 hp)

/-- The lattice W(2) carrier is simple from exactly the finite f_2 Zhu certificate. -/
theorem tripletWVOA_two_isSimple_of_fTwoZhuCertificate (hp : 1 ≤ 2)
    (hcert : FTwoZhuCertificateWp hp) : (tripletWVOA 2 hp).IsSimple := by
  apply ZhuPolynomialSimplicity.isSimple_of_zhuPolynomial
    (tripletWVOA 2 hp) (P := fTwoPolynomial)
  · obtain ⟨x, hx⟩ := exists_ne_zero_tripletW 2 hp
    intro htop
    apply hx
    exact (Submodule.mem_bot ℂ).mp (show x ∈ (⊥ : Submodule ℂ (tripletW 2 hp).carrier) by
      rw [← htop]
      exact Submodule.mem_top)
  · exact tripletWVOA_two_grading_one_eq_bot hp
  · exact zhuPolynomialRelation_of_fTwoZhuCertificate _ hcert
  · exact fTwoPolynomial_natCast_root

/-- With the same sole certificate, the existing package is strongly finite and irrational on the
lattice carrier. -/
theorem tripletWVOA_two_stronglyFinite_and_irrational_of_fTwoZhuCertificate
    (hp : 1 ≤ 2) (hcert : FTwoZhuCertificateWp hp) :
    StronglyFinite (tripletWVOA 2 hp) ∧
      ¬ AdmissiblyRational (tripletWVOA 2 hp) ∧
      ¬ GannonRational (tripletWVOA 2 hp) :=
  tripletWVOA_two_stronglyFinite_and_irrational_of_isSimple hp
    (tripletWVOA_two_isSimple_of_fTwoZhuCertificate hp hcert)

end LatGen.Wp

end VOA

section AxiomAudit
#print axioms VOA.mk_fTwoZhuRepresentative
#print axioms VOA.zhuPolynomialRelation_of_fTwoZhuCertificate
#print axioms VOA.fTwoScalar_natCast_eq_zero_iff
#print axioms VOA.LatGen.Wp.tripletWVOA_two_isSimple_of_fTwoZhuCertificate
end AxiomAudit
