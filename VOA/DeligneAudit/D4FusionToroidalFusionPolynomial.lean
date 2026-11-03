import VOA.DeligneAudit.D4FusionToroidalFusionAction
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Polynomial relations for toroidal evaluation operators

Any polynomial vanishing on the evaluation points gives an operator relation
on the entire tensor product, independently of its generator.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl

noncomputable section

variable {n N : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Fin N → CurrentModule f V) (z : Fin N → ℂ)

/-- Substitute the `t` operators into a scalar polynomial. -/
def polyOp (p : Polynomial ℂ) (c : Fin n) (i : ℕ) :
    Module.End ℂ (Tensor (K := ℂ) (ι := Fin N) (W := V)) :=
  p.sum fun k a => a • evalOp ρ z c i k

theorem polyOp_eq_sites (p : Polynomial ℂ) (c : Fin n) (i : ℕ) :
    polyOp ρ z p c i =
      ∑ q : Fin N, p.eval (z q) • localOp q ((ρ q).op c i) := by
  simp only [polyOp, Polynomial.sum, evalOp, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Polynomial.eval_eq_sum]
  simp only [Polynomial.sum]
  rw [Finset.sum_smul]

theorem polyOp_zero_of_roots (p : Polynomial ℂ) (c : Fin n) (i : ℕ)
    (hp : ∀ q : Fin N, p.eval (z q) = 0) : polyOp ρ z p c i = 0 := by
  rw [polyOp_eq_sites]
  simp [hp]

/-- The monic polynomial whose roots are all evaluation points. -/
def pointPolynomial : Polynomial ℂ :=
  ∏ q : Fin N, (Polynomial.X - Polynomial.C (z q))

theorem pointPolynomial_root (q : Fin N) :
    (pointPolynomial z).eval (z q) = 0 := by
  simp only [pointPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ q)
  simp

/-- The point polynomial annihilates every evaluated current operator. -/
theorem pointPolynomial_op_zero (c : Fin n) (i : ℕ) :
    polyOp ρ z (pointPolynomial z) c i = 0 :=
  polyOp_zero_of_roots ρ z (pointPolynomial z) c i (pointPolynomial_root z)

theorem pointPolynomial_monic : (pointPolynomial z).Monic :=
  Polynomial.monic_prod_of_monic _ _
    (fun q _ => Polynomial.monic_X_sub_C (z q))

theorem pointPolynomial_degree : (pointPolynomial z).natDegree = N := by
  rw [pointPolynomial, Polynomial.natDegree_prod_of_monic _ _
    (fun q _ => Polynomial.monic_X_sub_C (z q))]
  simp

/-- Shift the annihilating polynomial to any degree at least the site count. -/
def shiftedPointPolynomial (s : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ (s - N) * pointPolynomial z

theorem shiftedPointPolynomial_monic (s : ℕ) :
    (shiftedPointPolynomial z s).Monic :=
  (Polynomial.monic_X_pow _).mul (pointPolynomial_monic z)

theorem shiftedPointPolynomial_degree (s : ℕ) (hs : N ≤ s) :
    (shiftedPointPolynomial z s).natDegree = s := by
  rw [shiftedPointPolynomial,
    Polynomial.natDegree_mul (Polynomial.monic_X_pow _).ne_zero
      (pointPolynomial_monic z).ne_zero,
    Polynomial.natDegree_X_pow, pointPolynomial_degree]
  omega

theorem shiftedPointPolynomial_root (s : ℕ) (q : Fin N) :
    (shiftedPointPolynomial z s).eval (z q) = 0 := by
  simp [shiftedPointPolynomial, pointPolynomial_root]

/-- Every high `t` mode is a linear combination of strictly lower modes
as an identity of endomorphisms on the full tensor product. -/
theorem evalOp_high_rewrite (c : Fin n) (i s : ℕ) (hs : N ≤ s) :
    evalOp ρ z c i s =
      -(∑ k ∈ Finset.range s,
        (shiftedPointPolynomial z s).coeff k • evalOp ρ z c i k) := by
  let p := shiftedPointPolynomial z s
  have hm : p.Monic := shiftedPointPolynomial_monic z s
  have hd : p.natDegree = s := shiftedPointPolynomial_degree z s hs
  have hzero : polyOp ρ z p c i = 0 :=
    polyOp_zero_of_roots ρ z p c i (shiftedPointPolynomial_root z s)
  rw [polyOp, p.sum_over_range (by intro k; simp), hd,
    Finset.sum_range_succ] at hzero
  have htop : p.coeff s = 1 := by simpa only [hd] using hm.coeff_natDegree
  rw [htop] at hzero
  simpa only [one_smul] using eq_neg_of_add_eq_zero_right hzero

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.polyOp_eq_sites
#print axioms VOA.DeligneAudit.Toroidal.pointPolynomial_root
#print axioms VOA.DeligneAudit.Toroidal.pointPolynomial_op_zero
#print axioms VOA.DeligneAudit.Toroidal.evalOp_high_rewrite
