/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorLoop

/-!
# The loop operators form a representation of the current algebra

For structure constants `f` satisfying the Jacobi identity in coordinates (`JacobiCoord`), the
coadjoint loop operators satisfy the current-algebra commutation relations

  `[x ⊗ t^r, y ⊗ t^s] = Σ_e f(x,y,e) (e ⊗ t^{r+s})`.
-/

namespace VOA.DeligneAudit.SectorLoop

open VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier MvPolynomial

noncomputable section

variable {K σ : Type*} [Field K] [Fintype σ] [DecidableEq σ] (f : σ → σ → σ → K)

/-- The Jacobi identity in coordinates, in the form used by the coadjoint action:
`[b,[a,x]] - [a,[b,x]] = -[[a,b],x]`. -/
def JacobiCoord : Prop :=
  ∀ a b x c, (∑ d, f a x d * f b d c) - (∑ d, f b x d * f a d c) = -∑ e, f a b e * f e x c

omit [Fintype σ] [DecidableEq σ] in
theorem sum_split_diag {m : ℕ} {R : Type*} [AddCommMonoid R] (F : Fin m → R) (i : Fin m) :
    ∑ j, F j = F i + ∑ j, if j = i then 0 else F j := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
  congr 1
  ext j; simp [Finset.mem_erase, and_comm]

omit [DecidableEq σ] in
/-- Double application of loop operators, pointwise. -/
theorem loopOp_loopOp_apply (m : ℕ) (a b : σ) (r s : ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m 0) (t : Fin m → σ) :
    loopOp f m a r (loopOp f m b s p) t =
      (∑ i, zr i ^ (r + s) * ∑ c, ∑ d, C (f a (t i) c) * C (f b c d) *
          p (Function.update t i d)) +
      ∑ i, ∑ j, if j = i then 0 else
        zr i ^ r * zr j ^ s * ∑ c, ∑ d, C (f a (t i) c) * C (f b (t j) d) *
          p (Function.update (Function.update t i c) j d) := by
  simp only [loopOp, LinearMap.coe_mk, AddHom.coe_mk, mul_neg, Finset.sum_neg_distrib,
    neg_neg, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  rw [sum_split_diag _ i]
  congr 1
  · simp only [Function.update_self, Function.update_idem, pow_add]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hji
    · rfl
    · simp only [Function.update_of_ne hji]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      ring

omit [DecidableEq σ] in
/-- **Current-algebra commutation relations of the loop operators.** -/
theorem loopOp_comm (hJ : JacobiCoord f) (m : ℕ) (a b : σ) (r s : ℕ)
    (p : TensorPolynomial (K := K) (σ := σ) m 0) :
    loopOp f m a r (loopOp f m b s p) - loopOp f m b s (loopOp f m a r p) =
      ∑ e, f a b e • loopOp f m e (r + s) p := by
  funext t
  rw [Pi.sub_apply, loopOp_loopOp_apply, loopOp_loopOp_apply]
  have hcross :
      (∑ i, ∑ j, if j = i then (0 : MvPolynomial (Particle m 0) K) else
        zr i ^ r * zr j ^ s * ∑ c, ∑ d, C (f a (t i) c) * C (f b (t j) d) *
          p (Function.update (Function.update t i c) j d)) =
      ∑ i, ∑ j, if j = i then 0 else
        zr i ^ s * zr j ^ r * ∑ c, ∑ d, C (f b (t i) c) * C (f a (t j) d) *
          p (Function.update (Function.update t i c) j d) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    by_cases hji : j = i
    · subst hji; simp
    · rw [if_neg hji, if_neg (Ne.symm hji), Finset.sum_comm]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
      rw [Function.update_comm (Ne.symm hji)]
      ring
  rw [hcross, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  simp only [Finset.sum_apply, Pi.smul_apply, loopOp, LinearMap.coe_mk, AddHom.coe_mk,
    smul_neg, Finset.smul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm r s]
  have hJd : ∀ d, (C (-(∑ e, f a b e * f e (t i) d)) : MvPolynomial (Particle m 0) K) =
      (∑ c, C (f a (t i) c) * C (f b c d)) - ∑ c, C (f b (t i) c) * C (f a c d) := by
    intro d
    rw [← hJ a b (t i) d]
    simp only [map_sub, map_sum, map_mul]
  trans zr i ^ (s + r) * ∑ d, C (-(∑ e, f a b e * f e (t i) d)) * p (Function.update t i d)
  · simp only [hJd, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_sub]
    rw [Finset.sum_comm (f := fun x y => zr i ^ (s + r) *
        (C (f a (t i) y) * C (f b y x) * p (Function.update t i x)))]
    rw [Finset.sum_comm (f := fun x y => zr i ^ (s + r) *
        (C (f b (t i) y) * C (f a y x) * p (Function.update t i x)))]
  · simp only [map_neg, map_sum, map_mul, neg_mul, Finset.sum_mul, Finset.mul_sum,
      Finset.sum_neg_distrib, mul_neg, smul_eq_C_mul]
    refine congrArg Neg.neg ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => ?_
    ring

end

end VOA.DeligneAudit.SectorLoop

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorLoop.loopOp_comm
end AxiomAudit
