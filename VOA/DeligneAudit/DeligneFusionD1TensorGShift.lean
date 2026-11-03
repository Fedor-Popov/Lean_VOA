import VOA.DeligneAudit.DeligneFusionD1TensorGAction
import VOA.DeligneAudit.DeligneFusionD1SiteG
import VOA.DeligneAudit.DeligneFusionJetInterpolationOperators
import Mathlib.Tactic.Module

/-!
# Actual shifted two-jet tensor current module

At a site z, mode k is z^k A+k*z^(k-1) B. Differentiating the elementary
polynomial identity X^(r+s)=X^r X^s supplies the scalar Leibniz identity,
so the checked local zero/one-mode brackets prove every shifted bracket.
The finite tensor action is the already checked sum of local actions.
-/

namespace VOA.DeligneAudit.D1TensorG

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.SectorLoop

noncomputable section

private theorem monomial_jet_mul (z : ℂ) (r s : ℕ) :
    z ^ r * ((s : ℂ) * z ^ (s - 1)) + ((r : ℂ) * z ^ (r - 1)) * z ^ s =
      ((r + s : ℕ) : ℂ) * z ^ (r + s - 1) := by
  have h := congrArg (fun P : Polynomial ℂ => P.derivative.eval z)
    (pow_add (Polynomial.X : Polynomial ℂ) r s)
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h
  exact (add_comm _ _).trans h.symm

private theorem bracket_smul_add {U : Type*} [AddCommGroup U] [Module ℂ U]
    (A B C D : Module.End ℂ U) (a b c d : ℂ) :
    (a • A + b • B) * (c • C + d • D) - (c • C + d • D) * (a • A + b • B) =
      (a * c) • (A * C - C * A) + (a * d) • (A * D - D * A) +
        (b * c) • (B * C - C * B) + (b * d) • (B * D - D * B) := by
  simp only [add_mul, mul_add, smul_mul_smul_comm, smul_sub]
  module

variable {n N : ℕ} (f : Fin n → Fin n → Fin n → ℂ)
variable (hJ : JacobiCoord f) (hskew : ∀ a b c, f a b c = -f b a c)

/-- The Taylor action at one shifted two-jet site. -/
def shiftOp (z : ℂ) (c : Fin n) (k : ℕ) : Module.End ℂ (D1SiteG.Space n) :=
  z ^ k • D1SiteG.zeroOp f c + ((k : ℂ) * z ^ (k - 1)) • D1SiteG.oneOp c

include hJ hskew in
theorem shiftOp_comm (z : ℂ) (a b : Fin n) (r s : ℕ) :
    shiftOp f z a r * shiftOp f z b s - shiftOp f z b s * shiftOp f z a r =
      ∑ e, f a b e • shiftOp f z e (r + s) := by
  rw [shiftOp, shiftOp, bracket_smul_add, D1SiteG.zero_zero f hJ,
    D1SiteG.zero_one f, D1SiteG.one_zero f hskew, D1SiteG.one_one]
  simp only [smul_zero, add_zero, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = f a b e • ((z ^ r * z ^ s) • D1SiteG.zeroOp f e +
        (z ^ r * ((s : ℂ) * z ^ (s - 1)) + ((r : ℂ) * z ^ (r - 1)) * z ^ s) •
          D1SiteG.oneOp e) := by module
    _ = _ := by rw [← pow_add, monomial_jet_mul]; rfl

/-- The checked translated current representation at one site. -/
def shiftRep (z : ℂ) : CurrentModule f (D1SiteG.Space n) where
  op := shiftOp f z
  comm a b r s v := by
    have hh := congrArg (fun A => A v) (shiftOp_comm f hJ hskew z a b r s)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] using hh

@[simp] theorem shiftRep_op (z : ℂ) (c : Fin n) (k : ℕ) :
    (shiftRep f hJ hskew z).op c k = shiftOp f z c k := rfl

/-- The actual N-fold tensor product of the n+1-dimensional sites. -/
abbrev Space (n N : ℕ) := Tensor (K := ℂ) (ι := Fin N) (W := D1SiteG.Space n)

/-- The actual shifted tensor current representation. Distinctness of the
points is needed for cyclicity, not for the current bracket. -/
def rep (z : Fin N → ℂ) : CurrentModule f (Space n N) :=
  tensorRep (fun i => shiftRep f hJ hskew (z i))

theorem op_eq_jetOp (z : Fin N → ℂ) (c : Fin n) (k : ℕ) :
    (rep f hJ hskew z).op c k = JetInterpolation.jetOp z
      (fun i => localOp i (D1SiteG.zeroOp f c))
      (fun i => localOp i (D1SiteG.oneOp c)) k := by
  simp only [rep, tensorRep_op, tensorOp, shiftRep_op, shiftOp,
    localOp_add, localOp_smul, JetInterpolation.jetOp]

end
end VOA.DeligneAudit.D1TensorG

#print axioms VOA.DeligneAudit.D1TensorG.shiftRep
#print axioms VOA.DeligneAudit.D1TensorG.rep
#print axioms VOA.DeligneAudit.D1TensorG.op_eq_jetOp
