import VOA.DeligneAudit.DeligneFusionD1TensorGRank
import VOA.DeligneAudit.D4FusionToroidalCore
import Mathlib.Tactic.Module

/-!
# The untruncated toroidal evaluation action

The local `u` action is the checked coadjoint-plus-line current module. Evaluation
at `z` affects only the independent `t` mode. The tensor commutator follows from
the same-site current bracket and commutation of different tensor factors.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorLoop

noncomputable section

variable {n : ℕ} {f : Fin n → Fin n → Fin n → ℂ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An action of the two-variable, untruncated current algebra. -/
structure ToroidalAction (f : Fin n → Fin n → Fin n → ℂ)
    (V : Type*) [AddCommGroup V] [Module ℂ V] where
  op : Fin n → ℕ → ℕ → Module.End ℂ V
  comm : ∀ a b i j r s v,
    op a i r (op b j s v) - op b j s (op a i r v) =
      ∑ e, f a b e • op e (i + j) (r + s) v

variable {N : ℕ} (ρ : Fin N → CurrentModule f V) (z : Fin N → ℂ)

/-- Evaluation of the `t` variable on an actual tensor of `u` current sites. -/
def evalOp (c : Fin n) (i s : ℕ) : Module.End ℂ (Tensor (K := ℂ) (ι := Fin N)
    (W := V)) :=
  ∑ q : Fin N, z q ^ s • localOp q ((ρ q).op c i)

set_option maxHeartbeats 1000000 in
-- The double tensor sum makes simplification of this endomorphism identity expensive.
theorem evalOp_comm_end (a b : Fin n) (i j r s : ℕ) :
    evalOp ρ z a i r * evalOp ρ z b j s -
      evalOp ρ z b j s * evalOp ρ z a i r =
        ∑ e, f a b e • evalOp ρ z e (i + j) (r + s) := by
  have key : ∀ q p : Fin N,
      (z q ^ r • localOp q ((ρ q).op a i)) *
          (z p ^ s • localOp p ((ρ p).op b j)) -
        (z p ^ s • localOp p ((ρ p).op b j)) *
          (z q ^ r • localOp q ((ρ q).op a i)) =
        if q = p then
          ∑ e, f a b e •
            (z q ^ (r + s) • localOp q ((ρ q).op e (i + j))) else 0 := by
    intro q p
    by_cases hqp : q = p
    · subst p
      rw [if_pos rfl]
      rw [smul_mul_smul_comm, smul_mul_smul_comm,
        mul_comm (z q ^ s) (z q ^ r), ← smul_sub,
        local_current_comm, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [pow_add]
      module
    · rw [if_neg hqp]
      rw [smul_mul_smul_comm, smul_mul_smul_comm,
        localOp_comm hqp, mul_comm (z p ^ s) (z q ^ r), sub_self]
  have expand : evalOp ρ z a i r * evalOp ρ z b j s -
      evalOp ρ z b j s * evalOp ρ z a i r =
        ∑ q : Fin N, ∑ p : Fin N,
          ((z q ^ r • localOp q ((ρ q).op a i)) *
              (z p ^ s • localOp p ((ρ p).op b j)) -
            (z p ^ s • localOp p ((ρ p).op b j)) *
              (z q ^ r • localOp q ((ρ q).op a i))) := by
    simp only [evalOp, Finset.sum_mul_sum, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [expand]
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [evalOp, Finset.smul_sum]
  exact Finset.sum_comm

/-- Every finite tensor family of current sites gives a toroidal evaluation action. -/
def evalAction : ToroidalAction f (Tensor (K := ℂ) (ι := Fin N) (W := V)) where
  op := evalOp ρ z
  comm a b i j r s v := by
    have h := congrArg (fun A : Module.End ℂ (Tensor (K := ℂ) (ι := Fin N)
        (W := V)) => A v) (evalOp_comm_end ρ z a b i j r s)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
      LinearMap.smul_apply] using h

/-- The pure-evaluation action of the explicit one-site Demazure module. -/
def d1EvalAction (f : Fin n → Fin n → Fin n → ℂ) (hJ : JacobiCoord f)
    (hskew : ∀ a b c, f a b c = -f b a c) (z : Fin N → ℂ) :
    ToroidalAction f (D1TensorG.Space n N) :=
  evalAction (fun _ => VOA.DeligneAudit.D1SiteG.rep f hJ hskew) z

theorem d1EvalAction_op (f : Fin n → Fin n → Fin n → ℂ) (hJ : JacobiCoord f)
    (hskew : ∀ a b c, f a b c = -f b a c) (z : Fin N → ℂ)
    (c : Fin n) (i s : ℕ) :
    (d1EvalAction f hJ hskew z).op c i s =
      ∑ q : Fin N, z q ^ s • localOp q (VOA.DeligneAudit.D1SiteG.op f c i) := rfl

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.evalOp_comm_end
#print axioms VOA.DeligneAudit.Toroidal.evalAction
#print axioms VOA.DeligneAudit.Toroidal.d1EvalAction
