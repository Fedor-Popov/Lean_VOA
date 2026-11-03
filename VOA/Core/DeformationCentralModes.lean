/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationLiftedModes
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The central operator of a normalized first-order current deformation

A normalized deformation need not be regular. Its lifted currents have central
operator k·identity + δ·N, where N moves a constant state to its tangent copy and
kills tangent states. N squares to zero and commutes with every lifted mode.
Thus the level really moves by a dual-number scalar on the actual state space.
The dual-number action below is constructed explicitly, so later singular-vector
calculations can transport polynomial identities without assuming a representation.
-/
namespace VOA.Deform
open Module (End)
open TrivSqZeroExt
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- Multiplication by the infinitesimal parameter: (v,v₁) goes to (0,v). -/
def tangentShift : End ℂ (V × V) where
  toFun x := (0, x.1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The tangent shift is square-zero, reflecting the first-order truncation. -/
theorem tangentShift_sq : (tangentShift : End ℂ (V × V)) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  rfl

/-- Multiplication by any dual-number scalar on the first-order state space.
Its off-diagonal coefficient multiplies the constant coordinate only. -/
def dualScalarAction : DualNumber ℂ →ₐ[ℂ] End ℂ (V × V) where
  toFun z := z.fst • (1 : End ℂ (V × V)) + z.snd • tangentShift
  map_zero' := by simp
  map_one' := by simp
  map_add' z w := by simp only [fst_add, snd_add, add_smul]; abel
  map_mul' z w := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [Module.End.mul_apply, tangentShift, smul_add, smul_smul, smul_eq_mul] <;> module
  commutes' z := by
    simp [Algebra.algebraMap_eq_smul_one]

/-- Explicit coordinates of the constructed dual-number scalar action. -/
theorem dualScalarAction_apply (z : DualNumber ℂ) (x : V × V) :
    dualScalarAction z x = (z.fst • x.1, z.fst • x.2 + z.snd • x.1) := by
  apply Prod.ext <;> simp [dualScalarAction, tangentShift]

/-- A lifted current commutes with the tangent shift because both its diagonal
blocks are the original current mode. The correction occupies only the lower block. -/
theorem tangentShift_comm (D : FirstOrderDeformation W) (a : V) (n : ℤ) :
    Commute (tangentShift : End ℂ (V × V)) (liftedMode D a n) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> simp [Module.End.mul_apply, tangentShift, liftedMode]

/-- The tangent shift also commutes with the external degree derivation, which
acts identically on the two coordinates. -/
theorem tangentShift_degree_comm :
    Commute (tangentShift : End ℂ (V × V)) (liftedDegree (W := W)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext <;> simp [Module.End.mul_apply, tangentShift, liftedDegree]

/-- Normalized current commutators on the actual extension include the original
scalar central term and the tangent central term supplied by the actual pole.
Neither the tangent coefficient nor its vanishing is assumed independently. -/
theorem liftedMode_comm_of_pole (D : FirstOrderDeformation W)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) {a b : V}
    (ha : a ∈ W.grading 1) (hb : b ∈ W.grading 1)
    (β δ : ℂ) (hp : W.smul a 1 b = β • W.vacuum)
    (hδ : D.smul₁ a 1 b = δ • W.vacuum) (m n : ℤ) :
    ⁅liftedMode D a m, liftedMode D b n⁆ =
      liftedMode D (W.smul a 0 b) (m + n) +
        if m + n = 0 then (m : ℂ) •
          (β • (1 : End ℂ (V × V)) + δ • tangentShift) else 0 := by
  by_cases hmn : m + n = 0
  all_goals
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · have h := current_mode_commutator ha hb β hp x.1 m n
      simpa [hmn, LieRing.of_associative_ring_bracket, Module.End.mul_apply,
        liftedMode_apply, tangentShift, smul_smul] using h
    · have h := current_mode_commutator ha hb β hp x.2 m n
      have hd := poleForm_current_commutator D hD hnorm ha hb δ hδ.symm x.1 m n
      simp only [hmn, if_true, if_false] at h hd
      simp only [hmn, if_true, if_false, LieRing.of_associative_ring_bracket,
        LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, liftedMode_apply,
        Prod.snd_sub, Prod.snd_add, LinearMap.smul_apply, Module.End.one_apply,
        LinearMap.zero_apply, Prod.smul_snd, Prod.snd_zero, W.smul_add_right]
      change _ = _ + _
      try dsimp only [tangentShift, LinearMap.coe_mk, AddHom.coe_mk]
      rw [eq_sub_of_add_eq h.symm, eq_sub_of_add_eq hd.symm]
      try simp only [smul_add, smul_smul]
      abel

/-- A polynomial of the central block operator has the expected first-order
Taylor expansion. This transports scalar central identities into identities on
the actual extension, including their tangent coefficient. -/
theorem dualScalarAction_polynomial (p : Polynomial ℂ) (k δ : ℂ) :
    Polynomial.aeval (k • (1 : End ℂ (V × V)) + δ • tangentShift) p =
      p.eval k • (1 : End ℂ (V × V)) + (p.derivative.eval k * δ) • tangentShift := by
  have he (q : Polynomial ℂ) : q.aeval (inl k : DualNumber ℂ) = inl (q.eval k) :=
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval k q
  have ht : p.aeval (inl k + inr δ : DualNumber ℂ) =
      inl (p.eval k) + inr (p.derivative.eval k * δ) := by
    rw [Polynomial.aeval_add_of_sq_eq_zero p _ _ (by simp [pow_two]), he, he]
    ext <;> simp [mul_comm]
  have hc : dualScalarAction (V := V) (inl k + inr δ) =
      k • (1 : End ℂ (V × V)) + δ • tangentShift := by
    simp [dualScalarAction]
  rw [← hc, Polynomial.aeval_algHom_apply, ht]
  simp [dualScalarAction]

/-- If a central polynomial annihilates a pure nonzero state and has nonzero
derivative at the original level, the actual tangent level coefficient vanishes.
The annihilating polynomial must be proved from the representation; it is not
supplied automatically by the normalized current relations. -/
theorem tangent_zero_of_central_polynomial (p : Polynomial ℂ) (k δ : ℂ) (v : V)
    (hv : v ≠ 0) (hp : p.derivative.eval k ≠ 0)
    (hzero : (Polynomial.aeval (k • (1 : End ℂ (V × V)) + δ • tangentShift) p :
      End ℂ (V × V)) (v, 0) = 0) :
    δ = 0 := by
  rw [dualScalarAction_polynomial] at hzero
  have hs := congrArg Prod.snd hzero
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Prod.snd_add, Prod.smul_snd, Prod.snd_zero, tangentShift, LinearMap.coe_mk,
    AddHom.coe_mk, smul_zero, zero_add] at hs
  exact (mul_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hv)).resolve_left hp

end VOA.Deform
