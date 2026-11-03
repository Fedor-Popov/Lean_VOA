/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralDeformationPole
import VOA.Examples.AffineSl2NormalizedRepresentation

/-!
# Actual affine action with the varying central level

At every nonzero noncritical level, the actual normalized deformation yields
a full affine Lie representation whose center is kI+δN, with N²=0. The scalar
is extracted from that deformation, not supplied as an independent obstruction
assumption. Its vanishing remains to be proved for general admissible levels.
-/
namespace VOA.AffineSl2GeneralRigidity
open AffineVOA AffineVOA.Inst AffineLie Deform
open Module (End)
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)
local notation "I" => QuotVOA.maxGradedIdeal (universal k hk)

/-- The invariant form on the concrete weight-one basis agrees with the
coordinate sl₂ Killing form after the (e,f,h) to (e,h,f) order conversion. -/
theorem currentPairing_affineCurrent (x y : Sl2) :
    (currentPairing k hk hk0) ((affineCurrent k hk hk0) x) ((affineCurrent k hk hk0) y) = kappaForm x y := by
  simp only [currentPairing, sl2Pairing, affineCurrent, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, kappaForm_apply, Fin.sum_univ_three, kappa]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ite_true, ite_false]
  ring

/-- A normalized deformation at any nonzero noncritical level with its actual pole parameter gives an affine
Lie representation with a potentially nonscalar central action. The pole parameter
hypothesis is furnished uniquely by `(simple_existsUnique_pole_parameter k hk hk0)`. -/
noncomputable def simple_normalizedCurrentData (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1, D.poleVec a b = ((currentPairing k hk hk0) a b * δ) • (simple k hk).vacuum) :
    AffineCentralCurrentData ((WakModule k ⧸ I) × (WakModule k ⧸ I)) :=
  normalizedDeformationCurrentData D hD hnorm k δ (((simple k hk).grading 1).subtype.comp (affineCurrent k hk hk0))
    (fun x => ((affineCurrent k hk hk0) x).property)
    (fun x y => congrArg (fun v : (simple k hk).grading 1 => (v : WakModule k ⧸ I))
      ((affineCurrent_lie k hk hk0) x y).symm)
    (affineCurrent_pole k hk hk0) (fun x y => by
      have h := hδ ((affineCurrent k hk hk0) x) ((affineCurrent k hk hk0) y)
      rw [(currentPairing_affineCurrent k hk hk0), mul_comm] at h
      exact h)

/-- Every normalized graded deformation at any nonzero noncritical level supplies a concrete affine Lie
representation whose currents are the lifted modes and whose center is the
original level plus its actual tangent pole parameter. No regularity is assumed. -/
theorem simple_exists_normalized_representation (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃ (δ : ℂ) (ρ : AffSl2 →ₗ⁅ℂ⁆ End ℂ ((WakModule k ⧸ I) × (WakModule k ⧸ I))),
      (∀ a b : (simple k hk).grading 1, D.poleVec a b = ((currentPairing k hk hk0) a b * δ) • (simple k hk).vacuum) ∧
      (∀ x n, ρ (ofLoop kappaForm kappaForm_isInvariant x n) =
        liftedMode D ((affineCurrent k hk hk0) x) n) ∧
      ρ (AffineLie.C kappaForm kappaForm_isInvariant) =
        k • (1 : End ℂ ((WakModule k ⧸ I) × (WakModule k ⧸ I))) + δ • tangentShift ∧
      ρ (ell0 kappaForm kappaForm_isInvariant) = liftedDegree (W := (simple k hk)) := by
  obtain ⟨δ, hδ, _⟩ := (simple_existsUnique_pole_parameter k hk hk0) D hD hnorm
  let A := (simple_normalizedCurrentData k hk hk0) D hD hnorm δ hδ
  exact ⟨δ, A.rho, hδ, A.rho_ofLoop, A.rho_C, A.rho_ell0⟩

end VOA.AffineSl2GeneralRigidity
