/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.DeformationCentralModes
import VOA.Examples.AffineSl2CentralCurrentRealization
import VOA.Examples.AffineSl2DeformationRepresentation
import VOA.Examples.AffineSl2DeformationPole

/-!
# The actual affine action of a normalized deformation

The scalar pole parameter of a normalized graded deformation is represented
by an actual affine Lie action, with central operator k·identity + δ·N. Unlike
the regular vacuum representation, it does not impose the fixed-level relation
C=k on the extension. This is the representation in which the singular-vector
obstruction must be computed. Its construction does not force δ to vanish.
-/
namespace VOA.AffineVOA
open Deform
open Module (End)
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}

/-- Construct all affine operators from the actual normalized deformation and
its verified current bracket and two pole pairings. The center includes the
first-order level change; its commutation follows from the block-operator formula. -/
noncomputable def normalizedDeformationCurrentData (D : FirstOrderDeformation W)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (k δ : ℂ) (j : Sl2 →ₗ[ℂ] V)
    (hj : ∀ x, j x ∈ W.grading 1)
    (hbr : ∀ x y, W.smul (j x) 0 (j y) = j ⁅x, y⁆)
    (hp : ∀ x y, W.smul (j x) 1 (j y) = (k * kappaForm x y) • W.vacuum)
    (hδ : ∀ x y, D.smul₁ (j x) 1 (j y) = (δ * kappaForm x y) • W.vacuum) :
    AffineCentralCurrentData (V × V) where
  loopMode n := (liftedModeLinear D n).comp j
  degree := liftedDegree (W := W)
  central := k • (1 : End ℂ (V × V)) + δ • tangentShift
  loop_comm x y m n := by
    change ⁅liftedMode D (j x) m, liftedMode D (j y) n⁆ = _
    rw [liftedMode_comm_of_pole D hD hnorm (hj x) (hj y) _ _ (hp x y) (hδ x y), hbr]
    change liftedMode D (j ⁅x, y⁆) (m + n) + _ =
      liftedMode D (j ⁅x, y⁆) (m + n) + _
    by_cases hmn : m + n = 0
    · simp only [hmn, if_true]
      module
    · simp only [hmn, if_false]
  degree_comm x n := liftedDegree_comm D hD (hj x) n
  central_comm x n := by
    change ⁅k • (1 : End ℂ (V × V)) + δ • tangentShift, liftedMode D (j x) n⁆ = 0
    rw [add_lie, smul_lie, smul_lie]
    have hN : ⁅(tangentShift : End ℂ (V × V)), liftedMode D (j x) n⁆ = 0 := by
      exact sub_eq_zero.mpr (tangentShift_comm D (j x) n)
    rw [hN]
    simp [LieRing.of_associative_ring_bracket]
  central_degree := by
    rw [add_lie, smul_lie, smul_lie]
    have hN : ⁅(tangentShift : End ℂ (V × V)), liftedDegree (W := W)⁆ = 0 := by
      exact sub_eq_zero.mpr tangentShift_degree_comm
    rw [hN]
    simp [LieRing.of_associative_ring_bracket]

end VOA.AffineVOA

namespace VOA.LQ43
open AffineVOA AffineVOA.Inst AffineLie Deform
open Module (End)
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm

/-- The invariant form on the concrete weight-one basis agrees with the
coordinate sl₂ Killing form after the (e,f,h) to (e,h,f) order conversion. -/
theorem currentPairing_affineCurrent (x y : Sl2) :
    currentPairing (affineCurrent x) (affineCurrent y) = kappaForm x y := by
  simp only [currentPairing, sl2Pairing, affineCurrent, LinearMap.coe_mk, AddHom.coe_mk,
    map_add, map_smul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, kappaForm_apply, Fin.sum_univ_three, kappa]
  simp only [show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    ite_true, ite_false]
  ring

/-- A normalized L43 deformation with its actual pole parameter gives an affine
Lie representation with a potentially nonscalar central action. The pole parameter
hypothesis is furnished uniquely by `L43_existsUnique_pole_parameter`. -/
noncomputable def L43_normalizedCurrentData (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : L43.grading 1, D.poleVec a b = (currentPairing a b * δ) • L43.vacuum) :
    AffineCentralCurrentData ((WakModule kk ⧸ I) × (WakModule kk ⧸ I)) :=
  normalizedDeformationCurrentData D hD hnorm kk δ ((L43.grading 1).subtype.comp affineCurrent)
    (fun x => (affineCurrent x).property)
    (fun x y => congrArg (fun v : L43.grading 1 => (v : WakModule kk ⧸ I))
      (affineCurrent_lie x y).symm)
    affineCurrent_pole (fun x y => by
      have h := hδ (affineCurrent x) (affineCurrent y)
      rw [currentPairing_affineCurrent, mul_comm] at h
      exact h)

/-- Every normalized graded L43 deformation supplies a concrete affine Lie
representation whose currents are the lifted modes and whose center is the
original level plus its actual tangent pole parameter. No regularity is assumed. -/
theorem L43_exists_normalized_representation (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃ (δ : ℂ) (ρ : AffSl2 →ₗ⁅ℂ⁆ End ℂ ((WakModule kk ⧸ I) × (WakModule kk ⧸ I))),
      (∀ a b : L43.grading 1, D.poleVec a b = (currentPairing a b * δ) • L43.vacuum) ∧
      (∀ x n, ρ (ofLoop kappaForm kappaForm_isInvariant x n) =
        liftedMode D (affineCurrent x) n) ∧
      ρ (AffineLie.C kappaForm kappaForm_isInvariant) =
        kk • (1 : End ℂ ((WakModule kk ⧸ I) × (WakModule kk ⧸ I))) + δ • tangentShift ∧
      ρ (ell0 kappaForm kappaForm_isInvariant) = liftedDegree (W := L43) := by
  obtain ⟨δ, hδ, _⟩ := L43_existsUnique_pole_parameter D hD hnorm
  let A := L43_normalizedCurrentData D hD hnorm δ hδ
  exact ⟨δ, A.rho, hδ, A.rho_ofLoop, A.rho_C, A.rho_ell0⟩

end VOA.LQ43
