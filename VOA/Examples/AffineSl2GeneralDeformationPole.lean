/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2GeneralRegularReconstruction
import VOA.Core.DeformationPoleForm

/-!
# The sole scalar level variation at every nonzero noncritical level

Jacobi and the proved current basis extract one unique scalar from every
normalized graded deformation. Its vanishing gives triviality by the actual
fixed-level reconstruction. No claim that it vanishes at admissible levels
is made here; that requires the ordinary singular-pairing obstruction.
-/
namespace VOA.AffineSl2GeneralRigidity
open Deform LQ43
variable (k : ℂ) (hk : k + 2 ≠ 0) (hk0 : k ≠ 0)

/-- The normalized invariant form on the actual weight-one space, in the proved
(e,h,f) basis. Its nonzero basis entries are κ(e,f)=κ(f,e)=1 and κ(h,h)=2. -/
noncomputable def currentPairing (a b : (simple k hk).grading 1) : ℂ :=
  sl2Pairing (simple_weightOneBasis k hk hk0) a b

/-- Every normalized graded deformation has one uniquely determined level
parameter. This is extracted from its own pole pairing using the proved sl₂
basis, invariance from Jacobi, and nonvanishing of the vacuum. -/
theorem simple_existsUnique_pole_parameter (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃! δ : ℂ, ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = ((currentPairing k hk hk0) a b * δ) • (simple k hk).vacuum := by
  obtain ⟨δ, hδ⟩ := exists_currentPole_sl2 D hD hnorm
    (simple_weightOneBasis k hk hk0) (simple_weightOneTriple k hk hk0)
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  have h := (hr ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2)).symm.trans
    (hδ ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2))
  have he : (currentPairing k hk hk0) ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2) = 1 := by
    simp only [currentPairing, sl2Pairing, Module.Basis.repr_self]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  change ((currentPairing k hk hk0) _ _ * r) • (simple k hk).vacuum =
    ((currentPairing k hk hk0) _ _ * δ) • (simple k hk).vacuum at h
  rw [he, one_mul, one_mul] at h
  exact eq_of_smul_vacuum_eq (simple_vacuum_ne_zero k hk) h

/-- The master commutator has the same single scalar for every pair of currents.
This is derived from the deformation, without assuming the paper's master
relation or an independently supplied invariant pairing. -/
theorem simple_normalized_master_relation (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃ δ : ℂ, ∀ (a b : (simple k hk).grading 1) (x) (m n : ℤ),
      D.smul₁ a m ((simple k hk).smul b n x) + (simple k hk).smul a m (D.smul₁ b n x)
        - (D.smul₁ b n ((simple k hk).smul a m x) + (simple k hk).smul b n (D.smul₁ a m x))
      = D.smul₁ ((simple k hk).smul a 0 b) (m + n) x
        + if m + n = 0 then ((m : ℂ) * ((currentPairing k hk hk0) a b * δ)) • x else 0 := by
  obtain ⟨δ, hδ, _⟩ := (simple_existsUnique_pole_parameter k hk hk0) D hD hnorm
  refine ⟨δ, fun a b x m n => ?_⟩
  exact poleForm_current_commutator D hD hnorm a.property b.property
    ((currentPairing k hk hk0) a b * δ) (hδ a b).symm x m n

/-- With the actual normalized pole parameter supplied by the theorem above,
regularity is exactly its vanishing. This does not say that the parameter
vanishes; that remains the singular-vector obstruction step. -/
theorem simple_regular_iff_pole_parameter_zero (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = ((currentPairing k hk hk0) a b * δ) • (simple k hk).vacuum) :
    D.Regular ↔ δ = 0 := by
  constructor
  · intro hreg
    have h := hδ ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2)
    have he : (currentPairing k hk hk0) ((simple_weightOneBasis k hk hk0) 0) ((simple_weightOneBasis k hk hk0) 2) = 1 := by
      simp only [currentPairing, sl2Pairing, Module.Basis.repr_self]
      norm_num [Finsupp.single_apply, Fin.ext_iff]
    rw [D.poleVec_eq_zero_of_regular hreg ((simple_weightOneBasis k hk hk0) 0).property
      ((simple_weightOneBasis k hk hk0) 2).property, he, one_mul] at h
    exact eq_zero_of_smul_vacuum_eq_zero (simple_vacuum_ne_zero k hk) h.symm
  · intro hz
    apply (regular_iff_zero_one D hD).mpr
    intro a ha b hb
    refine ⟨hnorm a ha b hb, ?_⟩
    have h := hδ ⟨a, ha⟩ ⟨b, hb⟩
    simpa only [hz, mul_zero, zero_smul] using h


/-- If the scalar extracted from an actual normalized deformation is zero,
the deformation is a coboundary. This uses the proved reconstruction at the
same level, not an assumed regular-rigidity premise. -/
theorem simple_isTrivial_of_zero_pole_parameter (D : FirstOrderDeformation (simple k hk))
    (hD : D.IsGraded) (hnorm : D.InPoleForm)
    (hzero : ∀ a b : (simple k hk).grading 1,
      D.poleVec a b = (currentPairing k hk hk0 a b * (0 : ℂ)) • (simple k hk).vacuum) :
    D.IsTrivial :=
  simple_regular_isTrivial k hk hk0 D hD
    ((simple_regular_iff_pole_parameter_zero k hk hk0 D hD hnorm 0 hzero).2 rfl)

include hk0 in
/-- Arbitrary graded rigidity reduces to normalized pole vanishing, with
current normalization and regular reconstruction discharged at every nonzero
noncritical level. This is an interface, not an admissible-level theorem. -/
theorem simple_isRigidGraded_of_normalisedPoleVanishes
    (hvan : NormalisedPoleVanishes (simple k hk)) : IsRigidGraded (simple k hk) :=
  isRigidGraded_of_sl2Basis (simple k hk) (simple_sl2BasisOnWeightOne k hk hk0)
    (simple_regularImpliesTrivialGraded k hk hk0) hvan

end VOA.AffineSl2GeneralRigidity
