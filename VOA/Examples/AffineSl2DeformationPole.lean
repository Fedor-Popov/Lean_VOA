/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2RigidityBasis
import VOA.Core.DeformationPoleForm

/-!
# The actual scalar level parameter of a normalized affine deformation

For the simple affine VOA at level −4/3, the explicit current basis and Jacobi
give a unique scalar describing every normalized graded pole pairing.
This proves the single-parameter step of the deformation-to-obstruction bridge.
It does not prove that the parameter vanishes or supply the singular-vector
coordinate equations needed for that conclusion.
-/
namespace VOA.LQ43
open Deform

/-- The normalized invariant form on the actual weight-one space, in the proved
(e,h,f) basis. Its nonzero basis entries are κ(e,f)=κ(f,e)=1 and κ(h,h)=2. -/
noncomputable def currentPairing (a b : L43.grading 1) : ℂ :=
  sl2Pairing L43_weightOneBasis a b

/-- Every normalized graded deformation has one uniquely determined level
parameter. This is extracted from its own pole pairing using the proved sl₂
basis, invariance from Jacobi, and nonvanishing of the vacuum. -/
theorem L43_existsUnique_pole_parameter (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃! δ : ℂ, ∀ a b : L43.grading 1,
      D.poleVec a b = (currentPairing a b * δ) • L43.vacuum := by
  obtain ⟨δ, hδ⟩ := exists_currentPole_sl2 D hD hnorm
    L43_weightOneBasis L43_weightOneTriple
  refine ⟨δ, hδ, ?_⟩
  intro r hr
  have h := (hr (L43_weightOneBasis 0) (L43_weightOneBasis 2)).symm.trans
    (hδ (L43_weightOneBasis 0) (L43_weightOneBasis 2))
  have he : currentPairing (L43_weightOneBasis 0) (L43_weightOneBasis 2) = 1 := by
    simp only [currentPairing, sl2Pairing, Module.Basis.repr_self]
    norm_num [Finsupp.single_apply, Fin.ext_iff]
  change (currentPairing _ _ * r) • L43.vacuum =
    (currentPairing _ _ * δ) • L43.vacuum at h
  rw [he, one_mul, one_mul] at h
  exact eq_of_smul_vacuum_eq L43_vacuum_ne_zero h

/-- The master commutator has the same single scalar for every pair of currents.
This is derived from the deformation, without assuming the paper's master
relation or an independently supplied invariant pairing. -/
theorem L43_normalized_master_relation (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) :
    ∃ δ : ℂ, ∀ (a b : L43.grading 1) (x) (m n : ℤ),
      D.smul₁ a m (L43.smul b n x) + L43.smul a m (D.smul₁ b n x)
        - (D.smul₁ b n (L43.smul a m x) + L43.smul b n (D.smul₁ a m x))
      = D.smul₁ (L43.smul a 0 b) (m + n) x
        + if m + n = 0 then ((m : ℂ) * (currentPairing a b * δ)) • x else 0 := by
  obtain ⟨δ, hδ, _⟩ := L43_existsUnique_pole_parameter D hD hnorm
  refine ⟨δ, fun a b x m n => ?_⟩
  exact poleForm_current_commutator D hD hnorm a.property b.property
    (currentPairing a b * δ) (hδ a b).symm x m n

/-- With the actual normalized pole parameter supplied by the theorem above,
regularity is exactly its vanishing. This does not say that the parameter
vanishes; that remains the singular-vector obstruction step. -/
theorem L43_regular_iff_pole_parameter_zero (D : FirstOrderDeformation L43)
    (hD : D.IsGraded) (hnorm : D.InPoleForm) (δ : ℂ)
    (hδ : ∀ a b : L43.grading 1,
      D.poleVec a b = (currentPairing a b * δ) • L43.vacuum) :
    D.Regular ↔ δ = 0 := by
  constructor
  · intro hreg
    have h := hδ (L43_weightOneBasis 0) (L43_weightOneBasis 2)
    have he : currentPairing (L43_weightOneBasis 0) (L43_weightOneBasis 2) = 1 := by
      simp only [currentPairing, sl2Pairing, Module.Basis.repr_self]
      norm_num [Finsupp.single_apply, Fin.ext_iff]
    rw [D.poleVec_eq_zero_of_regular hreg (L43_weightOneBasis 0).property
      (L43_weightOneBasis 2).property, he, one_mul] at h
    exact eq_zero_of_smul_vacuum_eq_zero L43_vacuum_ne_zero h.symm
  · intro hz
    apply (regular_iff_zero_one D hD).mpr
    intro a ha b hb
    refine ⟨hnorm a ha b hb, ?_⟩
    have h := hδ ⟨a, ha⟩ ⟨b, hb⟩
    simpa only [hz, mul_zero, zero_smul] using h

end VOA.LQ43
