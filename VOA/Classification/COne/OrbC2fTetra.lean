import VOA.Classification.COne.OrbC2fFixed

/-! # Nonzero primary and weight-sixteen states in the actual tetrahedral orbifold -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbC2f
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice
  PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2b

/-- Fixedness is equivalent under the explicit sublattice equivalence. -/
theorem plusToKlein_fixed_iff (v : VP 4 four_ge_one) :
    plusToKlein v ∈ (orbifold (Subgroup.zpowers kleinCubic)).carrier ↔
      v ∈ (orbifold (Subgroup.zpowers plusCubic)).carrier := by
  rw [mem_orbifold_zpowers_iff, mem_orbifold_zpowers_iff,
    ← plusCubic_intertwine, plusToKlein.injective.eq_iff]

theorem map_plus_fixed :
    (orbifold (Subgroup.zpowers plusCubic)).carrier.map plusToKlein.toLinearMap =
      (orbifold (Subgroup.zpowers kleinCubic)).carrier := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (plusToKlein_fixed_iff x).mpr hx
  · intro hv
    refine ⟨plusToKlein.symm v, ?_, plusToKlein.apply_symm_apply v⟩
    apply (plusToKlein_fixed_iff _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hv

def fixedEquivKlein : (orbifold (Subgroup.zpowers plusCubic)).carrier ≃ₗ[ℂ]
    (orbifold (Subgroup.zpowers kleinCubic)).carrier :=
  (plusToKlein.submoduleMap _).trans (LinearEquiv.ofEq _ _ map_plus_fixed)

theorem fixedEquivKlein_hom : IsVOAHom (orbifoldVOA (Subgroup.zpowers plusCubic))
    (orbifoldVOA (Subgroup.zpowers kleinCubic)) fixedEquivKlein.toLinearMap := by
  constructor
  · exact Subtype.ext plusToKlein_vacuum
  · intro a n b
    exact Subtype.ext (plusToKlein_smul a b n)

theorem fixedEquivKlein_omega :
    fixedEquivKlein (orbifoldVOA (Subgroup.zpowers plusCubic)).conformalVector =
      (orbifoldVOA (Subgroup.zpowers kleinCubic)).conformalVector :=
  Subtype.ext plusToKlein_omega

/-- Explicitly links the transported action to the existing `tetra_cubic_iso`. -/
theorem plus_cubic_tetra_iso :
    VOAIsomorphic (orbifoldVOA (Subgroup.zpowers plusCubic)) (orbifoldVOA tetra) :=
  voaIso_trans' ⟨fixedEquivKlein, fixedEquivKlein_hom, fixedEquivKlein_omega⟩ tetra_cubic_iso

def fixedNine : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
  ⟨weightNine, (mem_orbifold_zpowers_iff _ _).mpr weightNine_fixed⟩

def fixedSixteen : (orbifold (Subgroup.zpowers plusCubic)).carrier :=
  ⟨weightSixteen, (mem_orbifold_zpowers_iff _ _).mpr weightSixteen_fixed⟩

theorem fixedNine_nonzero_primary :
    fixedNine ≠ 0 ∧ fixedNine ∈ (orbifoldVOA (Subgroup.zpowers plusCubic)).grading 9 ∧
      ∀ n : ℤ, 0 < n → (orbifoldVOA (Subgroup.zpowers plusCubic)).L n fixedNine = 0 := by
  refine ⟨fun hz => weightNine_ne_zero (congrArg Subtype.val hz), weightNine_mem_grading, ?_⟩
  intro n hn
  exact Subtype.ext (weightNine_primary n hn)

theorem fixedSixteen_nonzero_weight : fixedSixteen ≠ 0 ∧
    fixedSixteen ∈ (orbifoldVOA (Subgroup.zpowers plusCubic)).grading 16 :=
  ⟨fun hz => weightSixteen_ne_zero (congrArg Subtype.val hz), weightSixteen_mem_grading⟩

/-- Genuine tetrahedral states: no fixedness or generator-action hypothesis remains. -/
theorem tetra_nonzero_primary_nine_and_sixteen :
    ∃ U X : (orbifold tetra).carrier,
      (U ≠ 0 ∧ U ∈ (orbifoldVOA tetra).grading 9 ∧
        ∀ n : ℤ, 0 < n → (orbifoldVOA tetra).L n U = 0) ∧
      X ≠ 0 ∧ X ∈ (orbifoldVOA tetra).grading 16 := by
  obtain ⟨e, he, hω⟩ := plus_cubic_tetra_iso
  refine ⟨e fixedNine, e fixedSixteen, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun hz => fixedNine_nonzero_primary.1 (e.map_eq_zero_iff.mp hz)
  · exact ConverseUniverse.voaHom_map_grading he hω fixedNine_nonzero_primary.2.1
  · intro n hn
    have ht := ConverseUniverse.voaHom_map_L he hω n fixedNine
    rw [fixedNine_nonzero_primary.2.2 n hn, map_zero] at ht
    exact ht.symm
  · exact fun hz => fixedSixteen_nonzero_weight.1 (e.map_eq_zero_iff.mp hz)
  · exact ConverseUniverse.voaHom_map_grading he hω fixedSixteen_nonzero_weight.2

end VOA.Classification.COne.OrbC2f
