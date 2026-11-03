import VOA.Classification.COne.OrbifoldIdentification
import VOA.Classification.COne.PlusC2Final
import VOA.Classification.COne.ConverseUniverseTransport
import VOA.Classification.COne.OrbC2Reynolds

/-!
# Concrete cyclic and dihedral C₂ examples

These use the actual charge-rotation and reflection embeddings already
identified in `OrbifoldIdentification`, not arbitrary embeddings of abstract
groups. In particular the dihedral group of order four gives a concrete
C₂-cofinite Klein-four fixed algebra, isomorphic to `V₈⁺`.
-/

namespace VOA.Classification.COne.OrbC2
open VOA

/-- All standard charge-rotation orbifolds are C₂-cofinite. -/
theorem cyclic_c2Cofinite (m : ℕ) (hm : 1 ≤ m) (n : ℕ) [NeZero n] :
    C2Cofinite (orbifoldVOA (cycHom m hm n).range) := by
  obtain ⟨e, he, _⟩ := orbifold_cyclic_iso m hm n
  exact ConverseUniverse.c2Cofinite_of_iso e he
    (V2m_c2Cofinite _ (one_le_mn2 m hm n))

/-- All standard dihedral orbifolds are C₂-cofinite, by the proved plus theorem. -/
theorem dihedral_c2Cofinite (m : ℕ) (hm : 1 ≤ m) (n : ℕ) [NeZero n] :
    C2Cofinite (orbifoldVOA (dihHom m hm n).range) := by
  obtain ⟨e, he, _⟩ := orbifold_dihedral_iso m hm n
  exact ConverseUniverse.c2Cofinite_of_iso e he
    (V2mPlus_c2Cofinite _ (one_le_mn2 m hm n))

/-- The actual order-four dihedral subgroup of `Aut V₂`: no conjugacy claim is used. -/
theorem standard_klein_four_c2Cofinite :
    C2Cofinite (orbifoldVOA (dihHom 1 le_rfl 2).range) :=
  dihedral_c2Cofinite 1 le_rfl 2

end VOA.Classification.COne.OrbC2
