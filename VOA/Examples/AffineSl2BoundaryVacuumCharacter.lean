/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BoundarySymbolNonzero
import VOA.Commutative.GordonConformalCharacter
import VOA.Filtered.BoundaryArcLiMap
import VOA.Filtered.BoundaryArcConformalSqueeze

/-!
# The actual boundary vacuum character and dimension interfaces

The series below is defined from actual simple-VOA dimensions. It is independent
of the product candidate. Equality with that product is proved in
`AffineSl2BoundaryMainTheorems` using the actual determinant root orders. The
dimension squeeze and formal chain identity use the independent definitions here.
-/
namespace VOA.AffineSl2BoundaryCharacter
open VOA.AffineSl2BoundarySingularFamily VOA.AffineSl2GeneralRigidity
open VOA.BoundaryAuxiliary VOA.QSeries
noncomputable section

/-- The actual simple affine boundary VOA at index m. -/
abbrev vacuum (m : ℕ) := simple (level m) (level_noncritical m)

/-- Unshifted ordinary character, defined from the actual conformal-weight dimensions. -/
def character (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun N => (Module.finrank ℂ ((vacuum m).grading N) : ℚ))

@[simp] theorem coeff_character (m N : ℕ) :
    PowerSeries.coeff N (character m) = (Module.finrank ℂ ((vacuum m).grading N) : ℚ) :=
  PowerSeries.coeff_mk _ _

/-- The boundary product identified with the actual character in the main theorem module. -/
def product (m : ℕ) : PowerSeries ℚ :=
  (PowerSeries.expand (denominator m) (by dsimp [denominator]; omega) euler) ^ 3 *
    reciprocalEuler ^ 3

/-- Literal coefficientwise acceptance criterion for the full character theorem. -/
theorem character_eq_product_iff (m : ℕ) :
    character m = product m ↔ ∀ N : ℕ,
      (Module.finrank ℂ ((vacuum m).grading N) : ℚ) = PowerSeries.coeff N (product m) := by
  constructor
  · intro h N
    rw [← coeff_character, h]
  · intro h
    apply PowerSeries.ext
    intro N
    simpa only [coeff_character] using h N

/-- The proved Sections 2--5 bound, in the paper's positive boundary index. -/
theorem sourcePiece_finrank_le_product (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    (Module.finrank ℂ (sourcePiece (K := ℂ) m N) : ℚ) ≤ PowerSeries.coeff N (product m) := by
  cases m with
  | zero => omega
  | succ n =>
      simpa only [product, denominator] using
        VOA.GordonConformalCharacter.sourcePiece_finrank_le_product (K := ℂ) n N

/-- The actual simple-VOA weight space is no larger than the actual arc piece,
by the proved canonical current surjection in the fixed conformal weight. -/
theorem vacuum_finrank_le_sourcePiece (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    Module.finrank ℂ ((vacuum m).grading N) ≤
      Module.finrank ℂ (sourcePiece (K := ℂ) m N) := by
  let C := uniformCandidate m hm
  letI := finiteDimensional_sourcePiece (K := ℂ) m N
  have h := LinearMap.finrank_le_finrank_of_surjective
    (BoundaryArcConformalSqueeze.pieceMap_surjective
      (BoundaryArcLiMap.simpleVOA C) (BoundaryArcLiMap.gen C) (BoundaryArcLiMap.gen_mem C)
      m (BoundaryArcLiMap.sourceIdeal_le_kernel C) (BoundaryArcLiMap.polynomialMap_surjective C) N)
  rw [BoundaryArcConformalSqueeze.layers_finrank] at h
  exact h

/-- One side of the full character theorem is already unconditional in every
conformal weight of the actual simple VOA. -/
theorem coeff_character_le_product (m : ℕ) (hm : 1 ≤ m) (N : ℕ) :
    PowerSeries.coeff N (character m) ≤ PowerSeries.coeff N (product m) := by
  rw [coeff_character]
  have h := Nat.cast_le (α := ℚ).mpr (vacuum_finrank_le_sourcePiece m hm N)
  exact h.trans (sourcePiece_finrank_le_product m hm N)

/-- The remaining character gate is precisely the reverse all-degree dimension bound. -/
theorem character_eq_product_iff_reverse_bound (m : ℕ) (hm : 1 ≤ m) :
    character m = product m ↔ ∀ N : ℕ,
      PowerSeries.coeff N (product m) ≤ PowerSeries.coeff N (character m) := by
  constructor
  · intro h N
    rw [h]
  · intro h
    apply PowerSeries.ext
    intro N
    exact le_antisymm (coeff_character_le_product m hm N) (h N)

/-- The actual character identity is exactly the remaining input to the ordinary
conformal Hilbert squeeze, with the arc upper bound already proved. -/
theorem sourcePiece_finrank_le_vacuum_of_character (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) (N : ℕ) :
    Module.finrank ℂ (sourcePiece (K := ℂ) m N) ≤
      Module.finrank ℂ ((vacuum m).grading N) := by
  have h := sourcePiece_finrank_le_product m hm N
  rw [← hcharacter, coeff_character] at h
  exact_mod_cast h

/-- The actual chain character conclusion once the independent full character
formula is proved. The Section 5 chain/product identity itself is unconditional. -/
theorem character_eq_chain_of_product (m : ℕ) (hm : 1 ≤ m)
    (hcharacter : character m = product m) :
    character m = hilbertBoundSeries (K := ℚ) m := by
  rw [hcharacter, hilbertBoundSeries_product m hm]
  rfl

end
end VOA.AffineSl2BoundaryCharacter
