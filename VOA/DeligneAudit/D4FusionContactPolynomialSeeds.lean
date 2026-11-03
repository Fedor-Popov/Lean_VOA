import VOA.DeligneAudit.D4FusionContactPolynomialEval
import VOA.DeligneAudit.D4FusionContactPolynomialSource

/-!
# Actual seven seed polynomials in the full graded vector annihilator

The exact source identities are transferred to the restricted PBW symbols.
The seed ideal includes every polynomial multiple. Stability under the
candidate derivations is a subsequent, separate theorem.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def seedList (j : Fin 7) : List (Vars 2) :=
  [[(0,0), (0,0), (0,0)], [(0,0), (0,1)], [(0,1), (0,1)],
    [(8,0), (8,0), (8,0), (8,0), (8,0)], [(8,0), (8,0), (8,0), (8,1)],
    [(8,0), (8,1), (8,1)], [(8,1), (8,1), (8,1)]].getD j.val []

def seedPoly (j : Fin 7) : MvPolynomial (Vars 2) ℂ := polyWord (seedList j)

def seedIdeal : Ideal (MvPolynomial (Vars 2) ℂ) := Ideal.span (Set.range seedPoly)

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

theorem source_seed_word_zero (h : LocalWeylRelG D4sector R w 2) (j : Fin 7) :
    currentRadicalWord R ((seedList j).map (modeLetter 2)) w = 0 := by
  have hs := PolynomialSource.source_seedRel h
  fin_cases j
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      PolynomialSource.simpleF, pow_succ, Module.End.mul_apply] using hs.a_cube
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      PolynomialSource.simpleF] using hs.a_pair
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      PolynomialSource.simpleF] using hs.a_square
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      currentCenter, pow_succ, Module.End.mul_apply] using hs.c_five
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      currentCenter, pow_succ, Module.End.mul_apply] using hs.c31
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      currentCenter] using hs.c12
  · simpa [seedList, modeLetter, currentRadicalWord, wordOp, radIndex,
      currentCenter] using hs.c03

/-- Every actual seed belongs to the full vector annihilator ideal. -/
theorem source_seed_mem_ann (h : LocalWeylRelG D4sector R w 2) (j : Fin 7) :
    seedPoly j ∈ annIdeal R w (modeLetter 2) := by
  change polyEval R w (modeLetter 2) (seedPoly j) = 0
  rw [seedPoly, polyEval_polyWord]
  exact grWord_zero_of_source_zero R w _ (source_seed_word_zero h j)

/-- All polynomial multiples of the seven seeds are included. This does
not yet claim stability under the candidate current derivations. -/
theorem source_seedIdeal_le_ann (h : LocalWeylRelG D4sector R w 2) :
    seedIdeal ≤ annIdeal R w (modeLetter 2) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact source_seed_mem_ann h j

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_seed_mem_ann
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.source_seedIdeal_le_ann
