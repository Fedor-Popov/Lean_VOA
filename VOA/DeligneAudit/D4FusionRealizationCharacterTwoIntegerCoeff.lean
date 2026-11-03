import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Named coefficient maps prevent accidental reduction of the closed algorithm. -/
@[irreducible] def integerCoeff (values : LPoly) (shift : ℤ) (N : ℕ) : ℤ :=
  ((values.filter fun (t : Term) => decide (t.1.2 + shift = (N : ℤ))).map
    fun t => t.2).sum

theorem coefficient_from_sum (values : LPoly) (shift : ℤ) (N : ℕ) (value : ℤ)
    (h : ((values.filter fun (t : Term) => decide (t.1.2 + shift = (N : ℤ))).map
      fun t => t.2).sum = value) : integerCoeff values shift N = value := by
  unfold integerCoeff
  exact h

theorem coefficient_from_character (A : List (List ℤ)) (theta : List ℤ)
    (word : List ℕ) (m : ℕ) (values : LPoly) (shift : ℤ) (N : ℕ) (value : ℤ)
    (hc : demazureChar A theta word m = values)
    (hv : integerCoeff values shift N = value) :
    integerCoeff (demazureChar A theta word m) shift N = value :=
  (congrArg (fun v => integerCoeff v shift N) hc).trans hv

theorem natural_coefficient_bridge (A : List (List ℤ)) (theta : List ℤ)
    (word : List ℕ) (m N : ℕ) :
    levelOneDemazureHilb A theta word m N =
      (integerCoeff (demazureChar A theta word m) ((m : ℤ) * m) N).toNat := by
  unfold integerCoeff
  rfl

end VOA.DeligneAudit.D4CharacterTwo
