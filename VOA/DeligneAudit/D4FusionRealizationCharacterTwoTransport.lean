import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Parameter and output transport performed before specializing the computable algorithm. -/
theorem character_transport (A A' : List (List ℤ)) (theta theta' : List ℤ)
    (word word' : List ℕ) (m : ℕ) (v v' : LPoly)
    (hA : A = A') (ht : theta = theta') (hw : word = word') (hv : v = v')
    (h : demazureChar A theta word m = v) : demazureChar A' theta' word' m = v' := by
  cases hA; cases ht; cases hw; cases hv
  exact h

theorem natural_of_integer (A : List (List ℤ)) (theta : List ℤ) (word : List ℕ)
    (m N : ℕ) (value : ℤ)
    (h : (((demazureChar A theta word m).filter
      fun (t : Term) => decide (t.1.2 + (m : ℤ) * m = (N : ℤ))).map fun t => t.2).sum = value) :
    levelOneDemazureHilb A theta word m N = value.toNat := congrArg Int.toNat h

end VOA.DeligneAudit.D4CharacterTwo
