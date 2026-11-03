import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCharacter
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCoefficients
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoIntegerCoeff

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Complete D4 two-cycle algorithm coefficients, including every zero tail coefficient. -/
theorem charTwo_coeff (N : ℕ) :
    integerCoeff (demazureChar cartan theta word 2) 4 N = profile N :=
  coefficient_from_character cartan theta word 2 state10 4 N (profile N) char_two_eq
    (coefficient_from_sum state10 4 N (profile N) (state10_coefficient N))

theorem hilb_nat_two (N : ℕ) :
    levelOneDemazureHilb cartan theta word 2 N = (profile N).toNat :=
  (natural_coefficient_bridge cartan theta word 2 N).trans (congrArg Int.toNat (charTwo_coeff N))

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.char_two_eq
#print axioms VOA.DeligneAudit.D4CharacterTwo.charTwo_coeff
#print axioms VOA.DeligneAudit.D4CharacterTwo.hilb_nat_two
