import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCycle
import VOA.DeligneAudit.D4FusionRealizationCharacterTwoTransport

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Alias transport never unfolds the closed character algorithm. -/
private theorem first_eq : demazureChar cartan theta word 1 = state00 :=
  character_transport
    [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]] cartan
    [1, 2, 1, 1] theta [1, 0, 2, 1, 3, 1, 2, 0, 1] word 1 D4Small.charOne state00
    rfl rfl rfl (by decide +kernel) D4Small.charOne_eq

theorem char_two_eq : demazureChar cartan theta word 2 = state10 :=
  exceptional_character_two cartan theta word state00 state10
    (first_step_of_char cartan theta word state00 first_eq) cycle_two

end VOA.DeligneAudit.D4CharacterTwo

#print axioms VOA.DeligneAudit.D4CharacterTwo.char_two_eq
