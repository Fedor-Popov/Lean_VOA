import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckD4Zero
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckD40
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckD41
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckD42
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckD43
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckG2Zero
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckG20
import VOA.DeligneAudit.DeligneCharacterDemazureCountCheckG21

/-! Small reflection checks on already certified one-site characters. -/
namespace VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks
open VOA.DeligneAudit.DeligneCharacter

theorem d4_inv :
    invCheck [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]] [1, 2, 1, 1]
    [1, 0, 2, 1, 3, 1, 2, 0, 1] D4Small.charOne = true := by
  simp only [invCheck, List.all_cons, List.all_nil, d4_zero,
    d4_fin0, d4_fin1, d4_fin2, d4_fin3, Bool.true_and]

theorem d4_total : (D4Small.charOne.map (·.2)).sum = 29 := by decide +kernel

theorem g2_inv : invCheck cartanG2 thetaG2 wordG2 exceptionalG2State6 = true := by
  simp only [invCheck, wordG2, List.all_cons, List.all_nil, g2_zero,
    g2_fin0, g2_fin1, Bool.true_and]

theorem g2_total : (exceptionalG2State6.map (·.2)).sum = 15 := by decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks

#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks.d4_inv
#print axioms VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks.g2_inv
