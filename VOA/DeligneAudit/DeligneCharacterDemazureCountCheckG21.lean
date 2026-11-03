import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.D4FusionRealizationSmallCharacter
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedG2

/-! Small reflection checks on already certified one-site characters. -/
namespace VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks
open VOA.DeligneAudit.DeligneCharacter

theorem g2_fin1 :
    sameChar (mapW (reflFin cartanG2 1) exceptionalG2State6) exceptionalG2State6 = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks
