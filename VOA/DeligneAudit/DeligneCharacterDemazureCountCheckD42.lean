import VOA.DeligneAudit.DeligneCharacterDemazureCount
import VOA.DeligneAudit.D4FusionRealizationSmallCharacter
import VOA.DeligneAudit.DeligneCharacterExceptionalCertifiedG2

/-! Small reflection checks on already certified one-site characters. -/
namespace VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks
open VOA.DeligneAudit.DeligneCharacter

theorem d4_fin2 :
    sameChar (mapW (reflFin
      [[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]] 2)
      D4Small.charOne) D4Small.charOne = true := by
  decide +kernel

end VOA.DeligneAudit.DeligneCharacter.DemCount.SmallChecks
