import VOA.DeligneAudit.D4FusionContactPolynomialGrDimensionTransfer
import VOA.DeligneAudit.D4FusionContactPolynomialCutoff
import VOA.DeligneAudit.DeligneFusionUnivGSectorRelations

/-! # Actual homogeneous universal source for the D4 m=2 bound

These source identities use only the defining local Weyl/fusion relations.
No finiteness or fusion total-dimension input enters the universal source.
-/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem m2_universal_highest :
    HighestRel (univRepG contactF (lwSpec D4sector 2))
      (wUG contactF (lwSpec D4sector 2)) 2 :=
  highestRel_of_localWeyl (univ_localWeylRelG D4sector 2)

end
end VOA.DeligneAudit.D4FusionContact.Polynomial

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.m2_universal_highest
