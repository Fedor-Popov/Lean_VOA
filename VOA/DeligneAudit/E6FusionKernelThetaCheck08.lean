import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_8 :
    (∀ e : Fin 78, fZ brK 75 44 e = if e = 76 then 1 else 0) ∧
    (∀ e : Fin 78, fZ brK 75 76 e = 0) ∧ (∀ e : Fin 78, fZ brK 44 76 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
