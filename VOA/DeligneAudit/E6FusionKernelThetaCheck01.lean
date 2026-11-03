import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_1 :
    (∀ e : Fin 78, fZ brK 51 43 e = if e = 55 then 1 else 0) ∧
    (∀ e : Fin 78, fZ brK 51 55 e = 0) ∧ (∀ e : Fin 78, fZ brK 43 55 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
