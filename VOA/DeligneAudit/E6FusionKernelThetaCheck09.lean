import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_9 :
    (∀ e : Fin 78, fZ brK 76 46 e = if e = 77 then 1 else 0) ∧
    (∀ e : Fin 78, fZ brK 76 77 e = 0) ∧ (∀ e : Fin 78, fZ brK 46 77 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
