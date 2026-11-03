import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_5 :
    (∀ e : Fin 78, fZ brK 67 43 e = if e = 70 then 1 else 0) ∧
    (∀ e : Fin 78, fZ brK 67 70 e = 0) ∧ (∀ e : Fin 78, fZ brK 43 70 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
