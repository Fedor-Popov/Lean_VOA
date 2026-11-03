import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_3 :
    (∀ e : Fin 78, fZ brK 59 45 e = if e = 63 then -1 else 0) ∧
    (∀ e : Fin 78, fZ brK 59 63 e = 0) ∧ (∀ e : Fin 78, fZ brK 45 63 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
