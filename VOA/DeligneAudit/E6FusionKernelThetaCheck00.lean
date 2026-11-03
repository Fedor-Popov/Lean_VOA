import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_0 :
    (∀ e : Fin 78, fZ brK 46 44 e = if e = 51 then -1 else 0) ∧
    (∀ e : Fin 78, fZ brK 46 51 e = 0) ∧ (∀ e : Fin 78, fZ brK 44 51 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
