import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_7 :
    (∀ e : Fin 78, fZ brK 73 45 e = if e = 75 then -1 else 0) ∧
    (∀ e : Fin 78, fZ brK 73 75 e = 0) ∧ (∀ e : Fin 78, fZ brK 45 75 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
