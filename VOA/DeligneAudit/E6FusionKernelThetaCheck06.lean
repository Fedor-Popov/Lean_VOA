import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_6 :
    (∀ e : Fin 78, fZ brK 70 47 e = if e = 73 then -1 else 0) ∧
    (∀ e : Fin 78, fZ brK 70 73 e = 0) ∧ (∀ e : Fin 78, fZ brK 47 73 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
