import VOA.DeligneAudit.E6FusionKernelThetaData

namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse

theorem e6_chainZ_2 :
    (∀ e : Fin 78, fZ brK 55 42 e = if e = 59 then 1 else 0) ∧
    (∀ e : Fin 78, fZ brK 55 59 e = 0) ∧ (∀ e : Fin 78, fZ brK 42 59 e = 0) := by
  decide +kernel

end VOA.DeligneAudit.UnivG.E6K
