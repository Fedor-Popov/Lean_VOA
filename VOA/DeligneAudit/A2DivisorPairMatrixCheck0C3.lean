import VOA.DeligneAudit.A2CarrierChain
import VOA.DeligneAudit.A2DivisorPairData

namespace VOA.DeligneAudit.A2.PairCert

set_option maxHeartbeats 20000 in
-- Bound the small fixed-row normalization check.
theorem matrix_check_0_3 (d : Fin 8) :
    fullMatrix none (3, d) = (qZ none 3 d : ℂ) := by
  fin_cases d <;> simp [fullMatrix, casimirMatrix, entryMatrix, qZ]

end VOA.DeligneAudit.A2.PairCert
