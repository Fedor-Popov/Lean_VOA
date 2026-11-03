import VOA.DeligneAudit.A2CarrierChain
import VOA.DeligneAudit.A2DivisorPairData

namespace VOA.DeligneAudit.A2.PairCert

set_option maxHeartbeats 20000 in
-- Bound the small fixed-row normalization check.
theorem matrix_check_2_4 (d : Fin 8) :
    fullMatrix (some 1) (4, d) = (qZ (some 1) 4 d : ℂ) := by
  fin_cases d <;> simp [fullMatrix, relationMatrix, relationEntries, entryMatrix, qZ]

end VOA.DeligneAudit.A2.PairCert
