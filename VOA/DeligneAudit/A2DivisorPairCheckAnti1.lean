import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti1Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row1 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 1 d c' d') =
    comb (antiL 1 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_1_0
  · exact anti_cert_pair_1_1
  · exact anti_cert_pair_1_2
  · exact anti_cert_pair_1_3
  · exact anti_cert_pair_1_4
  · exact anti_cert_pair_1_5
  · exact anti_cert_pair_1_6
  · exact anti_cert_pair_1_7

end VOA.DeligneAudit.A2.PairCert
