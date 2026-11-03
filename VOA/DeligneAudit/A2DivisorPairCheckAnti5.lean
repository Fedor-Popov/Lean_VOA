import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti5Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row5 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 5 d c' d') =
    comb (antiL 5 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_5_0
  · exact anti_cert_pair_5_1
  · exact anti_cert_pair_5_2
  · exact anti_cert_pair_5_3
  · exact anti_cert_pair_5_4
  · exact anti_cert_pair_5_5
  · exact anti_cert_pair_5_6
  · exact anti_cert_pair_5_7

end VOA.DeligneAudit.A2.PairCert
