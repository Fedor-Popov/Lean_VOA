import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti2Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row2 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 2 d c' d') =
    comb (antiL 2 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_2_0
  · exact anti_cert_pair_2_1
  · exact anti_cert_pair_2_2
  · exact anti_cert_pair_2_3
  · exact anti_cert_pair_2_4
  · exact anti_cert_pair_2_5
  · exact anti_cert_pair_2_6
  · exact anti_cert_pair_2_7

end VOA.DeligneAudit.A2.PairCert
