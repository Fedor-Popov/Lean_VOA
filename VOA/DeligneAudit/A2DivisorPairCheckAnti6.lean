import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti6Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row6 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 6 d c' d') =
    comb (antiL 6 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_6_0
  · exact anti_cert_pair_6_1
  · exact anti_cert_pair_6_2
  · exact anti_cert_pair_6_3
  · exact anti_cert_pair_6_4
  · exact anti_cert_pair_6_5
  · exact anti_cert_pair_6_6
  · exact anti_cert_pair_6_7

end VOA.DeligneAudit.A2.PairCert
