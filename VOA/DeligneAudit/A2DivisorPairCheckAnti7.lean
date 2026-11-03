import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti7Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row7 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 7 d c' d') =
    comb (antiL 7 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_7_0
  · exact anti_cert_pair_7_1
  · exact anti_cert_pair_7_2
  · exact anti_cert_pair_7_3
  · exact anti_cert_pair_7_4
  · exact anti_cert_pair_7_5
  · exact anti_cert_pair_7_6
  · exact anti_cert_pair_7_7

end VOA.DeligneAudit.A2.PairCert
