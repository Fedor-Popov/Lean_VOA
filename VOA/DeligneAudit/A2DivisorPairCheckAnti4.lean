import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti4Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row4 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 4 d c' d') =
    comb (antiL 4 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_4_0
  · exact anti_cert_pair_4_1
  · exact anti_cert_pair_4_2
  · exact anti_cert_pair_4_3
  · exact anti_cert_pair_4_4
  · exact anti_cert_pair_4_5
  · exact anti_cert_pair_4_6
  · exact anti_cert_pair_4_7

end VOA.DeligneAudit.A2.PairCert
