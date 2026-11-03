import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti0Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row0 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 0 d c' d') =
    comb (antiL 0 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_0_0
  · exact anti_cert_pair_0_1
  · exact anti_cert_pair_0_2
  · exact anti_cert_pair_0_3
  · exact anti_cert_pair_0_4
  · exact anti_cert_pair_0_5
  · exact anti_cert_pair_0_6
  · exact anti_cert_pair_0_7

end VOA.DeligneAudit.A2.PairCert
