import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case0
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case1
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case2
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case3
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case4
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case5
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case6
import VOA.DeligneAudit.A2DivisorPairCheckAnti3Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem anti_cert_row3 : ∀ d : Fin 8, (fun c' d' => 6 * antiT 3 d c' d') =
    comb (antiL 3 d) := by
  intro d
  fin_cases d
  · exact anti_cert_pair_3_0
  · exact anti_cert_pair_3_1
  · exact anti_cert_pair_3_2
  · exact anti_cert_pair_3_3
  · exact anti_cert_pair_3_4
  · exact anti_cert_pair_3_5
  · exact anti_cert_pair_3_6
  · exact anti_cert_pair_3_7

end VOA.DeligneAudit.A2.PairCert
