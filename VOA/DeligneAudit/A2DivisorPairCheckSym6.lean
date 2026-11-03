import VOA.DeligneAudit.A2DivisorPairCheckSym6Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym6Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row6 : ∀ d : Fin 8, (fun c' d' => 72 * symT 6 d c' d') =
    fun c' d' => comb (symL 6 d) c' d' + ∑ r, phiZ r (symT 6 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_6_0
  · exact sym_cert_pair_6_1
  · exact sym_cert_pair_6_2
  · exact sym_cert_pair_6_3
  · exact sym_cert_pair_6_4
  · exact sym_cert_pair_6_5
  · exact sym_cert_pair_6_6
  · exact sym_cert_pair_6_7

end VOA.DeligneAudit.A2.PairCert
