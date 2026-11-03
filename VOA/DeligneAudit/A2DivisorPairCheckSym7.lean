import VOA.DeligneAudit.A2DivisorPairCheckSym7Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym7Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row7 : ∀ d : Fin 8, (fun c' d' => 72 * symT 7 d c' d') =
    fun c' d' => comb (symL 7 d) c' d' + ∑ r, phiZ r (symT 7 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_7_0
  · exact sym_cert_pair_7_1
  · exact sym_cert_pair_7_2
  · exact sym_cert_pair_7_3
  · exact sym_cert_pair_7_4
  · exact sym_cert_pair_7_5
  · exact sym_cert_pair_7_6
  · exact sym_cert_pair_7_7

end VOA.DeligneAudit.A2.PairCert
