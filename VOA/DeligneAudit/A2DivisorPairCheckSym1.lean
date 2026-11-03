import VOA.DeligneAudit.A2DivisorPairCheckSym1Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym1Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row1 : ∀ d : Fin 8, (fun c' d' => 72 * symT 1 d c' d') =
    fun c' d' => comb (symL 1 d) c' d' + ∑ r, phiZ r (symT 1 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_1_0
  · exact sym_cert_pair_1_1
  · exact sym_cert_pair_1_2
  · exact sym_cert_pair_1_3
  · exact sym_cert_pair_1_4
  · exact sym_cert_pair_1_5
  · exact sym_cert_pair_1_6
  · exact sym_cert_pair_1_7

end VOA.DeligneAudit.A2.PairCert
