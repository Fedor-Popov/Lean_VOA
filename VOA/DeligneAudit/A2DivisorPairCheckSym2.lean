import VOA.DeligneAudit.A2DivisorPairCheckSym2Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym2Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row2 : ∀ d : Fin 8, (fun c' d' => 72 * symT 2 d c' d') =
    fun c' d' => comb (symL 2 d) c' d' + ∑ r, phiZ r (symT 2 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_2_0
  · exact sym_cert_pair_2_1
  · exact sym_cert_pair_2_2
  · exact sym_cert_pair_2_3
  · exact sym_cert_pair_2_4
  · exact sym_cert_pair_2_5
  · exact sym_cert_pair_2_6
  · exact sym_cert_pair_2_7

end VOA.DeligneAudit.A2.PairCert
