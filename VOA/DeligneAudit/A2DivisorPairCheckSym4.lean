import VOA.DeligneAudit.A2DivisorPairCheckSym4Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym4Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row4 : ∀ d : Fin 8, (fun c' d' => 72 * symT 4 d c' d') =
    fun c' d' => comb (symL 4 d) c' d' + ∑ r, phiZ r (symT 4 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_4_0
  · exact sym_cert_pair_4_1
  · exact sym_cert_pair_4_2
  · exact sym_cert_pair_4_3
  · exact sym_cert_pair_4_4
  · exact sym_cert_pair_4_5
  · exact sym_cert_pair_4_6
  · exact sym_cert_pair_4_7

end VOA.DeligneAudit.A2.PairCert
