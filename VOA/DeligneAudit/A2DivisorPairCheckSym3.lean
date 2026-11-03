import VOA.DeligneAudit.A2DivisorPairCheckSym3Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym3Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row3 : ∀ d : Fin 8, (fun c' d' => 72 * symT 3 d c' d') =
    fun c' d' => comb (symL 3 d) c' d' + ∑ r, phiZ r (symT 3 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_3_0
  · exact sym_cert_pair_3_1
  · exact sym_cert_pair_3_2
  · exact sym_cert_pair_3_3
  · exact sym_cert_pair_3_4
  · exact sym_cert_pair_3_5
  · exact sym_cert_pair_3_6
  · exact sym_cert_pair_3_7

end VOA.DeligneAudit.A2.PairCert
