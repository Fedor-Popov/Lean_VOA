import VOA.DeligneAudit.A2DivisorPairCheckSym0Case0
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case1
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case2
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case3
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case4
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case5
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case6
import VOA.DeligneAudit.A2DivisorPairCheckSym0Case7

namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert_row0 : ∀ d : Fin 8, (fun c' d' => 72 * symT 0 d c' d') =
    fun c' d' => comb (symL 0 d) c' d' + ∑ r, phiZ r (symT 0 d) * UZ r c' d' := by
  intro d
  fin_cases d
  · exact sym_cert_pair_0_0
  · exact sym_cert_pair_0_1
  · exact sym_cert_pair_0_2
  · exact sym_cert_pair_0_3
  · exact sym_cert_pair_0_4
  · exact sym_cert_pair_0_5
  · exact sym_cert_pair_0_6
  · exact sym_cert_pair_0_7

end VOA.DeligneAudit.A2.PairCert
