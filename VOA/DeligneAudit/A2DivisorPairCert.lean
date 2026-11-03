import VOA.DeligneAudit.A2DivisorPairTreeCheck00
import VOA.DeligneAudit.A2DivisorPairTreeCheck01
import VOA.DeligneAudit.A2DivisorPairTreeCheck02
import VOA.DeligneAudit.A2DivisorPairTreeCheck03
import VOA.DeligneAudit.A2DivisorPairTreeCheck04
import VOA.DeligneAudit.A2DivisorPairTreeCheck05
import VOA.DeligneAudit.A2DivisorPairTreeCheck06
import VOA.DeligneAudit.A2DivisorPairTreeCheck07
import VOA.DeligneAudit.A2DivisorPairTreeCheck08
import VOA.DeligneAudit.A2DivisorPairTreeCheck09
import VOA.DeligneAudit.A2DivisorPairTreeCheck10
import VOA.DeligneAudit.A2DivisorPairTreeCheck11
import VOA.DeligneAudit.A2DivisorPairTreeCheck12
import VOA.DeligneAudit.A2DivisorPairTreeCheck13
import VOA.DeligneAudit.A2DivisorPairTreeCheck14
import VOA.DeligneAudit.A2DivisorPairTreeCheck15
import VOA.DeligneAudit.A2DivisorPairData
import VOA.DeligneAudit.A2DivisorPairCheckSym0
import VOA.DeligneAudit.A2DivisorPairCheckSym1
import VOA.DeligneAudit.A2DivisorPairCheckSym2
import VOA.DeligneAudit.A2DivisorPairCheckSym3
import VOA.DeligneAudit.A2DivisorPairCheckSym4
import VOA.DeligneAudit.A2DivisorPairCheckSym5
import VOA.DeligneAudit.A2DivisorPairCheckSym6
import VOA.DeligneAudit.A2DivisorPairCheckSym7
import VOA.DeligneAudit.A2DivisorPairCheckAnti0
import VOA.DeligneAudit.A2DivisorPairCheckAnti1
import VOA.DeligneAudit.A2DivisorPairCheckAnti2
import VOA.DeligneAudit.A2DivisorPairCheckAnti3
import VOA.DeligneAudit.A2DivisorPairCheckAnti4
import VOA.DeligneAudit.A2DivisorPairCheckAnti5
import VOA.DeligneAudit.A2DivisorPairCheckAnti6
import VOA.DeligneAudit.A2DivisorPairCheckAnti7

/-! Two-slot certificates assembled from smaller kernel checks. The integer data and
original theorem statements are unchanged. -/
namespace VOA.DeligneAudit.A2.PairCert

theorem sym_cert : ∀ c d : Fin 8, (fun c' d' => 72 * symT c d c' d') =
    fun c' d' => comb (symL c d) c' d' + ∑ r, phiZ r (symT c d) * UZ r c' d' := by
  intro c
  fin_cases c
  · exact sym_cert_row0
  · exact sym_cert_row1
  · exact sym_cert_row2
  · exact sym_cert_row3
  · exact sym_cert_row4
  · exact sym_cert_row5
  · exact sym_cert_row6
  · exact sym_cert_row7

theorem anti_cert : ∀ c d : Fin 8, (fun c' d' => 6 * antiT c d c' d') = comb (antiL c d) := by
  intro c
  fin_cases c
  · exact anti_cert_row0
  · exact anti_cert_row1
  · exact anti_cert_row2
  · exact anti_cert_row3
  · exact anti_cert_row4
  · exact anti_cert_row5
  · exact anti_cert_row6
  · exact anti_cert_row7

theorem symL_lev : ∀ c d : Fin 8, ∀ p ∈ symL c d, lev p.1 = 0 := by decide +kernel

theorem antiL_lev : ∀ c d : Fin 8, ∀ p ∈ antiL c d, lev p.1 ≤ 1 := by decide +kernel

theorem UL_lev : ∀ r : Option (Fin 8), ∀ p ∈ UL r, lev p.1 ≤ 2 := by decide +kernel

end VOA.DeligneAudit.A2.PairCert

#print axioms VOA.DeligneAudit.A2.PairCert.sym_cert
#print axioms VOA.DeligneAudit.A2.PairCert.anti_cert
