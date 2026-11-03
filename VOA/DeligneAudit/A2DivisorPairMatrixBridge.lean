import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck0C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck1C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck2C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck3C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck4C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck5C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck6C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck7C7
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C0
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C1
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C2
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C3
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C4
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C5
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C6
import VOA.DeligneAudit.A2DivisorPairMatrixCheck8C7

namespace VOA.DeligneAudit.A2.PairCert

theorem matrix_eq_qZ_checked (r : Option (Fin 8)) (c d : Fin 8) :
    fullMatrix r (c, d) = (qZ r c d : ℂ) := by
  cases r with
  | none =>
    fin_cases c
    · exact matrix_check_0_0 d
    · exact matrix_check_0_1 d
    · exact matrix_check_0_2 d
    · exact matrix_check_0_3 d
    · exact matrix_check_0_4 d
    · exact matrix_check_0_5 d
    · exact matrix_check_0_6 d
    · exact matrix_check_0_7 d
  | some r =>
    fin_cases r
    · fin_cases c
      · exact matrix_check_1_0 d
      · exact matrix_check_1_1 d
      · exact matrix_check_1_2 d
      · exact matrix_check_1_3 d
      · exact matrix_check_1_4 d
      · exact matrix_check_1_5 d
      · exact matrix_check_1_6 d
      · exact matrix_check_1_7 d
    · fin_cases c
      · exact matrix_check_2_0 d
      · exact matrix_check_2_1 d
      · exact matrix_check_2_2 d
      · exact matrix_check_2_3 d
      · exact matrix_check_2_4 d
      · exact matrix_check_2_5 d
      · exact matrix_check_2_6 d
      · exact matrix_check_2_7 d
    · fin_cases c
      · exact matrix_check_3_0 d
      · exact matrix_check_3_1 d
      · exact matrix_check_3_2 d
      · exact matrix_check_3_3 d
      · exact matrix_check_3_4 d
      · exact matrix_check_3_5 d
      · exact matrix_check_3_6 d
      · exact matrix_check_3_7 d
    · fin_cases c
      · exact matrix_check_4_0 d
      · exact matrix_check_4_1 d
      · exact matrix_check_4_2 d
      · exact matrix_check_4_3 d
      · exact matrix_check_4_4 d
      · exact matrix_check_4_5 d
      · exact matrix_check_4_6 d
      · exact matrix_check_4_7 d
    · fin_cases c
      · exact matrix_check_5_0 d
      · exact matrix_check_5_1 d
      · exact matrix_check_5_2 d
      · exact matrix_check_5_3 d
      · exact matrix_check_5_4 d
      · exact matrix_check_5_5 d
      · exact matrix_check_5_6 d
      · exact matrix_check_5_7 d
    · fin_cases c
      · exact matrix_check_6_0 d
      · exact matrix_check_6_1 d
      · exact matrix_check_6_2 d
      · exact matrix_check_6_3 d
      · exact matrix_check_6_4 d
      · exact matrix_check_6_5 d
      · exact matrix_check_6_6 d
      · exact matrix_check_6_7 d
    · fin_cases c
      · exact matrix_check_7_0 d
      · exact matrix_check_7_1 d
      · exact matrix_check_7_2 d
      · exact matrix_check_7_3 d
      · exact matrix_check_7_4 d
      · exact matrix_check_7_5 d
      · exact matrix_check_7_6 d
      · exact matrix_check_7_7 d
    · fin_cases c
      · exact matrix_check_8_0 d
      · exact matrix_check_8_1 d
      · exact matrix_check_8_2 d
      · exact matrix_check_8_3 d
      · exact matrix_check_8_4 d
      · exact matrix_check_8_5 d
      · exact matrix_check_8_6 d
      · exact matrix_check_8_7 d

end VOA.DeligneAudit.A2.PairCert
