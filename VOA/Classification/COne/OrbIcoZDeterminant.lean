import VOA.Classification.COne.OrbIcoZEigenfunctional
import VOA.Classification.COne.OrbIcoZNormal

/-! A computable four-by-four determinant with its exact polynomial semantics. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco

def det4PL (m : Fin 4 → Fin 4 → PL) : PL :=
  paddL (pmulL (m 0 0) (pmulL (m 1 1) (pmulL (m 2 2) (m 3 3)))) (
    paddL (pscaleL (-1) (pmulL (m 0 0) (pmulL (m 1 1) (pmulL (m 2 3) (m 3 2))))) (
      paddL (pscaleL (-1) (pmulL (m 0 0) (pmulL (m 1 2) (pmulL (m 2 1) (m 3 3))))) (
        paddL (pmulL (m 0 0) (pmulL (m 1 2) (pmulL (m 2 3) (m 3 1)))) (
          paddL (pmulL (m 0 0) (pmulL (m 1 3) (pmulL (m 2 1) (m 3 2)))) (
            paddL (pscaleL (-1) (pmulL (m 0 0) (pmulL (m 1 3) (pmulL (m 2 2) (m 3 1))))) (
              paddL (pscaleL (-1) (pmulL (m 0 1) (pmulL (m 1 0) (pmulL (m 2 2) (m 3 3))))) (
                paddL (pmulL (m 0 1) (pmulL (m 1 0) (pmulL (m 2 3) (m 3 2)))) (
                  paddL (pmulL (m 0 1) (pmulL (m 1 2) (pmulL (m 2 0) (m 3 3)))) (
                    paddL (pscaleL (-1) (pmulL (m 0 1) (pmulL (m 1 2) (pmulL (m 2 3) (m 3 0))))) (
                      paddL (pscaleL (-1) (pmulL (m 0 1) (pmulL (m 1 3) (pmulL (m 2 0) (m 3 2))))) (
                        paddL (pmulL (m 0 1) (pmulL (m 1 3) (pmulL (m 2 2) (m 3 0)))) (
                          paddL (pmulL (m 0 2) (pmulL (m 1 0) (pmulL (m 2 1) (m 3 3)))) (
                            paddL (pscaleL (-1) (pmulL (m 0 2) (pmulL (m 1 0) (pmulL (m 2 3) (m 3 1))))) (
                              paddL (pscaleL (-1) (pmulL (m 0 2) (pmulL (m 1 1) (pmulL (m 2 0) (m 3 3))))) (
                                paddL (pmulL (m 0 2) (pmulL (m 1 1) (pmulL (m 2 3) (m 3 0)))) (
                                  paddL (pmulL (m 0 2) (pmulL (m 1 3) (pmulL (m 2 0) (m 3 1)))) (
                                    paddL (pscaleL (-1) (pmulL (m 0 2) (pmulL (m 1 3) (pmulL (m 2 1) (m 3 0))))) (
                                      paddL (pscaleL (-1) (pmulL (m 0 3) (pmulL (m 1 0) (pmulL (m 2 1) (m 3 2))))) (
                                        paddL (pmulL (m 0 3) (pmulL (m 1 0) (pmulL (m 2 2) (m 3 1)))) (
                                          paddL (pmulL (m 0 3) (pmulL (m 1 1) (pmulL (m 2 0) (m 3 2)))) (
                                            paddL (pscaleL (-1) (pmulL (m 0 3) (pmulL (m 1 1) (pmulL (m 2 2) (m 3 0))))) (
                                              paddL (pscaleL (-1) (pmulL (m 0 3) (pmulL (m 1 2) (pmulL (m 2 0) (m 3 1))))) (
                                                paddL (pmulL (m 0 3) (pmulL (m 1 2) (pmulL (m 2 1) (m 3 0)))) (
                                                  []))))))))))))))))))))))))

theorem det_fin_four_formula {R : Type*} [CommRing R] (m : Matrix (Fin 4) (Fin 4) R) :
    m.det =
      m 0 0 * m 1 1 * m 2 2 * m 3 3
      - m 0 0 * m 1 1 * m 2 3 * m 3 2
      - m 0 0 * m 1 2 * m 2 1 * m 3 3
      + m 0 0 * m 1 2 * m 2 3 * m 3 1
      + m 0 0 * m 1 3 * m 2 1 * m 3 2
      - m 0 0 * m 1 3 * m 2 2 * m 3 1
      - m 0 1 * m 1 0 * m 2 2 * m 3 3
      + m 0 1 * m 1 0 * m 2 3 * m 3 2
      + m 0 1 * m 1 2 * m 2 0 * m 3 3
      - m 0 1 * m 1 2 * m 2 3 * m 3 0
      - m 0 1 * m 1 3 * m 2 0 * m 3 2
      + m 0 1 * m 1 3 * m 2 2 * m 3 0
      + m 0 2 * m 1 0 * m 2 1 * m 3 3
      - m 0 2 * m 1 0 * m 2 3 * m 3 1
      - m 0 2 * m 1 1 * m 2 0 * m 3 3
      + m 0 2 * m 1 1 * m 2 3 * m 3 0
      + m 0 2 * m 1 3 * m 2 0 * m 3 1
      - m 0 2 * m 1 3 * m 2 1 * m 3 0
      - m 0 3 * m 1 0 * m 2 1 * m 3 2
      + m 0 3 * m 1 0 * m 2 2 * m 3 1
      + m 0 3 * m 1 1 * m 2 0 * m 3 2
      - m 0 3 * m 1 1 * m 2 2 * m 3 0
      - m 0 3 * m 1 2 * m 2 0 * m 3 1
      + m 0 3 * m 1 2 * m 2 1 * m 3 0 := by
  let cols : Fin 4 → Fin 3 → Fin 4 :=
    ![![1,2,3], ![0,2,3], ![0,1,3], ![0,1,2]]
  have hc (j : Fin 4) (i : Fin 3) : j.succAbove i = cols j i := by
    fin_cases j <;> fin_cases i <;> rfl
  have hs : (2 : Fin 3).succ = (3 : Fin 4) := by decide
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, hc]
  norm_num [cols, Matrix.cons_val_two, Matrix.cons_val_three, hs]
  ring


theorem zp_det4PL (m : Fin 4 → Fin 4 → PL) :
    zp (det4PL m) = Matrix.det (fun i j => zp (m i j)) := by
  rw [det_fin_four_formula]
  simp only [det4PL, zp_paddL, zp_pmulL, zp_pscaleL, zp]
  simp only [Rat.cast_neg, Rat.cast_one, Polynomial.C_neg, Polynomial.C_1]
  ring

end VOA.Classification.COne.OrbIcoZ
