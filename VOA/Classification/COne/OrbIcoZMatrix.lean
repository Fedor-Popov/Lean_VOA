import VOA.Classification.COne.OrbIcoZMatrixRow9
import VOA.Classification.COne.OrbIcoZDeterminant
import VOA.Classification.COne.OrbIcoZPositiveRoots

/-! Shared exact minor machinery for bounded determinant certificates. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco

def det3PL (m : Fin 3 → Fin 3 → PL) : PL :=
  paddL (pmulL (m 0 0) (pmulL (m 1 1) (m 2 2))) (paddL (pscaleL (-1) (pmulL (m 0 0) (pmulL (m 1 2) (m 2 1)))) (paddL (pscaleL (-1) (pmulL (m 0 1) (pmulL (m 1 0) (m 2 2)))) (paddL (pmulL (m 0 1) (pmulL (m 1 2) (m 2 0))) (paddL (pmulL (m 0 2) (pmulL (m 1 0) (m 2 1))) (paddL (pscaleL (-1) (pmulL (m 0 2) (pmulL (m 1 1) (m 2 0)))) [])))))

theorem zp_det3PL (m : Fin 3 → Fin 3 → PL) :
    zp (det3PL m) = Matrix.det (fun i j => zp (m i j)) := by
  rw [Matrix.det_fin_three]
  simp only [det3PL, zp_paddL, zp_pmulL, zp_pscaleL, zp]
  simp only [Rat.cast_neg, Rat.cast_one, Polynomial.C_neg, Polynomial.C_1]
  ring

def matrixFirst : Fin 4 → Fin 4 → PL :=
  ![![matrixEntry1_0, matrixEntry1_1, matrixEntry1_2, matrixEntry1_3],
    ![matrixEntry3_0, matrixEntry3_1, matrixEntry3_2, matrixEntry3_3],
    ![matrixEntry5_0, matrixEntry5_1, matrixEntry5_2, matrixEntry5_3],
    ![matrixEntry7_0, matrixEntry7_1, matrixEntry7_2, matrixEntry7_3]]

def detScalarFirst : ℚ := mkRat (-13993841142819016221852181133385674348597756880506996825039259050490978252158164684193929381254895892840627744149623815995262995704447381744657363470461427492883105434060326572861909312588031241279097101149969146700378139408556202146421205730207107309875646653478055164553122776350720000000000000000000000000000000000000000) 1

def matrixSecond : Fin 4 → Fin 4 → PL :=
  ![![matrixEntry1_0, matrixEntry1_1, matrixEntry1_2, matrixEntry1_3],
    ![matrixEntry3_0, matrixEntry3_1, matrixEntry3_2, matrixEntry3_3],
    ![matrixEntry5_0, matrixEntry5_1, matrixEntry5_2, matrixEntry5_3],
    ![matrixEntry9_0, matrixEntry9_1, matrixEntry9_2, matrixEntry9_3]]

def detScalarSecond : ℚ := mkRat (-555133764092846914447119950254675954891935911727524286674780034699289046714406484560457201946418587969950970426832805105949846683045100987254469448857752477518209517942566817379526335442460102733050727152454236192919106151882476653830340156286598139875180417318782945563571650560000000000000000000000000000000000000000) 1

def commonMinorMatrix0 : Fin 3 → Fin 3 → PL :=
  ![![matrixEntry1_1, matrixEntry1_2, matrixEntry1_3],
    ![matrixEntry3_1, matrixEntry3_2, matrixEntry3_3],
    ![matrixEntry5_1, matrixEntry5_2, matrixEntry5_3]]

def commonMinorMatrix1 : Fin 3 → Fin 3 → PL :=
  ![![matrixEntry1_0, matrixEntry1_2, matrixEntry1_3],
    ![matrixEntry3_0, matrixEntry3_2, matrixEntry3_3],
    ![matrixEntry5_0, matrixEntry5_2, matrixEntry5_3]]

def commonMinorMatrix2 : Fin 3 → Fin 3 → PL :=
  ![![matrixEntry1_0, matrixEntry1_1, matrixEntry1_3],
    ![matrixEntry3_0, matrixEntry3_1, matrixEntry3_3],
    ![matrixEntry5_0, matrixEntry5_1, matrixEntry5_3]]

def commonMinorMatrix3 : Fin 3 → Fin 3 → PL :=
  ![![matrixEntry1_0, matrixEntry1_1, matrixEntry1_2],
    ![matrixEntry3_0, matrixEntry3_1, matrixEntry3_2],
    ![matrixEntry5_0, matrixEntry5_1, matrixEntry5_2]]

end VOA.Classification.COne.OrbIcoZ
