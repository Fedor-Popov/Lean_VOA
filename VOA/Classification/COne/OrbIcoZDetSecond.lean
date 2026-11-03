import VOA.Classification.COne.OrbIcoZTermSecond3

/-! Exact determinant factorization assembled from bounded cofactor checks. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco

def detSumSecond : PL := paddL detTermSecond0 (paddL detTermSecond1 (paddL detTermSecond2 detTermSecond3))

set_option maxHeartbeats 8000000 in
-- Four cached terms and a degree-nine/ten factor product.
theorem matrixSecond_det_check :
    ptrim (paddL detSumSecond
      (pscaleL (-1) (pscaleL detScalarSecond (pmulL icoCandidateList icoExtra10)))) = [] := by
  decide +kernel

theorem matrixSecond_det_sum :
    Matrix.det (fun i j => zp (matrixSecond i j)) = zp detSumSecond := by
  rw [det_fin_four_formula]
  simp only [detSumSecond, zp_paddL, detTermSecond0_sound, detTermSecond1_sound, detTermSecond2_sound, detTermSecond3_sound,
    commonMinor0_sound, commonMinor1_sound, commonMinor2_sound, commonMinor3_sound, Matrix.det_fin_three]
  simp [matrixSecond, commonMinorMatrix0, commonMinorMatrix1, commonMinorMatrix2, commonMinorMatrix3,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem matrixSecond_det_factorization :
    Matrix.det (fun i j => zp (matrixSecond i j)) =
      Polynomial.C (detScalarSecond : ℂ) * zp icoCandidateList * zp icoExtra10 := by
  rw [matrixSecond_det_sum]
  have hh := zp_eq_of_trim matrixSecond_det_check
  simpa only [zp_pscaleL, zp_pmulL, mul_assoc] using hh

theorem detScalarSecond_nonzero : detScalarSecond ≠ 0 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoZ
