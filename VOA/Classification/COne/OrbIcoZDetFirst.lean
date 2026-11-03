import VOA.Classification.COne.OrbIcoZTermFirst3

/-! Exact determinant factorization assembled from bounded cofactor checks. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option linter.style.longLine false
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco

def detSumFirst : PL := paddL detTermFirst0 (paddL detTermFirst1 (paddL detTermFirst2 detTermFirst3))

set_option maxHeartbeats 8000000 in
-- Four cached terms and a degree-nine/ten factor product.
theorem matrixFirst_det_check :
    ptrim (paddL detSumFirst
      (pscaleL (-1) (pscaleL detScalarFirst (pmulL icoCandidateList icoExtra9)))) = [] := by
  decide +kernel

theorem matrixFirst_det_sum :
    Matrix.det (fun i j => zp (matrixFirst i j)) = zp detSumFirst := by
  rw [det_fin_four_formula]
  simp only [detSumFirst, zp_paddL, detTermFirst0_sound, detTermFirst1_sound, detTermFirst2_sound, detTermFirst3_sound,
    commonMinor0_sound, commonMinor1_sound, commonMinor2_sound, commonMinor3_sound, Matrix.det_fin_three]
  simp [matrixFirst, commonMinorMatrix0, commonMinorMatrix1, commonMinorMatrix2, commonMinorMatrix3,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem matrixFirst_det_factorization :
    Matrix.det (fun i j => zp (matrixFirst i j)) =
      Polynomial.C (detScalarFirst : ℂ) * zp icoCandidateList * zp icoExtra9 := by
  rw [matrixFirst_det_sum]
  have hh := zp_eq_of_trim matrixFirst_det_check
  simpa only [zp_pscaleL, zp_pmulL, mul_assoc] using hh

theorem detScalarFirst_nonzero : detScalarFirst ≠ 0 := by
  decide +kernel

end VOA.Classification.COne.OrbIcoZ
