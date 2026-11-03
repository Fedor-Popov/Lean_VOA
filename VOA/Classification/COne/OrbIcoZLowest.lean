import VOA.Classification.COne.OrbIcoZDetSecond
import VOA.Classification.COne.OrbIcoZBottomMatrix
import VOA.Classification.COne.OrbPosLowest

/-! Actual nonzero bottom spaces force the candidate determinant root relation. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 10000
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA OrbOdd OrbZhu Polynomial OrbIco OrbB5 OrbPos

theorem scalarMatrixFirst_det (h : ℂ) :
    (scalarMatrix matrixFirst h).det =
      (detScalarFirst : ℂ) * (zp icoCandidateList).eval h * (zp icoExtra9).eval h := by
  unfold scalarMatrix
  rw [← (Polynomial.evalRingHom h).map_det, matrixFirst_det_factorization]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]

theorem scalarMatrixSecond_det (h : ℂ) :
    (scalarMatrix matrixSecond h).det =
      (detScalarSecond : ℂ) * (zp icoCandidateList).eval h * (zp icoExtra10).eval h := by
  unfold scalarMatrix
  rw [← (Polynomial.evalRingHom h).map_det, matrixSecond_det_factorization]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C]

/-- The root is forced by actual null/circle equations on an actual nonzero bottom. -/
theorem candidate_lowest_root {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) {h : ℂ} (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    (zp icoCandidateList).eval h = 0 := by
  obtain ⟨f, ht, hf⟩ := exists_topEigenfunctional N hl hne
  have hv : topVector f (0 : Fin 4) ∈ nonZeroDivisors ℂ := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    simpa [topVector] using ht
  have h1 := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (scalarMatrixFirst_kernel h f hf) hv
  have h2 := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    (scalarMatrixSecond_kernel h f hf) hv
  rw [scalarMatrixFirst_det] at h1
  rw [scalarMatrixSecond_det] at h2
  by_contra hp
  have hc1 : (detScalarFirst : ℂ) ≠ 0 := by exact_mod_cast detScalarFirst_nonzero
  have hc2 : (detScalarSecond : ℂ) ≠ 0 := by exact_mod_cast detScalarSecond_nonzero
  have he9 : (zp icoExtra9).eval h = 0 :=
    (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hc1 hp)
  have he10 : (zp icoExtra10).eval h = 0 :=
    (mul_eq_zero.mp h2).resolve_left (mul_ne_zero hc2 hp)
  exact icoExtra_no_common_root h ⟨he9, he10⟩

theorem ico_lowest_zero_or_positive {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) {h : ℂ} (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    h = 0 ∨ 0 < h.re :=
  candidate_root_zero_or_positive (candidate_lowest_root N hl hne)

/-- The actual A5 orbifold is pseudo-unitary without a rationality premise. -/
theorem ico_pseudoUnitary_holds : PseudoUnitary Wi := by
  apply (pseudoUnitary_iff_positiveLowestWeights Wi).mpr
  intro M _ _ N hi hn h hl hne
  rcases ico_lowest_zero_or_positive N hl hne with rfl | hp
  · obtain ⟨e⟩ := ico_vacuum_of_lowest_zero N hi hl hne
    exact (hn.false e).elim
  · exact hp

end VOA.Classification.COne.OrbIcoZ
