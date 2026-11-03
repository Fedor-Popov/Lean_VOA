import VOA.DeligneAudit.D4FusionContactAllMNormalCoefficientsCore
import VOA.DeligneAudit.D4FusionContactAllMNormalCubic
import VOA.DeligneAudit.D4FusionContactAllMWheelsTable

/-! Exact identification of the opposite cubic source word.
The factor216 is cancelled over the complex field. -/

namespace VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

open AllMWheels (direction sourceColor targetColor actionCoeff action_rows cancel_nat_factor)

noncomputable section

theorem action_mode (m r : ℕ) (j : Fin 12) :
    g0Deriv m (direction j) 0 (modeX m (sourceColor j) r) =
      (actionCoeff j : ℂ) • modeX m (targetColor j) r := by
  by_cases hr : r < m
  · rw [modeX, dif_pos hr]
    simp only [g0Deriv, MvPolynomial.mkDerivation_X, g0Image, zero_add,
      action_rows, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [modeX, dif_neg hr, map_zero, smul_zero]

theorem oppositeCubic_eq (m s : ℕ) :
    oppositeCubic m s = 216 * cubeCoeff (modeX m 7) s := by
  have h0 (r : ℕ) : g0Deriv m 7 0 (modeX m 0 r) = modeX m 1 r := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 0
  have h3 (r : ℕ) : g0Deriv m 8 0 (modeX m 1 r) = -modeX m 4 r := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 3
  have h4 (r : ℕ) : g0Deriv m 7 0 (modeX m 1 r) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 4
  have h5 (r : ℕ) : g0Deriv m 8 0 (modeX m 4 r) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 5
  have h6 (r : ℕ) : g0Deriv m 9 0 (modeX m 4 r) = modeX m 7 r := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 6
  have h7 (r : ℕ) : g0Deriv m 9 0 (modeX m 7 r) = 0 := by
    simpa [direction, sourceColor, targetColor, actionCoeff] using action_mode m r 7
  have hfirst := third_deriv_cubeCoeff_nsmul (g0Deriv m 7 0) (modeX m 0) (modeX m 1) h0 h4 s
  have hsecond : g0Deriv m 8 0 (g0Deriv m 8 0 (g0Deriv m 8 0
      (cubeCoeff (modeX m 1) s))) = (6 : ℕ) • (-cubeCoeff (modeX m 4) s) := by
    have hh := third_deriv_cubeCoeff_nsmul (g0Deriv m 8 0) (modeX m 1)
      (fun r => -modeX m 4 r) h3 (fun r => by rw [map_neg, h5, neg_zero]) s
    simpa only [cubeCoeff_neg] using hh
  have hthird := third_deriv_cubeCoeff_nsmul (g0Deriv m 9 0) (modeX m 4) (modeX m 7) h6 h7 s
  change -(g0Deriv m 9 0 (g0Deriv m 9 0 (g0Deriv m 9 0
    (g0Deriv m 8 0 (g0Deriv m 8 0 (g0Deriv m 8 0
      (g0Deriv m 7 0 (g0Deriv m 7 0 (g0Deriv m 7 0 (cubeCoeff (modeX m 0) s)))))))))) = _
  rw [hfirst]
  simp only [map_nsmul]
  rw [hsecond]
  simp only [map_neg, map_nsmul]
  rw [hthird]
  simp only [nsmul_eq_mul]
  ring

theorem opposite_cubeCoeff_mem (m s : ℕ) (hs : m < 3 + s) :
    cubeCoeff (modeX m 7) s ∈ AllM.candidateIdeal m := by
  have h := oppositeCubic_mem m s hs
  rw [oppositeCubic_eq] at h
  exact cancel_nat_factor (AllM.candidateIdeal m) 216 (by decide) h

def directBackRow (m s t : ℕ) : Poly m :=
  modeX m 4 t * g0Deriv m 5 0 (g0Deriv m 4 0 (cubeCoeff (modeX m 7) s)) -
    modeX m 3 t * g0Deriv m 6 0 (cubeCoeff (modeX m 7) s)

theorem backRow_eq (m s t : ℕ) : backRow m s t = 216 * directBackRow m s t := by
  have he : oppositeCubic m s = (216 : ℕ) • cubeCoeff (modeX m 7) s := by
    simpa only [nsmul_eq_mul] using oppositeCubic_eq m s
  simp only [backRow, directBackRow, he, map_nsmul]
  simp only [nsmul_eq_mul]
  ring

theorem directBackRow_mem (m s t : ℕ) (hs : m < 3 + s) :
    directBackRow m s t ∈ AllM.candidateIdeal m := by
  exact (AllM.candidateIdeal m).sub_mem
    ((AllM.candidateIdeal m).mul_mem_left _
      (g0_closed m 0 5 (g0_closed m 0 4 (opposite_cubeCoeff_mem m s hs))))
    ((AllM.candidateIdeal m).mul_mem_left _ (g0_closed m 0 6 (opposite_cubeCoeff_mem m s hs)))

theorem normal_direct_rows_mem {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    frontRow m (2 * m - 4) t ∈ AllM.candidateIdeal m ∧
      middleRow m (2 * m - 4) t ∈ AllM.candidateIdeal m ∧
      directBackRow m (2 * m - 4) t ∈ AllM.candidateIdeal m := by
  have hs : m < 3 + (2 * m - 4) := by omega
  exact ⟨frontRow_mem m _ t hs, middleRow_mem m _ t hs, directBackRow_mem m _ t hs⟩

end
end VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal

#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.oppositeCubic_eq
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.directBackRow_mem
#print axioms VOA.DeligneAudit.D4FusionContact.Polynomial.AllMNormal.normal_direct_rows_mem
