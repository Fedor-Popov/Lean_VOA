import VOA.Classification.COne.OrbOctaZCFinal

/-! Low-weight vanishing in the zero conformal fiber. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbOdd OrbZhu OrbOctaR OrbC2c OrbSpan OrbOctaZC

abbrev zeroKernel := LinearMap.ker (q24L.comp (mk W))

theorem q24_word {d : ℤ} {y : (orbifold OrbC2b.octa).carrier}
    (hy : y ∈ W.grading d) (hq : q24L (mk W y) = 0) (ks : List ℕ) :
    q24L (mk W (virWord W ks y)) = 0 := by
  induction ks with
  | nil => exact hq
  | cons k ks ih =>
    rw [virWord, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
      mk_L_neg W (virWord_grading W hy ks) (k + 1) (by omega)]
    simp only [map_smul, map_add, q24L_omega, ih, smul_zero, add_zero]

theorem q24_vacWord (ks : List ℕ) (hne : ks ≠ []) :
    q24L (mk W (virWord W ks W.vacuum)) = 0 := by
  induction ks with
  | nil => exact (hne rfl).elim
  | cons k ks ih =>
    rw [virWord, show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
      mk_L_neg W (virWord_grading W W.vacuum_mem ks) (k + 1) (by omega)]
    simp only [map_smul, map_add, q24L_omega, smul_zero, zero_add]
    cases ks with
    | nil => simp [OrbOctaR.wordWeight]
    | cons j js => rw [ih (by simp), smul_zero, smul_zero]

/-- Every positive-weight state below 36 vanishes on the zero conformal fiber. -/
theorem q24_grading_lt36 {N : ℤ} (hpos : 0 < N) (hN : N < 36)
    {y : (orbifold OrbC2b.octa).carrier} (hy : y ∈ W.grading N) :
    q24L (mk W y) = 0 := by
  have hp : ∀ z ∈ twoSeedSpan, piHom W N z ∈ zeroKernel := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · have hw := virWord_grading W W.vacuum_mem ks
        by_cases he : 0 + (OrbOctaR.wordWeight ks : ℤ) = N
        · rw [piHom_of_mem W (he ▸ hw)]
          apply q24_vacWord
          intro h
          simp [h, OrbOctaR.wordWeight] at he
          omega
        · rw [piHom_of_mem_ne W he hw]; exact Submodule.zero_mem _
      · have hw := virWord_grading W X_grading ks
        by_cases he : 16 + (OrbOctaR.wordWeight ks : ℤ) = N
        · rw [piHom_of_mem W (he ▸ hw)]
          exact q24_word X_grading q24_seed16 ks
        · rw [piHom_of_mem_ne W he hw]; exact Submodule.zero_mem _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h := hp y (grading_lt_36 N hN hy)
  simpa only [piHom_of_mem W hy, LinearMap.mem_ker, LinearMap.comp_apply] using h

/-- The circle relation at index -5 kills the new weight-36 mode class. -/
theorem q24_selfMode_neg5 : q24L (selfMode (-5)) = 0 := by
  have h := congrArg q24L (selfMode_circle 3)
  simp only [map_sum, map_smul, map_zero] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [Finset.sum_range_succ'] at h
  have hz : ∑ j ∈ Finset.range 16,
      cbz 16 ((j + 1 : ℕ) : ℤ) • q24L (selfMode (((j + 1 : ℕ) : ℤ) - 5)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hg : W.smul X (((j + 1 : ℕ) : ℤ) - 5) X ∈
        W.grading (35 - (j : ℤ)) := by
      convert W.grading_mode _ X_grading _ X_grading _ using 2 ; push_cast ; ring
    rw [q24_grading_lt36 (by have := Finset.mem_range.mp hj; omega) (by omega) hg,
      smul_zero]
  rw [hz, zero_add] at h
  simpa using h

end VOA.Classification.COne.OrbOctaZD
