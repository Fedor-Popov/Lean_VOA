import VOA.Classification.COne.OrbOctaZDChannel81

/-! The weight-64 top product closes the graded range below weight 81. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbOcta OrbC2b OrbC2c OrbOctaZC OrbOctaR

theorem inv_I4 : IsS4Inv I4 := ⟨isA4Inv_I4, s3_I4⟩
theorem inv_I3sq : IsS4Inv (I3 * I3) :=
  ⟨isA4Inv_mul isA4Inv_I3 isA4Inv_I3, by rw [map_mul, s3_I3, neg_mul_neg]⟩

theorem q24_XX_negative (m : ℕ) : q24L (selfMode (-((m : ℤ) + 1))) = 0 := by
  apply q24_negative_modes (d := 16) (by norm_num) X_grading ?_ m
  intro k hk hk16
  have hg : W.smul X k X ∈ W.grading (31 - k) := by
    convert W.grading_mode _ X_grading _ X_grading k using 2 ; ring
  exact q24_grading_lt36 (by omega) (by omega) hg

theorem q24_I4sq : q24L (mk W (Tav (I4 * I4))) = 0 :=
  q24_top inv_I4 inv_I4 I4_hom I4_hom q24_grading_lt64
    (by simpa using q24_XX_negative 32)

theorem q24_grading_lt81 : ∀ N : ℤ, 0 < N → N < 81 →
    ∀ y ∈ W.grading N, q24L (mk W y) = 0 := by
  apply q24_grading_below 81
  rintro ⟨a, b, c, d⟩ hp hn hb
  by_cases ha : 0 < a
  · rw [Tav_genMon_r2 a b c d ha, map_zero, map_zero]
  · have ha0 : a = 0 := by omega
    subst a
    have ht : 3 * b + 4 * c + 6 * d < 9 := by
      simp only [gdeg] at hb
      nlinarith
    simp only [par, gdeg] at hp hn
    have he : (b = 0 ∧ c = 1 ∧ d = 0) ∨ (b = 2 ∧ c = 0 ∧ d = 0) ∨
        (b = 0 ∧ c = 2 ∧ d = 0) := by
      have hb2 : b ≤ 2 := by omega
      have hc2 : c ≤ 2 := by omega
      have hd1 : d ≤ 1 := by omega
      interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simpa [genMon] using q24_seed16
    · simpa [genMon, pow_two] using q24_seed_two
    · simpa [genMon, pow_two] using q24_I4sq

theorem q24_XY_negative (m : ℕ) :
    q24L (mk W (W.smul X (-((m : ℤ) + 1)) (octaSeeds 2))) = 0 := by
  apply q24_negative_modes (d := 16) (by norm_num) X_grading ?_ m
  intro k hk hk16
  have hg36 : octaSeeds 2 ∈ W.grading (36 : ℤ) := OrbOctaZ.seeds_homogeneous 2
  have hg : W.smul X k (octaSeeds 2) ∈ W.grading (51 - k) := by
    convert W.grading_mode _ X_grading _ hg36 k using 2 ; ring
  exact q24_grading_lt64 _ (by omega) (by omega) _ hg

end VOA.Classification.COne.OrbOctaZD
