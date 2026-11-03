import VOA.Classification.COne.OrbOctaZDProjection81

/-! Close the graded range below 144 using the top product of the known seeds. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbOcta OrbC2b OrbC2c OrbOctaZC OrbOctaR

theorem inv_mul {F G : P3} (hF : IsS4Inv F) (hG : IsS4Inv G) : IsS4Inv (F * G) :=
  ⟨isA4Inv_mul hF.1 hG.1, by rw [map_mul, hF.2, hG.2]⟩

theorem Tav_grading {F : P3} {s : ℕ} (hF : IsS4Inv F) (hs : F.IsHomogeneous s) :
    Tav F ∈ W.grading ((s : ℤ) ^ 2) := by
  rw [orb_mem_grading, Tav_coe hF]
  exact T2_grad hs

theorem q24_grading_lt100 : ∀ N : ℤ, 0 < N → N < 100 →
    ∀ y ∈ W.grading N, q24L (mk W y) = 0 := by
  apply q24_grading_below 100
  rintro ⟨a, b, c, d⟩ hp hn hb
  by_cases ha : 0 < a
  · rw [Tav_genMon_r2 a b c d ha, map_zero, map_zero]
  · have ha0 : a = 0 := by omega
    subst a
    have ht : 3 * b + 4 * c + 6 * d < 10 := by
      simp only [gdeg] at hb
      nlinarith
    simp only [par, gdeg] at hp hn
    have he : (b = 0 ∧ c = 1 ∧ d = 0) ∨
        (b = 2 ∧ c = 0 ∧ d = 0) ∨
        (b = 0 ∧ c = 2 ∧ d = 0) ∨
        (b = 1 ∧ c = 0 ∧ d = 1) := by
      have hb3 : b ≤ 3 := by omega
      have hc2 : c ≤ 2 := by omega
      have hd1 : d ≤ 1 := by omega
      interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simpa [genMon] using q24_seed16
    · simpa [genMon, pow_two] using q24_seed_two
    · simpa [genMon, pow_two] using q24_I4sq
    · simpa [genMon] using q24_seed_three

theorem q24_I4I3sq : q24L (mk W (Tav (I4 * (I3 * I3)))) = 0 :=
  q24_top inv_I4 inv_I3sq I4_hom (I3_hom.mul I3_hom) q24_grading_lt100
    (by simpa using q24_XY_negative 48)

theorem q24_grading_lt144 : ∀ N : ℤ, 0 < N → N < 144 →
    ∀ y ∈ W.grading N, q24L (mk W y) = 0 := by
  apply q24_grading_below 144
  rintro ⟨a, b, c, d⟩ hp hn hb
  by_cases ha : 0 < a
  · rw [Tav_genMon_r2 a b c d ha, map_zero, map_zero]
  · have ha0 : a = 0 := by omega
    subst a
    have ht : 3 * b + 4 * c + 6 * d < 12 := by
      simp only [gdeg] at hb
      nlinarith
    simp only [par, gdeg] at hp hn
    have he : (b = 0 ∧ c = 1 ∧ d = 0) ∨
        (b = 2 ∧ c = 0 ∧ d = 0) ∨
        (b = 0 ∧ c = 2 ∧ d = 0) ∨
        (b = 1 ∧ c = 0 ∧ d = 1) ∨
        (b = 2 ∧ c = 1 ∧ d = 0) := by
      have hb3 : b ≤ 3 := by omega
      have hc2 : c ≤ 2 := by omega
      have hd1 : d ≤ 1 := by omega
      interval_cases b <;> interval_cases c <;> interval_cases d <;> omega
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simpa [genMon] using q24_seed16
    · simpa [genMon, pow_two] using q24_seed_two
    · simpa [genMon, pow_two] using q24_I4sq
    · simpa [genMon] using q24_seed_three
    · simpa [genMon, pow_two, mul_comm] using q24_I4I3sq

theorem q24_XI4sq_negative (m : ℕ) :
    q24L (mk W (W.smul X (-((m : ℤ) + 1)) (Tav (I4 * I4)))) = 0 := by
  apply q24_negative_modes (d := 16) (by norm_num) X_grading ?_ m
  intro k hk hk16
  have hg : W.smul X k (Tav (I4 * I4)) ∈ W.grading (79 - k) := by
    convert W.grading_mode _ X_grading _
      (Tav_grading (inv_mul inv_I4 inv_I4) (I4_hom.mul I4_hom)) k using 2 ; norm_num ; ring
  exact q24_grading_lt81 _ (by omega) (by omega) _ hg

theorem q24_YY_negative (m : ℕ) :
    q24L (mk W (W.smul (octaSeeds 2) (-((m : ℤ) + 1)) (octaSeeds 2))) = 0 := by
  have hg36 : octaSeeds 2 ∈ W.grading (36 : ℤ) := OrbOctaZ.seeds_homogeneous 2
  apply q24_negative_modes (d := 36) (by norm_num) hg36 ?_ m
  intro k hk hk36
  have hg : W.smul (octaSeeds 2) k (octaSeeds 2) ∈ W.grading (71 - k) := by
    convert W.grading_mode _ hg36 _ hg36 k using 2 ; ring
  exact q24_grading_lt81 _ (by omega) (by omega) _ hg

theorem q24_I4cube : q24L (mk W (Tav (I4 * (I4 * I4)))) = 0 :=
  q24_top inv_I4 (inv_mul inv_I4 inv_I4) I4_hom (I4_hom.mul I4_hom) q24_grading_lt144
    (by simpa using q24_XI4sq_negative 64)

theorem q24_I3four : q24L (mk W (Tav ((I3 * I3) * (I3 * I3)))) = 0 :=
  q24_top inv_I3sq inv_I3sq (I3_hom.mul I3_hom) (I3_hom.mul I3_hom) q24_grading_lt144
    (by simpa using q24_YY_negative 72)

end VOA.Classification.COne.OrbOctaZD
