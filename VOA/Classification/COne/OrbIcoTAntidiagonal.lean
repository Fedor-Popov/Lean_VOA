import VOA.Classification.COne.OrbIcoTBase
import VOA.Classification.COne.OrbIcoTLower
import VOA.Classification.COne.OrbIcoTCoeff

/-! The first nonzero antidiagonal of the sixth channel, including normalization. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VOA.LatGen VOA.LatGen.Triplet OrbIco OrbPrim OrbRat6

theorem sixth_pair_0 : V2v.smul (wv 6 0) 35 (wv 6 6) =
    (-33604986844 / 21 : ℂ) • wv 6 0 := w60_w66

theorem sixth_pair_1 : V2v.smul (wv 6 1) 35 (wv 6 5) =
    (8401246711 / 9 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 0 5 (by norm_num))
  rw [fo_smul, fo_wv 6 0 (by norm_num), fo_wv 6 5 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_0, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 12 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  exact hs

theorem sixth_pair_2 : V2v.smul (wv 6 2) 35 (wv 6 4) =
    (-6109997608 / 9 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 1 4 (by norm_num))
  rw [fo_smul, fo_wv 6 1 (by norm_num), fo_wv 6 4 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_1, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 11 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  simpa only [neg_div] using hs

theorem sixth_pair_3 : V2v.smul (wv 6 3) 35 (wv 6 3) =
    (3054998804 / 5 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 2 3 (by norm_num))
  rw [fo_smul, fo_wv 6 2 (by norm_num), fo_wv 6 3 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_2, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 10 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  exact hs

theorem sixth_pair_4 : V2v.smul (wv 6 4) 35 (wv 6 2) =
    (-6109997608 / 9 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 3 2 (by norm_num))
  rw [fo_smul, fo_wv 6 3 (by norm_num), fo_wv 6 2 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_3, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 9 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  simpa only [neg_div] using hs

theorem sixth_pair_5 : V2v.smul (wv 6 5) 35 (wv 6 1) =
    (8401246711 / 9 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 4 1 (by norm_num))
  rw [fo_smul, fo_wv 6 4 (by norm_num), fo_wv 6 1 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_4, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 8 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  exact hs

theorem sixth_pair_6 : V2v.smul (wv 6 6) 35 (wv 6 0) =
    (-33604986844 / 21 : ℂ) • wv 6 0 := by
  have h := congrArg fo (sixth_pair_zero 5 0 (by norm_num))
  rw [fo_smul, fo_wv 6 5 (by norm_num), fo_wv 6 0 (by norm_num),
    PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
    sixth_pair_5, smul_smul, map_zero] at h
  have hs := congrArg (fun v : Sp => (1 / 7 : ℂ) • v)
    (eq_neg_of_add_eq_zero_left h)
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  simpa only [neg_div] using hs

theorem sixth_base_pair (i j : ℕ) (hij : i + j = 6) :
    V2v.smul (wv 6 i) 35 (wv 6 j) =
      ((-33604986844 / 21 : ℂ) * (sixthCoeff i j : ℂ)) • wv 6 0 := by
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hj : j = 6 := by omega
    subst j
    rw [sixth_pair_0]
    norm_num [sixthCoeff, sixthRow0]
  · have hj : j = 5 := by omega
    subst j
    rw [sixth_pair_1]
    norm_num [sixthCoeff, sixthRow1]
  · have hj : j = 4 := by omega
    subst j
    rw [sixth_pair_2]
    norm_num [sixthCoeff, sixthRow2]
  · have hj : j = 3 := by omega
    subst j
    rw [sixth_pair_3]
    norm_num [sixthCoeff, sixthRow3]
  · have hj : j = 2 := by omega
    subst j
    rw [sixth_pair_4]
    norm_num [sixthCoeff, sixthRow4]
  · have hj : j = 1 := by omega
    subst j
    rw [sixth_pair_5]
    norm_num [sixthCoeff, sixthRow5]
  · have hj : j = 0 := by omega
    subst j
    rw [sixth_pair_6]
    norm_num [sixthCoeff, sixthRow6]

end VOA.Classification.COne.OrbIcoT
