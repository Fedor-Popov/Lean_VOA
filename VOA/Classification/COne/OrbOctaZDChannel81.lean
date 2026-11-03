import VOA.Classification.COne.OrbOctaZDBase81

/-! First transvectant channel from spin four and spin six to spin nine. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6

def lam9 : ℂ := 2652 / 8

theorem first46 : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 1 ≤ t → t ≤ 19 → i ≤ 8 → j ≤ 12 →
    V2v.smul (wv 4 i) (-30) (wv 6 j) - (lam9 * (8 * (j : ℂ) - 12 * i)) • wv 9 (i + j - 1) ∈
      lowerDesc V2v (((9 : ℕ) : ℤ) ^ 2) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i j hij ht ht19 hi hj
  by_cases ht1 : t = 1
  · subst ht1
    rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [base46_01, show 0 + 1 - 1 = 0 by rfl, wv_zero, lam9]
      simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
      rw [← sub_smul]
      norm_num
    · rw [base46_10, show 1 + 0 - 1 = 0 by rfl, wv_zero, lam9]
      simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
      rw [← sub_smul]
      norm_num
  · have ht2 : 2 ≤ t := by omega
    set Φ := fun a b : ℕ => V2v.smul (wv 4 a) (-30) (wv 6 b) -
      (lam9 * (8 * (b : ℂ) - 12 * a)) • wv 9 (a + b - 1) with hΦ
    change Φ i j ∈ _
    have hgr : Φ i j ∈ V2v.grading (((9 : ℕ) : ℤ) ^ 2) := by
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
      have h := V2v.smul_mem_grading (wv_grading 4 i) (wv_grading 6 j) (-30)
      convert h using 2
    have hho : ho (Φ i j) = (((2 * 9 : ℕ) : ℂ) - 2 * ((t - 1 : ℕ) : ℂ)) • Φ i j := by
      subst hij
      simp only [hΦ]
      rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right]
      push_cast [Nat.cast_sub (show 1 ≤ i + j by omega)]
      module
    have heo : eo (Φ i j) ∈ lowerDesc V2v (((9 : ℕ) : ℤ) ^ 2) := by
      have hsplit : eo (Φ i j) =
          (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
          (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
        simp only [hΦ]
        rw [map_sub, map_smul, eo_smul, eo_wv' 4 i (by omega), eo_wv' 6 j (by omega),
          eo_wv' 9 (i + j - 1) (by omega), if_neg (show ¬ i + j - 1 = 0 by omega)]
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · subst hi0
          simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
            PreVertexAlgebra.smul_smul_right]
          push_cast [Nat.cast_sub (show 1 ≤ j by omega)]
          module
        · subst hj0
          simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
            PreVertexAlgebra.smul_smul_left]
          push_cast [Nat.cast_sub (show 1 ≤ i by omega)]
          module
        · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
            PreVertexAlgebra.smul_smul_right,
            show i - 1 + j - 1 = i + j - 1 - 1 by omega,
            show i + (j - 1) - 1 = i + j - 1 - 1 by omega]
          push_cast [Nat.cast_sub (show 1 ≤ i + j by omega), Nat.cast_sub (show 1 ≤ i by omega),
            Nat.cast_sub (show 1 ≤ j by omega)]
          module
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · split_ifs with hi0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _
            (ih (i - 1 + j) (by omega) (i - 1) j rfl (by omega) (by omega) (by omega) hj)
      · split_ifs with hj0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _
            (ih (i + (j - 1)) (by omega) i (j - 1) rfl (by omega) (by omega) hi (by omega))
    exact ekernel 9 (t - 1) (by omega) hgr (by rw [hho]) heo

end VOA.Classification.COne.OrbOctaZD
