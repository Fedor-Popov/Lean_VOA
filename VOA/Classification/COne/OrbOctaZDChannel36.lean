import VOA.Classification.COne.OrbOctaZDBase36

/-! The second transvectant channel of two spin-four primaries. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbOctaZD
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6

private theorem fo41 : fo (wv 4 1) = (7 : ℂ) • wv 4 2 := by
  simp only [wv, cnk, vn, pow_succ', Module.End.mul_apply, map_smul]
  norm_num [Nat.factorial, smul_smul]

private theorem pair10 : V2v.smul (wv 4 1) (-5) (wv 4 0) = 0 := by
  have h := congrArg fo pair00
  rw [fo_smul, fo_wv0 4 (by norm_num), PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, pair01, smul_zero, add_zero, map_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

private theorem pair11 : V2v.smul (wv 4 1) (-5) (wv 4 1) =
    (14157 / 2 : ℂ) • wv 6 0 := by
  have h := congrArg fo pair01
  rw [fo_smul, fo_wv0 4 (by norm_num), fo41, PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, pair02, smul_smul, map_zero] at h
  have he := eq_neg_of_add_eq_zero_left h
  have hs := congrArg (fun v : Sp => (1 / 8 : ℂ) • v) he
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  simpa only [neg_div] using hs

private theorem pair20 : V2v.smul (wv 4 2) (-5) (wv 4 0) =
    (-56628 / 7 : ℂ) • wv 6 0 := by
  have h := congrArg fo pair10
  rw [fo_smul, fo41, fo_wv0 4 (by norm_num), PreVertexAlgebra.smul_smul_left,
    PreVertexAlgebra.smul_smul_right, pair11, smul_smul, map_zero] at h
  have he := eq_neg_of_add_eq_zero_left h
  have hs := congrArg (fun v : Sp => (1 / 7 : ℂ) • v) he
  norm_num [smul_smul, smul_neg, ← neg_smul] at hs
  simpa only [neg_div] using hs

/-- The normalized second-transvectant coefficient; the (0,2) entry is one. -/
def coeff36 (i j : ℕ) : ℂ :=
  ((i : ℂ) + j) * (i + j - 1) / 2 - (15 / 8 : ℂ) * i * j

/-- Actual mode projection, modulo lower Virasoro descendants. -/
theorem second44 : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 2 ≤ t → t ≤ 14 →
    i ≤ 8 → j ≤ 8 →
    V2v.smul (wv 4 i) (-5) (wv 4 j) -
      ((-56628 / 7 : ℂ) * coeff36 i j) • wv 6 (i + j - 2) ∈ lowerDesc V2v 36 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro i j hij ht ht14 hi hj
    by_cases ht2 : t = 2
    · subst ht2
      rcases (show (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 1) ∨ (i = 2 ∧ j = 0) by omega)
        with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [pair02]; norm_num [coeff36]
      · rw [pair11]; norm_num [coeff36]
      · rw [pair20]; norm_num [coeff36]
    · have ht3 : 3 ≤ t := by omega
      let Φ := fun a b : ℕ => V2v.smul (wv 4 a) (-5) (wv 4 b) -
        ((-56628 / 7 : ℂ) * coeff36 a b) • wv 6 (a + b - 2)
      change Φ i j ∈ _
      have hgr : Φ i j ∈ V2v.grading (((6 : ℕ) : ℤ) ^ 2) := by
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
        convert V2v.smul_mem_grading (wv_grading 4 i) (wv_grading 4 j) (-5) using 2
      have hho : ho (Φ i j) = ((12 : ℂ) - 2 * ((t - 2 : ℕ) : ℂ)) • Φ i j := by
        subst hij
        simp only [Φ]
        rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv,
          PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
        push_cast [Nat.cast_sub (show 2 ≤ i + j by omega)]
        module
      have heo : eo (Φ i j) ∈ lowerDesc V2v 36 := by
        have hsplit : eo (Φ i j) =
            (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
            (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
          simp only [Φ]
          rw [map_sub, map_smul, eo_smul, eo_wv' 4 i hi, eo_wv' 4 j hj,
            eo_wv' 6 (i + j - 2) (by omega), if_neg (show ¬ i + j - 2 = 0 by omega)]
          by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
          · omega
          · subst hi0
            simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
              PreVertexAlgebra.smul_smul_right]
            simp only [coeff36]
            push_cast [Nat.cast_sub (show 1 ≤ j by omega),
              Nat.cast_sub (show 2 ≤ j by omega)]
            module
          · subst hj0
            simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
              PreVertexAlgebra.smul_smul_left]
            simp only [coeff36]
            push_cast [Nat.cast_sub (show 1 ≤ i by omega),
              Nat.cast_sub (show 2 ≤ i by omega)]
            module
          · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
              PreVertexAlgebra.smul_smul_right,
              show i - 1 + j - 2 = i + j - 2 - 1 by omega,
              show i + (j - 1) - 2 = i + j - 2 - 1 by omega, coeff36]
            push_cast [Nat.cast_sub (show 2 ≤ i + j by omega),
              Nat.cast_sub (show 1 ≤ i by omega), Nat.cast_sub (show 1 ≤ j by omega)]
            module
        rw [hsplit]
        apply Submodule.add_mem
        · split_ifs with hi0
          · exact Submodule.zero_mem _
          · exact Submodule.smul_mem _ _
              (ih (i - 1 + j) (by omega) (i - 1) j rfl (by omega) (by omega) (by omega) hj)
        · split_ifs with hj0
          · exact Submodule.zero_mem _
          · exact Submodule.smul_mem _ _
              (ih (i + (j - 1)) (by omega) i (j - 1) rfl (by omega) (by omega) hi (by omega))
      exact ekernel 6 (t - 2) (by omega) hgr (by simpa using hho) heo

end VOA.Classification.COne.OrbOctaZD
