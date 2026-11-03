import VOA.Classification.COne.OrbIcoTAntidiagonal

/-! The sixth channel on the spin-six multiplet, modulo lower Virasoro descendants. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoT
open VOA VertexOperatorAlgebra OrbSpan OrbIco OrbPrim OrbRat6

local notation "K" => (-33604986844 / 21 : ℂ)

theorem sixth_wv : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → 6 ≤ t → t ≤ 18 →
    i ≤ 12 → j ≤ 12 →
    V2v.smul (wv 6 i) 35 (wv 6 j) - (K * (sixthCoeff i j : ℂ)) • wv 6 (i + j - 6) ∈
      lowerDesc V2v 36 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro i j hij ht ht18 hi hj
    by_cases ht6 : t = 6
    · have h6 : i + j = 6 := by omega
      rw [sixth_base_pair i j h6, h6, Nat.sub_self, sub_self]
      exact Submodule.zero_mem _
    · have ht7 : 7 ≤ t := by omega
      let Φ := fun a b : ℕ => V2v.smul (wv 6 a) 35 (wv 6 b) -
        (K * (sixthCoeff a b : ℂ)) • wv 6 (a + b - 6)
      change Φ i j ∈ _
      have hgr : Φ i j ∈ V2v.grading (((6 : ℕ) : ℤ) ^ 2) := by
        refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
        convert V2v.smul_mem_grading (wv_grading 6 i) (wv_grading 6 j) 35 using 2
      have hho : ho (Φ i j) = ((12 : ℂ) - 2 * ((t - 6 : ℕ) : ℂ)) • Φ i j := by
        subst hij
        simp only [Φ]
        rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv,
          PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
        push_cast [Nat.cast_sub (show 6 ≤ i + j by omega)]
        module
      have heo : eo (Φ i j) ∈ lowerDesc V2v 36 := by
        have hsplit : eo (Φ i j) =
            (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
            (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
          have hc := sixthCoeff_rec i j hi hj (by omega)
          simp only [Φ]
          rw [map_sub, map_smul, eo_smul, eo_wv' 6 i hi, eo_wv' 6 j hj,
            eo_wv' 6 (i + j - 6) (by omega), if_neg (show ¬ i + j - 6 = 0 by omega)]
          by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
          · omega
          · subst hi0
            simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
              PreVertexAlgebra.smul_smul_right,
              show j - 1 - 6 = j - 6 - 1 by omega]
            simp only [Nat.cast_zero, zero_add, zero_mul] at hc
            push_cast [Nat.cast_sub (show 6 ≤ j by omega)]
            linear_combination (norm := module) (-K * eps1 * hc) • wv 6 (j - 6 - 1)
          · subst hj0
            simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
              PreVertexAlgebra.smul_smul_left,
              show i - 1 - 6 = i - 6 - 1 by omega]
            simp only [Nat.cast_zero, add_zero, zero_mul] at hc
            push_cast [Nat.cast_sub (show 6 ≤ i by omega)]
            linear_combination (norm := module) (-K * eps1 * hc) • wv 6 (i - 6 - 1)
          · simp only [if_neg hi0, if_neg hj0, PreVertexAlgebra.smul_smul_left,
              PreVertexAlgebra.smul_smul_right,
              show i - 1 + j - 6 = i + j - 6 - 1 by omega,
              show i + (j - 1) - 6 = i + j - 6 - 1 by omega]
            push_cast [Nat.cast_sub (show 6 ≤ i + j by omega)]
            linear_combination (norm := module)
              (-K * eps1 * hc) • wv 6 (i + j - 6 - 1)
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
      exact ekernel 6 (t - 6) (by omega) hgr (by simpa using hho) heo

/-- The complete sixth-channel projection on every pair of multiplet vectors. -/
theorem sixth_wv_all (i j : ℕ) (hi : i ≤ 12) (hj : j ≤ 12) :
    V2v.smul (wv 6 i) 35 (wv 6 j) - (K * (sixthCoeff i j : ℂ)) • wv 6 (i + j - 6) ∈
      lowerDesc V2v 36 := by
  suffices hh : ∀ t : ℕ, ∀ a b : ℕ, a + b = t → a ≤ 12 → b ≤ 12 →
      V2v.smul (wv 6 a) 35 (wv 6 b) -
        (K * (sixthCoeff a b : ℂ)) • wv 6 (a + b - 6) ∈ lowerDesc V2v 36 from
    hh (i + j) i j rfl hi hj
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro a b hab ha hb
    by_cases hlo : t < 6
    · rw [sixth_pair_zero a b (by omega),
        sixthCoeff_support a b ha hb (Or.inl (by omega))]
      simp
    by_cases hmid : t ≤ 18
    · exact sixth_wv t a b hab (by omega) hmid ha hb
    have hhigh : 18 < a + b := by omega
    rw [sixthCoeff_support a b ha hb (Or.inr hhigh), Rat.cast_zero, mul_zero,
      zero_smul, sub_zero]
    have h1 := ih (a - 1 + b) (by omega) (a - 1) b rfl (by omega) hb
    have h2 := ih (a + (b - 1)) (by omega) a (b - 1) rfl ha (by omega)
    have hc := sixthCoeff_rec a b ha hb (by omega)
    rw [sixthCoeff_support a b ha hb (Or.inr hhigh), Rat.cast_zero, zero_mul] at hc
    have hg : V2v.smul (wv 6 a) 35 (wv 6 b) ∈ V2v.grading (((6 : ℕ) : ℤ) ^ 2) := by
      convert V2v.smul_mem_grading (wv_grading 6 a) (wv_grading 6 b) 35 using 2
    refine ekernel 6 (t - 6) (by omega) hg ?_ ?_
    · rw [ho_smul, ho_wv, ho_wv,
        PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right]
      subst hab
      push_cast [Nat.cast_sub (show 6 ≤ a + b by omega)]
      module
    · have he : eo (V2v.smul (wv 6 a) 35 (wv 6 b)) =
          (eps1 * (a : ℂ)) • (V2v.smul (wv 6 (a - 1)) 35 (wv 6 b) -
            (K * (sixthCoeff (a - 1) b : ℂ)) • wv 6 (a - 1 + b - 6)) +
          (eps1 * (b : ℂ)) • (V2v.smul (wv 6 a) 35 (wv 6 (b - 1)) -
            (K * (sixthCoeff a (b - 1) : ℂ)) • wv 6 (a + (b - 1) - 6)) := by
        rw [eo_smul, eo_wv' 6 a ha, eo_wv' 6 b hb,
          if_neg (show a ≠ 0 by omega), if_neg (show b ≠ 0 by omega),
          PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
          show a - 1 + b - 6 = a + b - 7 by omega,
          show a + (b - 1) - 6 = a + b - 7 by omega]
        linear_combination (norm := module) (-K * eps1 * hc) • wv 6 (a + b - 7)
      rw [he]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

end VOA.Classification.COne.OrbIcoT
