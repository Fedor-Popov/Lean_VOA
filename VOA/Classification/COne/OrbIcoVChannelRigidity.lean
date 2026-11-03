import VOA.Classification.COne.OrbIcoVGround
import VOA.Classification.COne.OrbIcoZLow

/-! Positive-mode rigidity in the actual two icosahedral channels below weight 100. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco OrbIcoS OrbC2b OrbC2c
  VOA.LatGen VOA.LatGen.Triplet OrbOctaR

def primaryLine (N : ℤ) : Submodule ℂ (orbifold ico).carrier :=
  if N = 36 then Submodule.span ℂ {Xico} else ⊥

private theorem primaryLine_le_prim (N : ℤ) : primaryLine N ≤ prim Wi N := by
  by_cases hN : N = 36
  · subst N
    simp only [primaryLine, if_pos rfl]
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact OrbIcoZ.X_primary
  · simp [primaryLine, hN]

private theorem project_seed_word (N : ℤ) (hpos : 0 < N)
    (x : (orbifold ico).carrier) (h : x = Wi.vacuum ∨ x = Xico) (ks : List ℕ) :
    piHom Wi N (virWord Wi ks x) ∈ primaryLine N ⊔ lowerDesc Wi N := by
  rcases h with rfl | rfl
  · have hw := virWord_grading Wi Wi.vacuum_mem ks
    by_cases he : 0 + (OrbOctaR.wordWeight ks : ℤ) = N
    · rw [piHom_of_mem Wi (he ▸ hw)]
      cases ks with
      | nil => simp [OrbOctaR.wordWeight] at he; omega
      | cons k ks =>
        apply Submodule.mem_sup_right
        refine Submodule.subset_span ⟨k, virWord Wi ks Wi.vacuum, ?_, rfl⟩
        have ht := virWord_grading Wi Wi.vacuum_mem ks
        have hh : N - (k : ℤ) - 1 = 0 + (OrbOctaR.wordWeight ks : ℤ) := by
          simp only [OrbOctaR.wordWeight, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one] at he ⊢
          omega
        rw [hh]; exact ht
    · rw [piHom_of_mem_ne Wi he hw]
      exact Submodule.zero_mem _
  · have hw := virWord_grading Wi Xico_grading ks
    by_cases he : 36 + (OrbOctaR.wordWeight ks : ℤ) = N
    · rw [piHom_of_mem Wi (he ▸ hw)]
      cases ks with
      | nil =>
        have hn : N = 36 := by simpa [OrbOctaR.wordWeight] using he.symm
        subst N
        apply Submodule.mem_sup_left
        simpa [primaryLine, virWord] using Submodule.subset_span (s := {Xico}) (by simp)
      | cons k ks =>
        apply Submodule.mem_sup_right
        refine Submodule.subset_span ⟨k, virWord Wi ks Xico, ?_, rfl⟩
        have ht := virWord_grading Wi Xico_grading ks
        have hh : N - (k : ℤ) - 1 = 36 + (OrbOctaR.wordWeight ks : ℤ) := by
          simp only [OrbOctaR.wordWeight, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one] at he ⊢
          omega
        rw [hh]; exact ht
    · rw [piHom_of_mem_ne Wi he hw]
      exact Submodule.zero_mem _

/-- Every positive primary below weight 100 lies on the actual weight-36 line. -/
theorem primary_below_hundred (N : ℤ) (hpos : 0 < N) (hN : N < 100) :
    prim Wi N ≤ primaryLine N := by
  intro p hp
  have hg := ((mem_prim _).mp hp).1
  have hs := grading_lt_100 N hN hg
  have hproj : ∀ z ∈ OrbIcoS.twoSeedSpan, piHom Wi N z ∈ primaryLine N ⊔ lowerDesc Wi N := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ks, rfl | rfl⟩ := hz
      · exact project_seed_word N hpos _ (Or.inl rfl) ks
      · exact project_seed_word N hpos _ (Or.inr rfl) ks
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hmem := hproj p hs
  rw [piHom_of_mem Wi hg] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hbp : b ∈ prim Wi N := by
    rw [← add_sub_cancel_left a b, hab]
    exact Submodule.sub_mem _ hp (primaryLine_le_prim N ha)
  have hz := OrbPrim.prim_inf_lowerDesc Wi
    ((v2VirUnitary_holds.some).restrict (orbifold ico)) N
  have hb0 : b = 0 := by
    have he : b ∈ prim Wi N ⊓ lowerDesc Wi N := ⟨hbp, hb⟩
    rw [hz] at he
    exact (Submodule.mem_bot ℂ).mp he
  rw [hb0, add_zero] at hab
  rwa [← hab]

/-- The vacuum channel has no positive-level highest vector in the needed energy range. -/
theorem vacuum_channel_positive_rigidity (N : ℤ) (hpos : 0 < N) (hN : N < 100)
    (x : (orbifold ico).carrier) (hx : x ∈ Wi.grading N)
    (hC : spinCasimir (x : Sp) = 0) (h1 : Wi.L 1 x = 0) (h2 : Wi.L 2 x = 0) : x = 0 := by
  have hp : x ∈ prim Wi N := by
    rw [mem_prim]
    refine ⟨hx, fun m => ?_⟩
    simpa using OrbOdd.L_pos_of_L1_L2 h1 h2 (m + 1) (by omega)
  have hl := primary_below_hundred N hpos hN hp
  by_cases he : N = 36
  · subst N
    simp only [primaryLine, if_pos rfl] at hl
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hl
    rw [← hc] at hC ⊢
    rw [Submodule.coe_smul, map_smul, spinCasimir_Xico, smul_smul] at hC
    have hz : (c * 168 : ℂ) = 0 := (smul_eq_zero.mp hC).resolve_right Xico_ambient_ne_zero
    have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_right (by norm_num)
    rw [hc0, zero_smul]
  · simp only [primaryLine, if_neg he, Submodule.mem_bot] at hl
    exact hl

/-- The spin-six channel has no higher highest vector before the next invariant seed. -/
theorem sixth_channel_positive_rigidity (N : ℤ) (hpos : 36 < N) (hN : N < 100)
    (x : (orbifold ico).carrier) (hx : x ∈ Wi.grading N)
    (h1 : Wi.L 1 x = 0) (h2 : Wi.L 2 x = 0) : x = 0 := by
  have hp : x ∈ prim Wi N := by
    rw [mem_prim]
    refine ⟨hx, fun m => ?_⟩
    simpa using OrbOdd.L_pos_of_L1_L2 h1 h2 (m + 1) (by omega)
  have hl := primary_below_hundred N (by omega) hN hp
  simpa [primaryLine, show N ≠ 36 by omega] using hl

end VOA.Classification.COne.OrbIcoV
