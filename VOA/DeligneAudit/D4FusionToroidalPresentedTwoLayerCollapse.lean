import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerBounds

/-! Conditional second-layer bound with the surviving quadratic seed at t-mode zero. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem twoQuadraticSeed_mem_N2 : twoQuadraticSeed ∈ twoN 2 := by
  exact twoN_word 2
    [(D4sector.c₀, 1, 0), (D4sector.c₀, 1, 0)] (by simp [twoUDeg])

theorem two_second_layer_bound_of_collapse (h : TwoUTwoCollapse) :
    FiniteDimensional ℂ twoN2inN1 ∧ Module.finrank ℂ twoN2inN1 ≤ 1 := by
  let seedN1 : twoN 1 :=
    ⟨twoQuadraticSeed, twoN_mono (by omega) twoQuadraticSeed_mem_N2⟩
  have hle : twoN2inN1 ≤ Submodule.span ℂ {seedN1} := by
    intro x hx
    have hx2 : (x : PTE 2) ∈ Submodule.span ℂ {twoQuadraticSeed} :=
      h ((twoN2inN1_subtype x).mp hx)
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx2
    apply Submodule.mem_span_singleton.mpr
    exact ⟨a, Subtype.ext ha⟩
  letI : FiniteDimensional ℂ (Submodule.span ℂ {seedN1}) :=
    FiniteDimensional.span_singleton ℂ seedN1
  letI : FiniteDimensional ℂ twoN2inN1 :=
    Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  calc
    Module.finrank ℂ twoN2inN1 ≤
        Module.finrank ℂ (Submodule.span ℂ {seedN1}) :=
      Submodule.finrank_mono hle
    _ ≤ 1 := by
      simpa using (finrank_span_le_card (R := ℂ) ({seedN1} : Set (twoN 1)))

theorem presentedRankBoundE_two_of' (h₁ : TwoPositiveSpanBound)
    (h₂ : TwoUTwoCollapse) : PresentedRankBoundE 2 (by norm_num) :=
  presentedRankBoundE_two_of
    ⟨two_first_layer_bound_of_span h₁, two_second_layer_bound_of_collapse h₂⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.twoQuadraticSeed_mem_N2
#print axioms VOA.DeligneAudit.Toroidal.two_second_layer_bound_of_collapse
#print axioms VOA.DeligneAudit.Toroidal.presentedRankBoundE_two_of'
