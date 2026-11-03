import VOA.Classification.COne.ABDWeakAdmissibleNormalForm

/-! The degree-normal-form residual, proved for arbitrary weak modules. -/
namespace VOA.Classification.COne.ABDWeakAdmissible
open VOA.Huang.BuhlSpanning VOA.Huang.LogRemovalAdmissible C2LevelFinite

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Arbitrary homogeneous words reduce to generator words of the same degree. -/
theorem homogeneousWord_mem_degreeFiltration (D : GenData W) (A : WeakModule W M)
    (B : Submodule ℂ M) {x : M} (hx : x ∈ B) (l : List (HomogeneousLetter W)) :
    ∃ G, homogeneousWord A l x ∈ DegreeFiltration.E D A B G (homogeneousDegree l) := by
  induction l with
  | nil => exact ⟨0, DegreeFiltration.mem_E_zero hx 0⟩
  | cons a l ih =>
    obtain ⟨G, hG⟩ := ih
    rcases lt_or_ge a.weight 0 with ha | ha
    · have hz : a.state = 0 := by
        have h := a.homogeneous
        rw [W.positivity _ ha, Submodule.mem_bot] at h
        exact h
      refine ⟨0, ?_⟩
      simp [homogeneousWord, hz]
    · obtain ⟨p, hp⟩ : ∃ p : ℕ, a.weight = (p : ℤ) :=
        ⟨a.weight.toNat, by omega⟩
      have h := DegreeFiltration.act_mem_E p a.state (hp ▸ a.homogeneous)
        a.modeIndex G (homogeneousDegree l) _ hG
      refine ⟨G + p, ?_⟩
      simpa [homogeneousWord, homogeneousDegree, hp, add_comm] using h

/-- Degree-preserving Buhl normalization, with no grading assumed on the weak module. -/
theorem weakDegreeNormalForm : WeakDegreeNormalForm W := by
  intro hC2 M _ _ A x
  obtain ⟨D⟩ := exists_genData hC2
  obtain ⟨N₀, hN₀⟩ := exists_grading_le_O₂ W hC2
  obtain ⟨Bm, hcut⟩ := exists_generator_cutoff D A x
  let B : Submodule ℂ M := Submodule.span ℂ {x}
  have hcutB : ∀ l : List (Ltr D), l.Pairwise (modeLE D) →
      (∃ e ∈ l, (Bm : ℤ) ≤ e.2) → ∀ b ∈ B, wordL D A l b = 0 := by
    intro l hl hbig b hb
    have hker : B ≤ LinearMap.ker (wordL D A l) := by
      apply Submodule.span_le.mpr
      rw [Set.singleton_subset_iff]
      exact sorted_word_eq_zero D A x hcut l hl hbig
    exact hker hb
  refine ⟨D, N₀ + 1, Bm, ?_⟩
  intro d
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨G, hG⟩ := homogeneousWord_mem_degreeFiltration D A B
    (Submodule.mem_span_singleton_self x) l
  rw [hl] at hG
  have hn := DegreeFiltration.E_le_normalSpan hN₀ hcutB G d hG
  have hle : DegreeFiltration.normalSpan D A B (N₀ + 1) d ≤
      normalDegreeSpan D A x (N₀ + 1) Bm d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, b, hr, hd, hb, rfl⟩
    by_cases hbig : ∃ e ∈ r, (Bm : ℤ) ≤ e.2
    · rw [hcutB r hr.1 hbig b hb]; exact Submodule.zero_mem _
    push Not at hbig
    induction hb using Submodule.span_induction with
    | mem b hb =>
      have he : b = x := Set.mem_singleton_iff.mp hb
      subst b
      exact Submodule.subset_span ⟨r, ⟨hr, hbig, hd⟩, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  exact hle hn

/-- Unconditional conformal local finiteness for C₂-cofinite weak modules. -/
theorem weakL0LocallyFinite : WeakL0LocallyFinite W :=
  weakL0LocallyFinite_of_degreeNormalForm weakDegreeNormalForm

/-- Only the global spectral lower bound remains in the ABD reduction. -/
theorem abdWeakIsAdmissible_of_boundedBelow (hbound : WeakSpectrumBoundedBelow W) :
    ABDWeakIsAdmissible W :=
  abdWeakIsAdmissible_of_degreeNormalForm_boundedBelow weakDegreeNormalForm hbound

end VOA.Classification.COne.ABDWeakAdmissible
