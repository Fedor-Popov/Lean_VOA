import VOA.Classification.COne.PlusRat3Raise
import VOA.Classification.COne.PlusRatReverse

/-! # Degree-one words on an eigenvector are single degree-one modes (general VOA)

For an `L(0)`-eigenvector `x` (eigenvalue `k`), every homogeneous mode word of total degree one
applied to `x` lies in the span of the single modes `a₍β-2₎x`, `a ∈ V_β` (`degreeSpan_one_le`).
Proof: Li's single-mode spanning (`modeSpan`) and the spectral decomposition of `L(0)`.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusRat3
open VOA VertexOperatorAlgebra PlusSplitting PlusRatTelescope VOA.Huang.LogRemovalAdmissible
  ABDWeakAdmissible PlusRatSign
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V} (A : WeakModule W M)

/-- The span of the single degree-one modes on `x`. -/
def degOneSpan (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (β : ℤ) (a : V), a ∈ W.grading β ∧ y = mode (A.YM a) (β - 2) x}

theorem degOneSpan_le_gen {x : M} {k : ℂ} (hL : L0 A x = k • x) :
    degOneSpan A x ≤ (L0 A).maxGenEigenspace (k + 1) := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  apply Submodule.span_le.mpr
  rintro _ ⟨β, a, ha, rfl⟩
  have h := mode_mem_maxGenEigenspace A ha (β - 2) hxg
  have hc : k + ((β - (β - 2) - 1 : ℤ) : ℂ) = k + 1 := by push_cast; ring
  rwa [hc] at h

theorem modeSpan_le_degOne_sup {x : M} {k : ℂ} (hL : L0 A x = k • x) :
    VOA.Moonshine.SigmaExist.modeSpan A {x} ≤
      degOneSpan A x ⊔ spectralPart A {μ | μ ≠ k + 1} := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  apply Submodule.span_le.mpr
  rintro _ ⟨a, q, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hv : a ∈ ⨆ k, W.grading k := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction _ (motive := fun a => A.act a q y ∈
    degOneSpan A y ⊔ spectralPart A {μ | μ ≠ k + 1}) hv ?_ ?_ ?_
  · intro j b hb
    by_cases hq : q = j - 2
    · subst hq
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨j, b, hb, rfl⟩)
    · apply Submodule.mem_sup_right
      have h := mode_mem_maxGenEigenspace A hb q hxg
      apply Submodule.mem_iSup_of_mem (k + ((j - q - 1 : ℤ) : ℂ))
      apply Submodule.mem_iSup_of_mem
      · exact h
      · intro he
        have h2 : ((j - q - 1 : ℤ) : ℂ) = 1 := by linear_combination he
        have h3 : (j - q - 1 : ℤ) = 1 := by exact_mod_cast h2
        omega
  · simp
  · intro a b ha hb
    have he : A.act (a + b) q y = A.act a q y + A.act b q y := by
      simp only [WeakModule.act_def, map_add, mode_add, LinearMap.add_apply]
    rw [he]
    exact Submodule.add_mem _ ha hb

/-- Degree-one words on an eigenvector are single degree-one modes. -/
theorem degreeSpan_one_le {x : M} {k : ℂ} (hL : L0 A x = k • x) :
    homogeneousDegreeSpan A x 1 ≤ degOneSpan A x := by
  have hxg : x ∈ (L0 A).maxGenEigenspace k :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hL)
  intro w hw
  have hg := homogeneousDegreeSpan_gen A hxg 1 hw
  have hsp : w ∈ VOA.Moonshine.SigmaExist.modeSpan A {x} := by
    refine Submodule.span_induction
      (p := fun v _ => v ∈ VOA.Moonshine.SigmaExist.modeSpan A {x}) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, _, rfl⟩
      exact homogeneousWord_mem_modeSpan A x l
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (modeSpan_le_degOne_sup A hL hsp)
  have hs' := degOneSpan_le_gen A hL hs
  have hk : (k + ((1 : ℤ) : ℂ)) = k + 1 := by push_cast; ring
  rw [hk] at hg
  have htg : t ∈ (L0 A).maxGenEigenspace (k + 1) := by
    have : t = w - s := by rw [← hst]; abel
    rw [this]; exact Submodule.sub_mem _ hg hs'
  have ht0 : t = 0 := by
    have hd := spectralPart_disjoint A (s := {k + 1}) (t := {μ | μ ≠ k + 1})
      (Set.disjoint_left.mpr (by intro μ hμ hn; exact hn (Set.mem_singleton_iff.mp hμ)))
    have htg' : t ∈ spectralPart A {k + 1} := by
      apply Submodule.mem_iSup_of_mem (k + 1)
      exact Submodule.mem_iSup_of_mem rfl htg
    exact Submodule.disjoint_def.mp hd t htg' ht
  rw [← hst, ht0, add_zero]
  exact hs

end VOA.Classification.COne.PlusRat3
