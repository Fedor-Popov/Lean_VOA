import VOA.Classification.COne.PlusSplitGeneralized

/-!
# Integral generalized-weight blocks

The construction works for every VOA. Spectral decomposition is an explicit
hypothesis on the weak module (and is automatic for C₂-cofinite VOAs).
No admissible-level grading of a submodule is used.
Reference: Abe, https://arxiv.org/html/math/0311210, Lemma 2.3 and Proposition 2.4.
-/

set_option maxSynthPendingDepth 3

namespace VOA.Classification.COne.PlusSplitting

open PlusRational ABDWeakAdmissible VOA.Huang.LogRemovalAdmissible
universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Equality of conformal weights modulo integers. -/
def SameCoset (α β : ℂ) : Prop := ∃ z : ℤ, β = α + (z : ℂ)

theorem sameCoset_refl (α : ℂ) : SameCoset α α := ⟨0, by simp⟩

theorem sameCoset_trans {α β γ : ℂ} (h : SameCoset α β) (k : SameCoset β γ) :
    SameCoset α γ := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, rfl⟩ := k
  exact ⟨i + j, by push_cast; ring⟩

theorem sameCoset_symm {α β : ℂ} (h : SameCoset α β) : SameCoset β α := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨-i, by push_cast; ring⟩

/-- The sum of generalized eigenspaces with eigenvalues in a set. -/
noncomputable def spectralPart (A : WeakModule W M) (s : Set ℂ) : Submodule ℂ M :=
  ⨆ α ∈ s, (L0 A).maxGenEigenspace α

/-- Every integer-translation-stable set of generalized weights gives a mode submodule. -/
noncomputable def spectralSubmodule (A : WeakModule W M) (s : Set ℂ)
    (hs : ∀ α ∈ s, ∀ z : ℤ, α + (z : ℂ) ∈ s) : Submodule (modeAlg A) M :=
  toR A {
    carrier := spectralPart A s
    act_mem := by
      intro a p x hx
      have ha : a ∈ ⨆ w, W.grading w := by
        rw [W.isInternal.submodule_iSup_eq_top]; trivial
      refine Submodule.iSup_induction W.grading
        (motive := fun a => A.act a p x ∈ spectralPart A s) ha ?_ ?_ ?_
      · intro w a ha
        have hle : spectralPart A s ≤ (spectralPart A s).comap (mode (A.YM a) p) := by
          apply iSup_le
          intro α
          apply iSup_le
          intro hα y hy
          exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem
            (hs α hα (w - p - 1)) (mode_mem_maxGenEigenspace A ha p hy))
        exact hle hx
      · simpa [WeakModule.act] using (spectralPart A s).zero_mem
      · intro a b ha hb
        simpa [WeakModule.act, map_add] using (spectralPart A s).add_mem ha hb }

noncomputable def cosetBlock (A : WeakModule W M) (α : ℂ) : Submodule (modeAlg A) M :=
  spectralSubmodule A {β | SameCoset α β} (by
    intro β hβ z
    exact sameCoset_trans hβ ⟨z, rfl⟩)

noncomputable def otherCosets (A : WeakModule W M) (α : ℂ) : Submodule (modeAlg A) M :=
  spectralSubmodule A {β | ¬SameCoset α β} (by
    intro β hβ z h
    exact hβ (sameCoset_trans h ⟨-z, by push_cast; ring⟩))

/-- Distinct spectral sets are disjoint even without local finiteness. -/
theorem spectralPart_disjoint (A : WeakModule W M) {s t : Set ℂ}
    (h : Disjoint s t) : Disjoint (spectralPart A s) (spectralPart A t) :=
  ((L0 A).independent_genEigenspace ⊤).disjoint_biSup_biSup h

theorem cosetBlock_disjoint_otherCosets (A : WeakModule W M) (α : ℂ) :
    Disjoint (cosetBlock A α) (otherCosets A α) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  exact Submodule.disjoint_def.mp (spectralPart_disjoint A
    (s := {β | SameCoset α β}) (t := {β | ¬SameCoset α β})
    (Set.disjoint_left.mpr (fun _ h hn => hn h))) x hx hy

theorem cosetBlock_le_otherCosets (A : WeakModule W M) {α β : ℂ}
    (h : ¬SameCoset α β) : cosetBlock A α ≤ otherCosets A β := by
  change spectralPart A {γ | SameCoset α γ} ≤ spectralPart A {γ | ¬SameCoset β γ}
  apply iSup_le
  intro γ
  apply iSup_le
  intro hγ
  exact le_iSup_of_le γ (le_iSup_of_le
    (fun hβ => h (sameCoset_trans hγ (sameCoset_symm hβ))) le_rfl)

/-- Every invariant subspace splits across a coset and its complement. -/
theorem submodule_coset_decomposition (A : WeakModule W M)
    (hloc : ∀ x : M, ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, L0 A y ∈ S)
    (P : Submodule (modeAlg A) M) (α : ℂ) :
    P = (P ⊓ cosetBlock A α) ⊔ (P ⊓ otherCosets A α) := by
  apply le_antisymm
  · have hP := eq_iSup_inf_maxGenEigenspace_of_locally_finite (L0 A) hloc
      (P.restrictScalars ℂ) (fun y hy => P.smul_mem
        (⟨mode (A.YM W.conformalVector) 1,
          Algebra.subset_adjoin ⟨W.conformalVector, 1, rfl⟩⟩ : modeAlg A) hy)
    have hle : P.restrictScalars ℂ ≤
        ((P ⊓ cosetBlock A α) ⊔ (P ⊓ otherCosets A α)).restrictScalars ℂ := by
      rw [hP]
      apply iSup_le
      intro β x hx
      by_cases h : SameCoset α β
      · exact Submodule.mem_sup_left ⟨hx.1,
          Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem h hx.2)⟩
      · exact Submodule.mem_sup_right ⟨hx.1,
          Submodule.mem_iSup_of_mem β (Submodule.mem_iSup_of_mem h hx.2)⟩
    exact hle
  · exact sup_le inf_le_left inf_le_left

/-- A generalized conformal cyclic generator is supported in just one coset.
Thus different-coset factors cannot occur inside the cyclic modules of F2. -/
theorem cyclic_le_cosetBlock (A : WeakModule W M) (α : ℂ) (x : M)
    (hx : x ∈ (L0 A).maxGenEigenspace α) : cyclic A x ≤ cosetBlock A α := by
  apply Submodule.span_le.mpr
  apply Set.singleton_subset_iff.mpr
  exact Submodule.mem_iSup_of_mem α
    (Submodule.mem_iSup_of_mem (sameCoset_refl α) hx)

/-- Separation of two distinct cosets splits an interval. The support hypotheses
say that the two factors are images of their indicated spectral blocks.
This does not require either factor to be simple. -/
theorem relativeComplement_of_distinct_cosets (A : WeakModule W M)
    (hloc : ∀ x : M, ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ x ∈ S ∧
      ∀ y ∈ S, L0 A y ∈ S)
    {a b c : Submodule (modeAlg A) M} (hab : a ≤ b) (hbc : b ≤ c)
    (α β : ℂ) (hne : ¬SameCoset α β)
    (hba : b ≤ a ⊔ cosetBlock A α) (hcb : c ≤ b ⊔ cosetBlock A β) :
    ∃ d : Submodule (modeAlg A) M,
      a ≤ d ∧ d ≤ c ∧ b ⊓ d = a ∧ b ⊔ d = c := by
  have hsep : b ⊓ cosetBlock A β ≤ a := by
    intro x hx
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hba hx.1)
    rw [submodule_coset_decomposition A hloc a β] at hy
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hy
    have hzero : v + z = 0 := by
      apply Submodule.disjoint_def.mp (cosetBlock_disjoint_otherCosets A β)
      · have heq : v + z = x - u := by rw [← he, ← huv]; abel
        rw [heq]
        exact (cosetBlock A β).sub_mem hx.2 hu.2
      · exact (otherCosets A β).add_mem hv.2 (cosetBlock_le_otherCosets A hne hz)
    have hxu : x = u := by rw [← he, ← huv, add_assoc, hzero, add_zero]
    exact hxu ▸ hu.1
  refine ⟨a ⊔ (c ⊓ cosetBlock A β), le_sup_left,
    sup_le (hab.trans hbc) inf_le_left, ?_, ?_⟩
  · rw [inf_comm, sup_inf_assoc_of_le _ hab]
    apply le_antisymm
    · exact sup_le le_rfl (fun x hx => hsep ⟨hx.2, hx.1.2⟩)
    · exact le_sup_left
  · rw [← sup_assoc, sup_eq_left.mpr hab, inf_comm c,
      ← sup_inf_assoc_of_le _ hbc, inf_eq_right.mpr hcb]

end VOA.Classification.COne.PlusSplitting
