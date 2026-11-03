import VOA.Classification.COne.AdmissibleOrdinaryLevels

/-!
# Ordinary structures on irreducible C₂-cofinite admissible modules

The original weak action is preserved exactly. The DLM citation follows for
C₂-cofinite VOAs without using its rationality antecedent. ABD Corollary 5.8
then follows conditionally on the separate weak-to-admissible citation.
-/

namespace VOA.Classification.COne.AdmissibleOrdinary

open VOA.Huang.LogRemovalAdmissible

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
  {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- Reindex admissible levels by the injective map `j ↦ h + j`. -/
def shiftedWeight (N : AdmissibleModule W M) (h α : ℂ) : Submodule ℂ M :=
  ⨆ (j : ℤ) (_ : h + (j : ℂ) = α), N.lev j

theorem shiftedWeight_at (N : AdmissibleModule W M) (h : ℂ) (j : ℤ) :
    shiftedWeight N h (h + (j : ℂ)) = N.lev j := by
  unfold shiftedWeight
  simp only [add_right_inj, Int.cast_inj]
  exact iSup_iSup_eq_left

theorem shiftedWeight_eq_bot (N : AdmissibleModule W M) (h α : ℂ)
    (hne : ∀ j : ℤ, h + (j : ℂ) ≠ α) : shiftedWeight N h α = ⊥ :=
  iSup_eq_bot.mpr (fun j => iSup_eq_bot.mpr (fun hj => (hne j hj).elim))

/-- A scalar conformal action on finite admissible levels gives an ordinary structure. -/
noncomputable def ordinaryOfLevelScalar (N : AdmissibleModule W M) (h : ℂ)
    (hfin : ∀ j, FiniteDimensional ℂ (N.lev j))
    (hscalar : ∀ (j : ℤ) (y : M), y ∈ N.lev j →
      L0 N.toWeakModule y = (h + (j : ℂ)) • y) : OrdVModule W M where
  toWeakModule := N.toWeakModule
  weight := shiftedWeight N h
  isInternal := by
    have hi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top N.lev).mp
      N.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨?_, ?_⟩
    · exact iSupIndep_extend N.lev (shiftedWeight N h) (fun j => h + (j : ℂ))
        (fun α hα => shiftedWeight_eq_bot N h α hα) (shiftedWeight_at N h) hi.1
    · rw [← hi.2]
      apply le_antisymm
      · exact iSup_le (fun α => iSup_le (fun j => iSup_le (fun _ => le_iSup N.lev j)))
      · exact iSup_le (fun j => le_iSup_of_le (h + (j : ℂ))
          (by rw [shiftedWeight_at]))
  L0_weight := by
    intro α y hy
    by_cases ha : ∃ j : ℤ, h + (j : ℂ) = α
    · obtain ⟨j, rfl⟩ := ha
      rw [shiftedWeight_at] at hy
      exact hscalar j y hy
    · rw [shiftedWeight_eq_bot N h α (not_exists.mp ha)] at hy
      have : y = 0 := hy
      simp [this]
  finrank := by
    intro α
    by_cases ha : ∃ j : ℤ, h + (j : ℂ) = α
    · obtain ⟨j, rfl⟩ := ha
      rw [shiftedWeight_at]
      exact hfin j
    · rw [shiftedWeight_eq_bot N h α (not_exists.mp ha)]
      infer_instance
  boundedBelow := by
    refine ⟨h.re, ?_⟩
    intro α hα
    by_cases ha : ∃ j : ℤ, h + (j : ℂ) = α
    · obtain ⟨j, rfl⟩ := ha
      rw [shiftedWeight_at] at hα
      have hj : 0 ≤ j := by
        by_contra hj
        exact hα (N.lev_eq_bot_of_neg j (lt_of_not_ge hj))
      simp only [Complex.add_re, Complex.intCast_re, le_add_iff_nonneg_right]
      exact_mod_cast hj
    · exact (hα (shiftedWeight_eq_bot N h α (not_exists.mp ha))).elim

/-- Every irreducible admissible module of a C₂-cofinite VOA is ordinary,
with exactly the given weak action. No rationality hypothesis is needed. -/
theorem irreducible_admissible_isOrdinary (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (hirr : N.IsIrreducible) :
    ∃ O : OrdVModule W M, O.toWeakModule = N.toWeakModule := by
  obtain ⟨h, hh⟩ := exists_level_scalar hC2 N hirr
  exact ⟨ordinaryOfLevelScalar N h (finiteDimensional_level hC2 N hirr) hh, rfl⟩

/-- In particular, the actual `L(0)` eigenspaces are finite-dimensional. -/
theorem finiteDimensional_eigenspace (hC2 : C2Cofinite W)
    (N : AdmissibleModule W M) (hirr : N.IsIrreducible) (α : ℂ) :
    FiniteDimensional ℂ ((L0 N.toWeakModule).eigenspace α) := by
  obtain ⟨O, hO⟩ := irreducible_admissible_isOrdinary hC2 N hirr
  have he : (L0 N.toWeakModule).eigenspace α = O.weight α := by
    rw [← hO]
    ext x
    exact ⟨fun hx => eigenvector_mem_weight O (Module.End.mem_eigenspace_iff.mp hx),
      fun hx => Module.End.mem_eigenspace_iff.mpr (O.L0_weight α x hx)⟩
  rw [he]
  exact O.finrank α

/-- DLM 8.1(c), on the C₂-cofinite locus; its rationality antecedent is unused. -/
theorem dlmSimpleAdmissibleOrdinary_of_c2Cofinite (hC2 : C2Cofinite W) :
    DLMSimpleAdmissibleOrdinary W := by
  intro _ M _ _ N hirr
  exact irreducible_admissible_isOrdinary hC2 N hirr

/-- The citation required by strongly rational consumers. -/
theorem dlmSimpleAdmissibleOrdinary_of_stronglyRational (hV : StronglyRational W) :
    DLMSimpleAdmissibleOrdinary W :=
  dlmSimpleAdmissibleOrdinary_of_c2Cofinite hV.c2Cofinite

/-- ABD 5.8 from ABD 5.7 and the proved admissible-to-ordinary step.
Unlike the previous library factorization, this requires no rationality. -/
theorem abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible (hWA : ABDWeakIsAdmissible W) :
    ABDIrreducibleWeakIsOrdinary W := by
  intro hC2 M _ _ A hA
  obtain ⟨N, rfl⟩ := hWA hC2 A
  exact irreducible_admissible_isOrdinary hC2 N hA

end VOA.Classification.COne.AdmissibleOrdinary
