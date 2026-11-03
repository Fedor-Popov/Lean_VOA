import VOA.DeligneAudit.D4FusionToroidalPresentedEigRank

/-! The corrected presentation is a quotient of the earlier presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

theorem JT_mono_syntax {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) (m : ℕ)
    {S S' : Set (FreeT n)} (h : S ⊆ S') : JT f m S ≤ JT f m S' := by
  apply Submodule.span_mono
  rintro z ⟨p, hcomm | hhigh | ⟨q, hq, rfl⟩⟩
  · exact ⟨p, Or.inl hcomm⟩
  · exact ⟨p, Or.inr (Or.inl hhigh)⟩
  · exact ⟨p, Or.inr (Or.inr ⟨q, h hq, rfl⟩)⟩

def PT_to_PTE (m : ℕ) : PT m →ₗ[ℂ] PTE m :=
  (JT D4sector.f m (JprimeSyntax m)).liftQ
    (JT D4sector.f m (JprimeSyntaxE m)).mkQ
    (by
      rw [Submodule.ker_mkQ]
      exact JT_mono_syntax D4sector.f m (Set.subset_union_left))

theorem PT_to_PTE_surjective (m : ℕ) : Function.Surjective (PT_to_PTE m) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (JT D4sector.f m (JprimeSyntaxE m)) y
  refine ⟨Submodule.Quotient.mk z, ?_⟩
  exact Submodule.liftQ_apply _ _ _

theorem PTE_of_PT (m : ℕ) (hm : 1 ≤ m)
    (h : PresentedRankBound m hm) : PresentedRankBoundE m hm := by
  letI : FiniteDimensional ℂ (PT m) := h.1
  have hs := PT_to_PTE_surjective m
  haveI : FiniteDimensional ℂ (PTE m) :=
    FiniteDimensional.of_surjective (PT_to_PTE m) hs
  exact ⟨inferInstance,
    (LinearMap.finrank_le_finrank_of_surjective hs).trans h.2⟩

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.PTE_of_PT
