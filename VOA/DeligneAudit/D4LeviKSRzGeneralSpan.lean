import VOA.DeligneAudit.D4LeviKSRzGeneralKernel

/-! The full graded span of general Rz orbit generators lies in the kernel. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def rzOrbitRelationSpan (a b k l s d : ℕ) :
    Submodule ℂ (pairTargetSymmetric a b (k + l)) :=
  Submodule.span ℂ {T | ∃ (α : Fin b ⊕ Fin a → ℕ)
      (β : Fin l → ℕ),
    ((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
        ((Finset.univ.toList : List (Fin l)).map β).sum + s = d ∧
      T = rzTargetGenerator a b k l s α β}

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rzOrbitRelationSpan_le_ker
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b k l s d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hk : 1 ≤ k) (hks : m + 1 ≤ k + s)
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b (k + l) d) :
    rzOrbitRelationSpan a b k l s d ≤
      (pairTargetQuotientEvaluation ρ w m i a b (k + l)
        (pairKernelPrefix_of_sat ρ w m i a b (k + l)
          d h hi hkey)).ker := by
  apply Submodule.span_le.mpr
  intro T hT
  obtain ⟨α, β, hdeg, rfl⟩ := hT
  have hkey' : keyEnum m ⟨i, hi⟩ =
      pairFinalKey a b (k + l)
        (((Finset.univ.toList : List (Fin b ⊕ Fin a)).map α).sum +
          ((Finset.univ.toList : List (Fin l)).map β).sum + s) := by
    rw [hdeg]
    exact hkey
  simpa [hdeg] using rzTargetGenerator_mem_ker ρ w m i a b k l s
    α β h hk hks hi hkey'

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.rzOrbitRelationSpan_le_ker
