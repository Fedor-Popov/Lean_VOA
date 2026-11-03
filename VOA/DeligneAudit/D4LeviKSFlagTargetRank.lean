import VOA.DeligneAudit.D4LeviKSFlagFiniteBox

/-! The corrected multiplicity count bounds the graded PAIR target image. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

noncomputable def ksFlagTargetHomogeneous (a b c d : ℕ) :
    Submodule ℂ (pairTargetSymmetric a b c) :=
  (homogeneousSubmodule (PairTarget a b c) ℂ d).comap
    (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The homogeneous target multiplicity image has the exact graded box bound. -/
theorem ksFlag_target_image_finrank_le (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    Module.finrank ℂ ((ksFlagTargetHomogeneous a b c d).map
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey))) ≤
      ksGradedBoxCount m a b c d := by
  apply (pairTarget_image_finrank_le_of_span ρ w m i a b c
    (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey)
    (ksFlagTargetHomogeneous a b c d) (ksFlagFiniteBox m a b c d) ?_).trans
      (ksFlagFiniteBox_card_le m a b c d)
  intro P hP
  exact (sup_le_sup_left (ksFlagMaximalRelationSpan_le_ker
    ρ w m i a b c d h hi hkey) _)
      (ksFlag_homogeneous_finite_span m a b c d P hP)

/-- The same target estimate in the corrected count attached to the final key. -/
theorem ksFlag_target_image_finrank_le_corrected
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    Module.finrank ℂ ((ksFlagTargetHomogeneous a b c d).map
      (pairTargetQuotientEvaluation ρ w m i a b c
        (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey))) ≤
      ksCorrectedBoxCount m (pairFinalKey a b c d) := by
  by_cases hsize : a + b + c ≤ m
  · rw [ksCorrectedBoxCount_pairFinalKey m a b c d hsize]
    exact ksFlag_target_image_finrank_le ρ w m i a b c d h hi hkey
  · rw [pairTargetQuotientEvaluation_eq_zero_of_overfull
      ρ w m i a b c d h hi hkey (by omega), Submodule.map_zero]
    simp

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksFlag_target_image_finrank_le
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_target_image_finrank_le_corrected
