import VOA.DeligneAudit.D4LeviKSKeyWordShape
import VOA.DeligneAudit.D4LeviKSCorrectedUniv

/-! The homogeneous PAIR target bound controls the actual key-layer quotient. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Exact-key radical words land in the homogeneous PAIR target image. -/
theorem ksKey_image_le_target_image (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    (keyLayer ρ w (pairFinalKey a b c d)).map (keyPrefix ρ w m i).mkQ ≤
      (ksFlagTargetHomogeneous a b c d).map
        (pairTargetQuotientEvaluation ρ w m i a b c
          (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey)) := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro v ⟨l, hl, rfl⟩
  obtain ⟨P, hdP, hP⟩ := ksPair_key_word_symmetric_lift ρ w a b c d l hl
  refine ⟨pairSymmetricRestriction a b c P, ?_, ?_⟩
  · change (pairRestriction a b c (P : MvPolynomial (PairSource a b c) ℂ)).IsHomogeneous d
    exact hdP.rename_isHomogeneous
  · rw [pairTargetQuotientEvaluation_comp]
    change (keyPrefix ρ w m i).mkQ (xyzEvaluation ρ w (pairSourceShape a b c) P) = _
    rw [hP]

/-- The finite target box also gives a finite spanning set for its quotient image. -/
theorem ksFlag_target_image_le_box_span (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    let q := pairTargetQuotientEvaluation ρ w m i a b c
      (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey)
    (ksFlagTargetHomogeneous a b c d).map q ≤
      Submodule.span ℂ (q '' (ksFlagFiniteBox m a b c d : Set _)) := by
  classical
  intro q v hv
  obtain ⟨P, hP, rfl⟩ := hv
  obtain ⟨B, hB, C, hC, heq⟩ := Submodule.mem_sup.mp
    (ksFlag_homogeneous_finite_span m a b c d P hP)
  have hzero : q C = 0 :=
    ksFlagMaximalRelationSpan_le_ker ρ w m i a b c d h hi hkey hC
  rw [← heq, map_add, hzero, add_zero]
  have hh : q B ∈ (Submodule.span ℂ (ksFlagFiniteBox m a b c d : Set _)).map q :=
    ⟨B, hB, rfl⟩
  simpa only [Submodule.map_span, Finset.coe_image] using hh

/-- The key quotient and the image under the prefix quotient map have equal rank. -/
theorem ksKey_quot_finrank_eq_image (F S : Submodule ℂ V) :
    Module.finrank ℂ (S ⧸ F.comap S.subtype) = Module.finrank ℂ (S.map F.mkQ) := by
  let f : S →ₗ[ℂ] V ⧸ F := F.mkQ.comp S.subtype
  have hker : LinearMap.ker f = F.comap S.subtype := by
    simp [f, LinearMap.ker_comp]
  have hrange : LinearMap.range f = S.map F.mkQ := by
    simp [f, LinearMap.range_comp, Submodule.range_subtype]
  let e : (S ⧸ F.comap S.subtype) ≃ₗ[ℂ] LinearMap.range f :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans f.quotKerEquivRange
  rw [← hrange]
  exact e.finrank_eq

/-- The supported-key multiplicity bound, including overfull symmetric shapes. -/
theorem ksKey_quot_finrank_le_corrected (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c d : ℕ) (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c d) :
    Module.finrank ℂ
      (keyLayer ρ w (pairFinalKey a b c d) ⧸ (keyPrefix ρ w m i).comap
        (keyLayer ρ w (pairFinalKey a b c d)).subtype) ≤
      ksCorrectedBoxCount m (pairFinalKey a b c d) := by
  classical
  rw [ksKey_quot_finrank_eq_image]
  have himage := ksKey_image_le_target_image ρ w m i a b c d h hi hkey
  by_cases hsize : a + b + c ≤ m
  · let q := pairTargetQuotientEvaluation ρ w m i a b c
      (pairKernelPrefix_of_sat ρ w m i a b c d h hi hkey)
    let B : Finset (V ⧸ keyPrefix ρ w m i) := (ksFlagFiniteBox m a b c d).image q
    have hspan : (keyLayer ρ w (pairFinalKey a b c d)).map (keyPrefix ρ w m i).mkQ ≤
        Submodule.span ℂ (B : Set _) :=
      by simpa only [B, Finset.coe_image] using
        himage.trans (ksFlag_target_image_le_box_span ρ w m i a b c d h hi hkey)
    haveI : FiniteDimensional ℂ
        (Submodule.span ℂ (B : Set (V ⧸ keyPrefix ρ w m i))) :=
      FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet B)
    rw [ksCorrectedBoxCount_pairFinalKey m a b c d hsize]
    exact (Submodule.finrank_mono hspan).trans
      ((finrank_span_finset_le_card (R := ℂ) (s := B)).trans
        (Finset.card_image_le.trans (ksFlagFiniteBox_card_le m a b c d)))
  · rw [pairTargetQuotientEvaluation_eq_zero_of_overfull
      ρ w m i a b c d h hi hkey (by omega), Submodule.map_zero] at himage
    rw [eq_bot_iff.mpr himage]
    simp

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksKey_image_le_target_image
#print axioms VOA.DeligneAudit.D4Levi.ksFlag_target_image_le_box_span
#print axioms VOA.DeligneAudit.D4Levi.ksKey_quot_finrank_eq_image
#print axioms VOA.DeligneAudit.D4Levi.ksKey_quot_finrank_le_corrected
