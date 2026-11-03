import VOA.DeligneAudit.SL4TMixedRelativePresentation
import VOA.DeligneAudit.SL4TMixedSourceSurjective

/-! The mixed-ring surjection onto the relative symmetric source of the second Levi block. -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open MvPolynomial
attribute [local instance 2000] Fin.fintype Fin.instOfNat

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The mixed parameter tuple associated to the two Levi count vectors. -/
def mixedLabelBlockParams (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ) : MixedParams :=
  ⟨a, b, d 0, d 1, d 2, e₁, e₂⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The five elementary tails vanish before the relative quotient is taken. -/
theorem mixedElementarySource_elementary_tail (a b c : ℕ) (d : Fin 3 → ℕ)
    (e₁ e₂ : ℕ) (j : Fin 5) (s : ℕ) (hs : ![d 0, d 1, d 2, e₁, e₂] j < s) :
    mixedElementarySource a b c d e₁ e₂ (mixedE j s) = 0 := by
  rw [mixedE, mixedElementarySource_alphabet]
  fin_cases j
  · change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b c d 0 (elementary s)) = 0
    rw [radicalGrassmannianAlphabet_elementary_tail _ _ _ _ _ _ hs, map_zero]
  · change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b c d 1 (elementary s)) = 0
    rw [radicalGrassmannianAlphabet_elementary_tail _ _ _ _ _ _ hs, map_zero]
  · change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b c d 2 (elementary s)) = 0
    rw [radicalGrassmannianAlphabet_elementary_tail _ _ _ _ _ _ hs, map_zero]
  · apply Subtype.ext
    change (secondLeviElementaryAlphabet (B := RadicalGrassmannianRing a b c d)
      e₁ e₂ 0 (elementary s)).val = 0
    rw [secondLeviElementaryAlphabet_elementary]
    have hz : esymm (Fin e₁) (RadicalGrassmannianRing a b c d) s = 0 := by
      have hc : (Finset.univ : Finset (Fin e₁)).card < s := by simpa using hs
      simp only [esymm, Finset.powersetCard_eq_empty.mpr hc, Finset.sum_empty]
    simp [hz]
  · apply Subtype.ext
    change (secondLeviElementaryAlphabet (B := RadicalGrassmannianRing a b c d)
      e₁ e₂ 1 (elementary s)).val = 0
    rw [secondLeviElementaryAlphabet_elementary]
    have hz : esymm (Fin e₂) (RadicalGrassmannianRing a b c d) s = 0 := by
      have hc : (Finset.univ : Finset (Fin e₂)).card < s := by simpa using hs
      simp only [esymm, Finset.powersetCard_eq_empty.mpr hc, Finset.sum_empty]
    simp [hz]

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Every defining mixed relation belongs to the relative symmetric relation ideal. -/
theorem mixedElementarySource_ideal_le (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) :
    mixedIdeal (mixedLabelBlockParams a b d e₁ e₂) ≤
      (secondLeviRelativeIdeal e₁ e₂
        (fun j => (A3Sector.a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩).toNat)
        (radicalLeviPowerSum a b a d)).comap (mixedElementarySource a b a d e₁ e₂) := by
  rw [mixedIdeal, if_pos hv]
  apply Ideal.span_le.mpr
  intro P hP
  change mixedElementarySource a b a d e₁ e₂ P ∈
    secondLeviRelativeIdeal e₁ e₂
      (fun j => (A3Sector.a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩).toNat)
      (radicalLeviPowerSum a b a d)
  have hv' := hv
  simp only [MixedValid, mixedLabelBlockParams, mixedP, mixedQ] at hv'
  rcases hP with ⟨j, s, hs, rfl⟩ | ⟨s, hs, _, rfl⟩ | ⟨s, hs, _, rfl⟩ |
    ⟨s, hs, _, rfl⟩ | ⟨s, hs, ht, rfl⟩ | ⟨s, hs, ht, rfl⟩
  · rw [mixedElementarySource_elementary_tail _ _ _ _ _ _ _ _ (by
      simpa [mixedLengths, mixedLabelBlockParams] using hs)]
    exact Ideal.zero_mem _
  · rw [mixedH, mixedElementarySource_alphabet]
    change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b a d 0 (complete s)) ∈ _
    rw [radicalGrassmannianAlphabet_complete_tail _ _ _ _ _ _ (by
      simp only [mixedLabelBlockParams] at hs
      simp only [A3Sector.weightABC, Fin.isValue, Matrix.cons_val_zero]
      omega), map_zero]
    exact Ideal.zero_mem _
  · rw [mixedH, mixedElementarySource_alphabet]
    change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b a d 1 (complete s)) ∈ _
    rw [radicalGrassmannianAlphabet_complete_tail _ _ _ _ _ _ (by
      simp only [mixedLabelBlockParams] at hs
      change b - d 1 < s
      omega), map_zero]
    exact Ideal.zero_mem _
  · rw [mixedH, mixedElementarySource_alphabet]
    change secondLeviSymmetricBase e₁ e₂
      (radicalGrassmannianAlphabet a b a d 2 (complete s)) ∈ _
    rw [radicalGrassmannianAlphabet_complete_tail _ _ _ _ _ _ (by
      simp only [mixedLabelBlockParams] at hs
      change a - d 2 < s
      omega), map_zero]
    exact Ideal.zero_mem _
  · have hr : secondLeviRelativeGenerator e₁ e₂ 0 (radicalLeviPowerSum a b a d 0) s ∈
        secondLeviRelativeIdeal e₁ e₂
          (fun j => (A3Sector.a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩).toNat)
          (radicalLeviPowerSum a b a d) := by
      apply Ideal.subset_span
      refine ⟨0, s, ?_, ?_, rfl⟩
      all_goals
        simp only [mixedLabelBlockParams, mixedP] at hs ht
        simp only [A3Sector.a3KeyLabelInt, if_pos rfl, ite_true]
        omega
    rw [mixedElementarySource_firstRelative] at hr
    exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_neg_one.pow s)).mp hr
  · have hr : secondLeviRelativeGenerator e₁ e₂ 1 (radicalLeviPowerSum a b a d 1) s ∈
        secondLeviRelativeIdeal e₁ e₂
          (fun j => (A3Sector.a3KeyLabelInt b a j ⟨d 0, d 1, d 2, 0⟩).toNat)
          (radicalLeviPowerSum a b a d) := by
      apply Ideal.subset_span
      refine ⟨1, s, ?_, ?_, rfl⟩
      all_goals
        simp only [mixedLabelBlockParams, mixedQ] at hs ht
        simp only [A3Sector.a3KeyLabelInt, show (1 : Fin 2) ≠ 0 by decide, if_false]
        omega
    rw [mixedElementarySource_secondRelative] at hr
    exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_neg_one.pow s)).mp hr

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- The mixed multiplicity ring maps onto the relative symmetric-function quotient. -/
def mixedToRadicalRelative (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) :
    MixedRing (mixedLabelBlockParams a b d e₁ e₂) →ₐ[ℂ]
      RadicalSecondLeviRelativeRing a b a d e₁ e₂ :=
  Ideal.quotientMapₐ _ (mixedElementarySource a b a d e₁ e₂)
    (mixedElementarySource_ideal_le a b d e₁ e₂ hv)

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
theorem mixedToRadicalRelative_mk (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) (P : MixedPoly) :
    mixedToRadicalRelative a b d e₁ e₂ hv (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (mixedElementarySource a b a d e₁ e₂ P) := rfl

set_option synthInstance.maxHeartbeats 100000 in
-- Symmetric sources over nested quotient algebras need a larger synthesis budget.
/-- Surjectivity holds for every valid count tuple, without any dimension comparison. -/
theorem mixedToRadicalRelative_surjective (a b : ℕ) (d : Fin 3 → ℕ) (e₁ e₂ : ℕ)
    (hv : MixedValid (mixedLabelBlockParams a b d e₁ e₂)) :
    Function.Surjective (mixedToRadicalRelative a b d e₁ e₂ hv) := by
  intro x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ _ x
  obtain ⟨Q, rfl⟩ := mixedElementarySource_surjective a b a d e₁ e₂ P
  exact ⟨Ideal.Quotient.mk _ Q, rfl⟩

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_elementary_tail
#print axioms VOA.DeligneAudit.SL4T.mixedElementarySource_ideal_le
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_mk
#print axioms VOA.DeligneAudit.SL4T.mixedToRadicalRelative_surjective
