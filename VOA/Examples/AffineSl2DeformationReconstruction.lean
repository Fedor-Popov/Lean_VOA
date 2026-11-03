/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2RigidityBasis
import VOA.Core.DeformationCurrentModes

/-!
# The concrete generated carrier for affine sl₂ at level −4/3

Current words span the universal affine algebra and continue to span its simple
quotient. Consequently the explicitly constructed first-order carrier always
surjects onto the simple quotient. Simplicity then turns separation of the pure
first-order vacuum into a coboundary, by an actual inverse linear map.

Separation is NOT proved here. In particular this file does not discharge
`RegularImpliesTrivialGraded L43`. The current commutator theorem is a proved
ingredient for a future universal-representation proof of that missing fact.
-/
namespace VOA.LQ43
open AffineVOA AffineLie AffineVOA.Inst Sl2Sing Deform.Reconstruction
local notation "kk" => (-4 / 3 : ℂ)
local notation "I" => QuotVOA.maxGradedIdeal voaSl2Adm

/-- All states of the simple affine quotient are generated from its vacuum by
weight-one modes. The proof transports current-word spanning through the quotient. -/
theorem L43_modeGenerating : ModeGenerating L43 (L43.grading 1 : Set _) := by
  intro S hvac _hgens hclosed
  have hword (l : List (Fin 3 × ℕ)) : (I).mkQ (wordStateA kk l) ∈ S := by
    induction l with
    | nil => simpa [wordStateA_nil, L43, QuotVOA.maxQuotientVOA,
        voaSl2Adm_vacuum] using hvac
    | cons an l ih =>
      have hc : (I).mkQ (currentState kk an.1) ∈ L43.grading 1 :=
        Submodule.mem_map.mpr ⟨_,
          currentState_mem_grading kk admLevel_noncritical an.1, rfl⟩
      have h := hclosed _ hc _ ih (-(an.2 : ℤ) - 1)
      change (QuotVOA.quotientVOA voaSl2Adm (I)
        (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
        (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm)).smul _ _ _ ∈ S at h
      rw [QuotVOA.quotientVOA_mkQ_smul (QuotVOA.maxGradedIdeal_isIdeal voaSl2Adm)
        (QuotVOA.maxGradedIdeal_isGradedIdeal voaSl2Adm), smul_currentState_adm] at h
      simpa only [wordStateA_cons] using h
  have hpre : S.comap (I).mkQ = ⊤ := by
    apply top_unique
    rw [← wordStateA_span kk]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact hword l
  apply top_unique
  intro x _
  obtain ⟨v, rfl⟩ := (I).mkQ_surjective x
  change v ∈ S.comap (I).mkQ
  rw [hpre]
  trivial

/-- The constructed carrier has every ordinary state as its constant term.
This requires no condition on the deformation, including no regularity condition. -/
theorem L43_generatedCarrier_surjective (D : Deform.FirstOrderDeformation L43) :
    Function.Surjective (reduction (generatedCarrier D (L43.grading 1 : Set _))) :=
  generatedCarrier_surjective D _ L43_modeGenerating

/-- The reconstruction conclusion with its still-open separation input exposed.
This is an intermediate reduction and must not be cited as affine rigidity. -/
theorem L43_isTrivial_of_generated_separation (D : Deform.FirstOrderDeformation L43)
    (hsep : (0, L43.vacuum) ∉ generatedCarrier D (L43.grading 1 : Set _)) : D.IsTrivial :=
  isTrivial_of_generated_separation D _ L43_isSimple L43_modeGenerating hsep

end VOA.LQ43
