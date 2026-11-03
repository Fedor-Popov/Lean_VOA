/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.SimpleQuotient
import VOA.DeligneAudit.A2CurrentJetSurjectivity
import VOA.Filtered.GeneratorCurrentLiSpanning

/-!
# Every Deligne case on the general simple affine VOA: two of the four capstone inputs

For a Deligne case `case`, Lie data `D` indexed by `Fin case.currentDimension` and a non-critical
level `k`, this file instantiates the higher-rank capstone on `W := L_k(𝔤) = simpleVOA D k hk`:

* `presentation case D k hk : CurrentC2Presentation case W` (ideal = full kernel, as for A₂);
* `currentJetSurjectivity case D k hk` — **discharged for every `𝔤`**: the current commutator gives
  the tracked estimate on `V^k(𝔤)` (`generatorModeTracked_of_current_comm`), current words span
  (`wordStateA_span`), and current-word spanning of Li's filtration descends to the maximal quotient;
* `classicallyFree_of_two_inputs`: each case rests only on `GeometricCarrierEmbedding` and
  `OrdinaryCarrierCharacter`.

This generalizes `VOA.DeligneAudit.A2.currentJetSurjectivity` from sl₃ to every `𝔤`.
-/

namespace VOA.AffineGeneral.Deligne

open VOA.AffineGeneral VOA.AffineGeneral.LieData VOA.DeligneHigherRankConditionalCapstone

noncomputable section

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤}
variable (case : HigherRankDeligneCase) (D : LieData κ (Fin case.currentDimension))
variable (k : ℂ) (hk : k + D.h ≠ 0)

/-- The universal current states. -/
abbrev ugen (a : Fin case.currentDimension) : Vacuum D k := currentState D k (D.generator a)

theorem smul_ugen (a : Fin case.currentDimension) (m : ℤ) (v : Vacuum D k) :
    (affineVOA D k hk).smul (ugen case D k a) m v = J D k a m v := by
  change mode (YA D k hk (J D k a (-1) (vacuumA D k))) m v = _
  rw [YA_current_state, mode_Jfield]

theorem genWordState_ugen (l : List (Fin case.currentDimension × ℕ)) :
    genWordState (affineVOA D k hk) (ugen case D k) (fun _ => 1) l = wordStateA D k l := by
  induction l with
  | nil => rfl
  | cons ar rest ih =>
      obtain ⟨a, r⟩ := ar
      rw [genWordState_cons, smul_ugen, ih, wordStateA_cons]

/-- Li's filtration of `V^k(𝔤)` is spanned by current words. -/
theorem universal_genWordsSpan :
    GeneratorWordsSpanLiFiltration (affineVOA D k hk) (ugen case D k) (fun _ => 1) := by
  apply generatorWordsSpanLiFiltration_of_tracked
  · exact generatorModeTracked_of_current_comm (J D k) (structureConstant D)
      (fun a b m => (m : ℂ) * k * formTable D a b) (smul_ugen case D k hk)
      (fun a b m p => by rw [current_comm]; rfl)
      (fun a m hm => J_vacuum_nonneg D k a hm)
  · rw [show genWordState (affineVOA D k hk) (ugen case D k) (fun _ => 1) = wordStateA D k from
      funext (genWordState_ugen case D k hk)]
    exact wordStateA_span D k

/-- The current generators of `L_k(𝔤)`. -/
def gen (a : Fin case.currentDimension) : Vacuum D k ⧸ maxIdeal D k hk :=
  simpleCurrentState D k hk (D.generator a)

theorem gen_weight_one (a : Fin case.currentDimension) : gen case D k hk a ∈ (simpleVOA D k hk).grading (1 : ℤ) :=
  simpleCurrentState_mem D k hk a

/-- The current-coordinate `C₂` presentation of `L_k(𝔤)` by the full kernel. -/
def presentation : CurrentC2Presentation case (simpleVOA D k hk) where
  gen := gen case D k hk
  gen_weight_one := gen_weight_one case D k hk
  ideal := RingHom.ker
    (MvPolynomial.aeval fun i =>
      liDegreeZeroClass (simpleVOA D k hk) 1 ⟨gen case D k hk i, gen_weight_one case D k hk i⟩).toRingHom
  relations := le_rfl

/-- Li's filtration of `L_k(𝔤)` is spanned by current words. -/
theorem genWordsSpan :
    GeneratorWordsSpanLiFiltration (simpleVOA D k hk) (presentation case D k hk).gen (fun _ => 1) :=
  generatorWordsSpanLiFiltration_quotient (QuotVOA.maxGradedIdeal (affineVOA D k hk))
    (QuotVOA.maxGradedIdeal_isIdeal _) (QuotVOA.maxGradedIdeal_isGradedIdeal _)
    (universal_genWordsSpan case D k hk)

/-- **`CurrentJetSurjectivity` for every Deligne case on `L_k(𝔤)`.** -/
theorem currentJetSurjectivity : CurrentJetSurjectivity case (simpleVOA D k hk) (presentation case D k hk) :=
  DeligneAudit.currentJetSurjectivity_of_genWordSpan (presentation case D k hk)
    (genWordsSpan case D k hk)

/-- **Each Deligne case on `L_k(𝔤)`, conditional on the two remaining packages.** -/
theorem classicallyFree_of_two_inputs
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding case (simpleVOA D k hk) (presentation case D k hk) Carrier)
    (hchar : OrdinaryCarrierCharacter (simpleVOA D k hk) Carrier) :
    CaseClassicallyFree case (simpleVOA D k hk) (presentation case D k hk) :=
  (caseClassicallyFree_of_explicit_inputs case (simpleVOA D k hk) (presentation case D k hk) Carrier
    (currentJetSurjectivity case D k hk) hgeom hchar).1

end

end VOA.AffineGeneral.Deligne
