/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2CurrentJetSurjectivity

/-!
# The character input reduces to a lower bound

`OrdinaryCarrierCharacter W Carrier` asks for *equality* of the ordinary carrier character with
the VOA character.  In the presence of the two other packages this equality is equivalent to the
lower bound

  `∀ N, ∑_{p ≤ N} dim Carrier p N ≤ dim W_N`,

because current-jet surjectivity and the injective dual carrier map already give, in every
Li/conformal bidegree, `dim gr^Li_{p,N} W ≤ dim Source_{p,N} ≤ dim Carrier p N`, and the Li layers
sum to `dim W_N` (`sum_liWeightLayer_finrank_eq_grading`).

So the only genuinely new character information is the lower bound `CarrierLowerBound`.  This file
proves the reduction generically (any case, any VOA), restates the capstone with the weaker
hypothesis, and specializes it to A₂, where `CurrentJetSurjectivity` is already discharged.

No new mathematics about `L_{-3/2}(sl₃)` is proved here.  For A₂ the lower bound is, by the paper's
carrier identity, `dim L_{-3/2}(sl₃)_N ≥ [q^N] ∏_{r ≥ 1} (1+q^r)^8` (`KacWakimotoLowerBound`; in the
literature, the Kac–Wakimoto admissible character formula).  It is proved in Lean via the AK
MLDE:
`A2.kacWakimotoLowerBound_of_productMLDE A2.a2ProductMLDE`.
-/

namespace VOA.DeligneAudit

open VertexOperatorAlgebra VOA.DeligneHigherRankConditionalCapstone

noncomputable section

universe uV uC

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {case : HigherRankDeligneCase} {W : VertexOperatorAlgebra V}

/-- The **lower half** of the ordinary character identity: the carrier character is bounded by
the VOA character in every conformal weight. -/
def CarrierCharacterLowerBound (W : VertexOperatorAlgebra V)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)] : Prop :=
  ∀ N,
    (∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N)) ≤
      Module.finrank ℂ (W.grading N)

/-- The reverse inequality `dim W_N ≤ ∑_p dim Carrier p N` holds unconditionally once current-jet
surjectivity and the geometric carrier embedding are available. -/
theorem finrank_grading_le_carrier_sum
    (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier) (N : ℕ) :
    Module.finrank ℂ (W.grading N) ≤
      ∑ p ∈ Finset.range (N + 1), Module.finrank ℂ (Carrier p N) := by
  rw [← sum_liWeightLayer_finrank_eq_grading W N]
  refine Finset.sum_le_sum fun p _ => ?_
  letI : FiniteDimensional ℂ
      (FiniteJet.PresentedJetLiBidegreeImage
        (fun _ : Fin case.currentDimension => 1) p p N P.ideal) :=
    FiniteJet.finiteDimensional_presentedJetLiBidegreeImage
      (fun _ : Fin case.currentDimension => 1) (fun _ => by simp) p p N P.ideal
  calc
    Module.finrank ℂ (liWeightLayer W p N)
        ≤ Module.finrank ℂ
            (FiniteJet.PresentedJetLiBidegreeImage
              (fun _ : Fin case.currentDimension => 1) p p N P.ideal) :=
          LinearMap.finrank_le_finrank_of_surjective (hsurj.bidegree p N)
    _ = Module.finrank ℂ (Module.Dual ℂ
            (FiniteJet.PresentedJetLiBidegreeImage
              (fun _ : Fin case.currentDimension => 1) p p N P.ideal)) :=
          (Subspace.dual_finrank_eq).symm
    _ ≤ Module.finrank ℂ (Carrier p N) :=
          LinearMap.finrank_le_finrank_of_injective (hgeom.injective p N)

/-- **Equality from the lower bound.**  Given the other two packages, the carrier lower bound
already implies the ordinary character identity required by the capstone. -/
theorem ordinaryCarrierCharacter_of_le
    (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier)
    (hlow : CarrierCharacterLowerBound W Carrier) :
    OrdinaryCarrierCharacter W Carrier := fun N =>
  le_antisymm (hlow N) (finrank_grading_le_carrier_sum P Carrier hsurj hgeom N)

/-- Conversely the capstone's character equality gives the lower bound; the two hypotheses are
equivalent in the presence of the other packages. -/
theorem carrierCharacterLowerBound_of_ordinary
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hchar : OrdinaryCarrierCharacter W Carrier) :
    CarrierCharacterLowerBound W Carrier := fun N => (hchar N).le

/-- **The higher-rank capstone with the character input weakened to a lower bound.** -/
theorem caseClassicallyFree_of_lowerBound
    (P : CurrentC2Presentation case W)
    (Carrier : ℕ → ℕ → Type uC)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hsurj : CurrentJetSurjectivity case W P)
    (hgeom : GeometricCarrierEmbedding case W P Carrier)
    (hlow : CarrierCharacterLowerBound W Carrier) :
    CaseClassicallyFree case W P ∧
      RingHom.ker
          (MvPolynomial.aeval fun i =>
            liDegreeZeroClass W 1 ⟨P.gen i, P.gen_weight_one i⟩).toRingHom =
        P.ideal :=
  caseClassicallyFree_of_explicit_inputs case W P Carrier hsurj hgeom
    (ordinaryCarrierCharacter_of_le P Carrier hsurj hgeom hlow)

namespace A2

/-- **A₂, conditional on the geometric carrier embedding and the carrier lower bound only.**
`CurrentJetSurjectivity` is discharged (`A2.currentJetSurjectivity`). -/
theorem classicallyFree_of_lowerBound
    (Carrier : ℕ → ℕ → Type)
    [∀ p N, AddCommGroup (Carrier p N)]
    [∀ p N, Module ℂ (Carrier p N)]
    [∀ p N, FiniteDimensional ℂ (Carrier p N)]
    (hgeom : GeometricCarrierEmbedding .A2 A2.W presentation Carrier)
    (hlow : CarrierCharacterLowerBound A2.W Carrier) :
    CaseClassicallyFree .A2 A2.W presentation :=
  (caseClassicallyFree_of_lowerBound presentation Carrier currentJetSurjectivity hgeom hlow).1

end A2

end

end VOA.DeligneAudit

section AxiomAudit
#print axioms VOA.DeligneAudit.finrank_grading_le_carrier_sum
#print axioms VOA.DeligneAudit.ordinaryCarrierCharacter_of_le
#print axioms VOA.DeligneAudit.caseClassicallyFree_of_lowerBound
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_lowerBound
end AxiomAudit
