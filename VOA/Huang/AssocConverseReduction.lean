/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocConverseFinite
import VOA.Huang.PzTensorDecomp
import VOA.Classification.COne.ABDWeakAdmissibleComplete
import VOA.Classification.COne.AdmissibleOrdinaryBridge

/-!
# Converse associativity reduced to product-channel independence

This assembles the proved forward theorem without using the PBW theorem `VOA.pbw`: the displayed
complete finite family supplies finiteness of the irreducible
classes. The only residual beyond that family is injectivity of the actual product evaluation
map. In particular this is not an unconditional proof of `AssociativityConverse`.
-/

namespace VOA.Huang.AssocConverse

open VOA VOA.Huang.AssocTarget
open VOA.Classification.COne.ABDWeakAdmissible VOA.Classification.COne.AdmissibleOrdinary

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {ι : Type v}

/-- A complete finite family already supplies finiteness of `Φ W`; no PBW witness is used. -/
theorem finite_Φ_of_complete_family [Finite ι] (R : ι → LWModule W)
    (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j)) :
    Finite (Φ W) := by
  let F : ι → IrrModule W := fun j => ⟨(R j).carrier, (R j).isMod, iR j⟩
  apply Finite.of_surjective (fun j => (F j).toΦ)
  intro c
  obtain ⟨j, ⟨e⟩⟩ := hcomplete (canonicalIrrLWModule c) (canonicalIrrLWModule_irreducible c)
  refine ⟨j, ?_⟩
  have heq : (F j).toΦ = (canonicalIrrModule c).toΦ := Quotient.sound ⟨e.symm⟩
  exact heq.trans (canonicalIrrModule_toΦ c)

/-- The forward theorem with finiteness supplied by a displayed family. -/
theorem associativityInput_of_complete_family [Finite ι] (hV : StronglyRational W)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j)) :
    AssociativityInput W :=
  VOA.Huang.PzTensorDecomp.associativityInput_of_citations hV abdWeakIsAdmissible
    (abdIrreducibleWeakIsOrdinary_of_weakIsAdmissible abdWeakIsAdmissible)
    (finite_Φ_of_complete_family R iR hcomplete)

variable [Fintype ι]

/-- Strong rationality and a complete finite family reduce the requested converse to
product-channel independence. The forward identity and iterate upper bound are proved. -/
theorem associativityConverse_of_stronglyRational_faithful (hV : StronglyRational W)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j))
    (hfaith : ProductChannelFaithful hV R) : AssociativityConverse W :=
  associativityConverse_of_productChannelFaithful hV
    (associativityInput_of_complete_family hV R iR hcomplete) R iR hcomplete hfaith

/-- Both directions, with the same explicit residual. -/
theorem associativityBoth_of_stronglyRational_faithful (hV : StronglyRational W)
    (R : ι → LWModule W) (iR : ∀ j, (R j).IsIrreducibleLW)
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ j, LWModule.Iso W Q (R j))
    (hfaith : ProductChannelFaithful hV R) : AssociativityBoth W :=
  ⟨associativityInput_of_complete_family hV R iR hcomplete,
    associativityConverse_of_stronglyRational_faithful hV R iR hcomplete hfaith⟩

end VOA.Huang.AssocConverse
