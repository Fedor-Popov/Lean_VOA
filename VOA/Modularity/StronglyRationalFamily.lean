/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.ConformalWeightChoice
import VOA.Modularity.FamilyIndexing
import VOA.Modules.ZhuVermaAnArchLUBijectionPBW
import VOA.Modules.ZhuBottomSimple

/-!
# The canonical family of irreducible modules

Once `Φ W` is finite, it itself is the correct index type for Zhu modularity.  This file chooses a
representative of each quotient class and discharges the family cardinality, conformal-weight and
bottom-separation inputs.  Zhu semisimplicity and the PBW universal-module construction (theorem
`VOA.pbw`) also discharge bottom simplicity.
-/

namespace VOA

open VHat VHat.DLM3

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱}

/-- A chosen representative of an irreducible ordinary-module isomorphism class. -/
noncomputable def canonicalIrrModule (c : Φ W) : IrrModule W := Quotient.out c

@[simp] theorem canonicalIrrModule_toΦ (c : Φ W) : (canonicalIrrModule c).toΦ = c :=
  Quotient.out_eq c

/-- The chosen representative equipped with its canonical conformal weight. -/
noncomputable def canonicalIrrLWModule (c : Φ W) : LWModule W where
  carrier := (canonicalIrrModule c).carrier
  isMod := (canonicalIrrModule c).isMod
  h := conformalWeightOf (canonicalIrrModule c)
  isLow := (hasConformalWeight_conformalWeightOf (canonicalIrrModule c)).2
  realized := (hasConformalWeight_conformalWeightOf (canonicalIrrModule c)).1

@[simp] theorem canonicalIrrLWModule_isMod (c : Φ W) :
    (canonicalIrrLWModule c).isMod = (canonicalIrrModule c).isMod := rfl

theorem canonicalIrrLWModule_irreducible (c : Φ W) :
    (canonicalIrrLWModule c).IsIrreducibleLW :=
  (canonicalIrrModule c).irreducible

/-- The canonical family is irredundant and complete. -/
theorem canonicalIrrFamily_irredundant_complete :
    Irredundant (canonicalIrrModule (W := W)) ∧ Complete (canonicalIrrModule (W := W)) := by
  constructor
  · intro i j hij
    have : (canonicalIrrModule i).toΦ = (canonicalIrrModule j).toΦ := Quotient.sound hij
    simpa using this
  · intro V
    refine ⟨V.toΦ, ?_⟩
    exact Quotient.exact (canonicalIrrModule_toΦ (W := W) V.toΦ).symm

/-- With its canonical weight, every chosen representative satisfies `HasConformalWeight`. -/
theorem canonicalIrrFamily_hasConformalWeight :
    ∀ c : Φ W, HasConformalWeight (canonicalIrrModule c).isMod
      (conformalWeightOf (canonicalIrrModule c)) :=
  hasConformalWeight_family canonicalIrrModule

/-- The bottom of each canonical representative is simple when the Zhu algebra is semisimple. -/
theorem canonicalIrrFamily_bottomSimple
    (hss : letI := instRingA W; IsSemisimpleRing (A W)) :
    ∀ c : Φ W, IsSimpleAMod
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) c).2) := by
  intro c
  let P := canonicalIrrLWModule (W := W) c
  exact isSimpleAMod_of_irreducible_of_semisimple
    (voaPBWBottomProjection (parabolicRepOfAMod W (regularAMod W))) hss P
    (canonicalIrrLWModule_irreducible c)

/-- Distinct canonical representatives with the same conformal weight have non-isomorphic Zhu
bottoms.  This is the injective half of the PBW-based (theorem `VOA.pbw`) Zhu correspondence. -/
theorem canonicalIrrFamily_bottomSeparated {j k : Φ W} (hjk : j ≠ k)
    (_hw : conformalWeightOf (canonicalIrrModule j) =
      conformalWeightOf (canonicalIrrModule k)) :
    IsEmpty (AModEquiv W
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) j).2)
      (lowestAMod (canonicalIrrFamily_hasConformalWeight (W := W) k).2)) := by
  constructor
  intro e
  let Pj : IrrLWModule W :=
    ⟨canonicalIrrLWModule (W := W) j, canonicalIrrLWModule_irreducible j⟩
  let Pk : IrrLWModule W :=
    ⟨canonicalIrrLWModule (W := W) k, canonicalIrrLWModule_irreducible k⟩
  have hforward : forwardMapIrr W
      (Quotient.mk (IrrLWModule.setoid W) Pj) =
      forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pk) := by
    rw [forwardMapIrr_mk, forwardMapIrr_mk]
    exact Quotient.sound ⟨e⟩
  have hclasses := (zhuBijective_of_voaPBW W).1 hforward
  have hforget := congrArg (forgetClass W) hclasses
  apply hjk
  change (canonicalIrrModule j).toΦ = (canonicalIrrModule k).toΦ at hforget
  simpa using hforget

/-- The family-index cardinality input is tautological for the canonical `Φ W` family. -/
theorem canonicalIrrFamily_card [Fintype (Φ W)] :
    Fintype.card (Φ W) = Nat.card (Φ W) := by
  exact (Nat.card_eq_fintype_card : Nat.card (Φ W) = Fintype.card (Φ W)).symm

end VOA
