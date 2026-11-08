/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNMonsterActionLift
import VOA.Moonshine.MoonshineCNFinalAudit

/-!
# The Conway–Norton conjecture for the elements of the Monster `AutO` that lift to `V♮`

`conwayNorton : ConwayNortonConjecture` holds for every automorphism of `V♮`.  Composed with the
lift `monsterLift : liftableSubgroup →* AutVnat` it becomes a statement about elements of Axiom's
Monster `AutO`: for every `g ∈ AutO` that lifts, the McKay–Thompson series of its (unique) action on
`V♮` is the normalised Hauptmodul of a genus-zero group containing some `Γ₀(N)`.  The first
coefficient is the trace of `g` on the rational Griess algebra `SpaceB`
(`mckayThompson_monsterLift_coeff_one`), so the series is attached to `g` itself, not to a choice.

Once every element of `AutO` is known to lift (for instance from liftable generators and a
generation theorem, `conwayNorton_autO_of_closure`), this is Conway–Norton for the whole Monster.

## Main results
* ⭐ `conwayNorton_liftable`, `conwayNortonVia_monsterLift`.
* `trace_griessConj` (`tr(griessConj g | V♮₂) = tr(g | SpaceB)`),
  ⭐ `mckayThompson_monsterLift_coeff_one`.
* `mckayThompsonFun_eq_of_restrict` (independence of the lift).
* ⭐ `conwayNorton_monster_of_isVnatLiftable` — Monster-language statement for one liftable `g`.
* ⭐ `conwayNorton_monster_of_liftable` (`ConwayNortonVia (monsterLiftOfAll hlift)`),
  ⭐ `conwayNorton_autO_of_closure`, ⭐ `conwayNorton_autO_of_generators` (`⟨Gvis ∪ {τ}⟩ = AutO`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.MonsterAction

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.ConwayNorton
open scoped TensorProduct

/-- ⭐ **Conway–Norton for every liftable element of the Monster.** -/
theorem conwayNorton_liftable (g : liftableSubgroup) : ConwayNortonFor (monsterLift g) :=
  conwayNorton (monsterLift g)

/-- The same through the fixed interface `ConwayNortonVia`. -/
theorem conwayNortonVia_monsterLift : ConwayNortonVia monsterLift :=
  fun g => conwayNorton_liftable g

/-! ## The first coefficient: the trace on the rational Griess algebra -/

/-- `tr(griessConj g | V♮₂) = tr(g | SpaceB)`: conjugation and base change preserve traces. -/
theorem trace_griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) :
    LinearMap.trace ℂ (VnatVOA.grading 2) (griessConj g).toLinearMap
      = ((LinearMap.trace ℚ SpaceB g.toLinearMap : ℚ) : ℂ) := by
  have hconj : (griessConj g).toLinearMap = griessIso.conj (griessBaseChange g).toLinearMap :=
    LinearMap.ext fun v => by rw [LinearEquiv.conj_apply_apply]; rfl
  rw [hconj, LinearMap.trace_conj', griessBaseChange, LinearEquiv.coe_baseChange,
    LinearMap.trace_baseChange, eq_ratCast]

/-- ⭐ **The `q`-coefficient of `T_g` is the trace of `g` on Axiom's Griess algebra**:
`coeff₁ (mckayThompson (monsterLift g)) = tr(g | SpaceB)` (a rational number). -/
theorem mckayThompson_monsterLift_coeff_one (g : liftableSubgroup) :
    PowerSeries.coeff 1 (mckayThompson (monsterLift g))
      = ((LinearMap.trace ℚ SpaceB ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB).toLinearMap : ℚ) : ℂ) := by
  rw [mckayThompson_coeff, ← trace_griessConj, ← monsterLift_restrict]
  rfl

/-- **The series does not depend on the lift**: any automorphism of `V♮` acting on `V♮₂` as
`griessConj g` has the McKay–Thompson function of `monsterLift g`. -/
theorem mckayThompsonFun_eq_of_restrict (g : liftableSubgroup) (h : AutVnat)
    (hh : vnatWeightTwoRestrict h = griessConj ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB)) :
    mckayThompsonFun h = mckayThompsonFun (monsterLift g) := by
  rw [monsterLift_unique g h hh]

/-- ⭐ **Conway–Norton in Monster language, for one liftable element**: if `g ∈ AutO` lifts, there is
a unique automorphism `h` of `V♮` acting on `V♮₂ ≅ ℂ ⊗ SpaceB` as `ℂ ⊗ g`; its McKay–Thompson series
has `q`-coefficient `tr(g | SpaceB)` and is the normalised Hauptmodul of a genus-zero group
`Γ ⊇ Γ₀(N)` commensurable with `SL₂(ℤ)`. -/
theorem conwayNorton_monster_of_isVnatLiftable (g : AutO) (hg : IsVnatLiftable g) :
    ∃ h : AutVnat, vnatWeightTwoRestrict h = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      (∀ h' : AutVnat, vnatWeightTwoRestrict h' = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) → h' = h) ∧
      PowerSeries.coeff 1 (mckayThompson h)
        = ((LinearMap.trace ℚ SpaceB (g : SpaceB ≃ₗ[ℚ] SpaceB).toLinearMap : ℚ) : ℂ) ∧
      ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
        IsNormalizedHauptmodul Γ (mckayThompsonFun h) := by
  have hmem : g ∈ liftableSubgroup := mem_liftableSubgroup.2 hg
  exact ⟨monsterLift ⟨g, hmem⟩, monsterLift_restrict ⟨g, hmem⟩,
    fun h' hh' => monsterLift_unique ⟨g, hmem⟩ h' hh',
    mckayThompson_monsterLift_coeff_one ⟨g, hmem⟩, conwayNorton_liftable ⟨g, hmem⟩⟩

/-! ## The whole Monster, once every element lifts -/

/-- ⭐ **Conway–Norton for the whole Monster `AutO`, given that every element lifts**:
`ConwayNortonVia (monsterLiftOfAll hlift)`, i.e. for every `g ∈ AutO` the McKay–Thompson series of
its action on `V♮` is a normalised Hauptmodul of a genus-zero group `Γ ⊇ Γ₀(N)`. -/
theorem conwayNorton_monster_of_liftable (hlift : ∀ g : AutO, IsVnatLiftable g) :
    ConwayNortonVia (monsterLiftOfAll hlift) :=
  fun g => conwayNorton (monsterLiftOfAll hlift g)

/-- ⭐ **Conway–Norton for `AutO` from liftable generators**: if every element of `S ⊆ AutO` lifts to
`V♮` and `S` generates `AutO`, then Conway–Norton holds for every element of `AutO` (through the
injective lift `monsterLiftOfAll`). -/
theorem conwayNorton_autO_of_closure {S : Set AutO} (hS : ∀ g ∈ S, IsVnatLiftable g)
    (hgen : Subgroup.closure S = ⊤) :
    ConwayNortonVia (monsterLiftOfAll (isVnatLiftable_of_closure_eq_top hS hgen)) :=
  conwayNorton_monster_of_liftable _

/-- ⭐ **Conway–Norton for `AutO` in the generator shape `⟨Gvis ∪ {τ}⟩ = AutO`**: if every element
of `Gvis` lifts, `τ` lifts, and `Gvis ∪ {τ}` generates `AutO` (`hGmat`, the generation theorem of
the CFSG port), then for every `g ∈ AutO` the McKay–Thompson series of its action on `V♮` is a
normalised Hauptmodul of a genus-zero group containing some `Γ₀(N)`. -/
theorem conwayNorton_autO_of_generators {Gvis : Set AutO} {τ : AutO}
    (hvis : ∀ g ∈ Gvis, IsVnatLiftable g) (hτ : IsVnatLiftable τ)
    (hGmat : Subgroup.closure (insert τ Gvis) = ⊤) (g : AutO) :
    ∃ h : AutVnat, vnatWeightTwoRestrict h = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
        IsNormalizedHauptmodul Γ (mckayThompsonFun h) := by
  have hg : g ∈ liftableSubgroup :=
    subgroupClosure_insert_le_liftable hvis hτ (hGmat ▸ Subgroup.mem_top g)
  exact ⟨monsterLift ⟨g, hg⟩, monsterLift_restrict ⟨g, hg⟩, conwayNorton_liftable ⟨g, hg⟩⟩

end VOA.Moonshine.MonsterAction
