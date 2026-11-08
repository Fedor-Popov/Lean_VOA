import VOA.Moonshine.MoonshineLRLiftVisible2
import VOA.Moonshine.MoonshineCNMonsterActionMoonshine

/-!
# Conway–Norton for the Monster, given only `τ_B` and `Gmat = AutO`

`conwayNorton_autO_of_generators` needs liftability of every element of the visible group
`Gvis`, liftability of `τ_B`, and `⟨τ_B, Gvis⟩ = AutO`. The theorem `liftVisRAllVisible` supplies
liftability of `Gvis`; `conwayNorton_autO_of_tauB` then needs only liftability of `τ_B` and the
generation equality.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction VOA.Moonshine.MonsterGriess.Visible

/-- The visible group, as a subset of `AutO`. -/
def visibleSetAutO : Set AutO := {g | (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Gvis}

/-- **Every element of the visible group is liftable.** -/
theorem isVnatLiftable_of_mem_visibleSetAutO : ∀ g ∈ visibleSetAutO, IsVnatLiftable g :=
  fun g hg => liftVisRAllVisible (g : SpaceB ≃ₗ[ℚ] SpaceB) hg

/-- **Conway–Norton for every element of the Monster `AutO`**, given that `τ` is liftable and that
`τ` together with the visible group generates `AutO` (CFSG's `Gmat = AutO`). -/
theorem conwayNorton_autO_of_tauB {τ : AutO} (hτ : IsVnatLiftable τ)
    (hGmat : Subgroup.closure (insert τ visibleSetAutO) = ⊤) (g : AutO) :
    ∃ h : AutVnat, vnatWeightTwoRestrict h = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
        IsNormalizedHauptmodul Γ (mckayThompsonFun h) :=
  conwayNorton_autO_of_generators isVnatLiftable_of_mem_visibleSetAutO hτ hGmat g

end VOA.Moonshine.ConwayNorton.M8
