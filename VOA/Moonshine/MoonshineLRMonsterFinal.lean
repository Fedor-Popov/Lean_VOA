import VOA.Moonshine.MoonshineLRTauB
import VOA.Moonshine.MonsterGriess.ProductInvariance

/-!
# Conway–Norton for every element of the Monster, given only `Gmat = AutO`

`tauB_mem_AutO` (no hypotheses) discharges the remaining hypothesis of
`tauBLift_conwayNorton_autO_of_Gmat`. What remains is CFSG's `Gmat = AutO`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction

/-- **The triality generator `τ_B` is liftable**, with no hypotheses. -/
theorem isVnatLiftable_tauB : IsVnatLiftable ⟨tauB, tauB_mem_AutO⟩ :=
  tauBLift_isVnatLiftable_tauB_of_mem_AutO tauB_mem_AutO

/-- **Conway–Norton for every element of the Monster `AutO`**, given only CFSG's `Gmat = AutO`:
every `g : AutO` is the restriction to `V♮₂` of some `h : AutVnat` whose McKay–Thompson series is a
normalised Hauptmodul for a moonshine group. -/
theorem conwayNorton_monster_of_Gmat (hGmat : Generated.Gmat = AutO) (g : AutO) :
    ∃ h : AutVnat, vnatWeightTwoRestrict h = griessConj (g : SpaceB ≃ₗ[ℚ] SpaceB) ∧
      ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
        IsNormalizedHauptmodul Γ (mckayThompsonFun h) :=
  tauBLift_conwayNorton_autO_of_Gmat tauB_mem_AutO hGmat g

end VOA.Moonshine.ConwayNorton.M8
