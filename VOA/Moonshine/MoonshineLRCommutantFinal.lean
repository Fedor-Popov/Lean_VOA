import VOA.Moonshine.MoonshineLRCommutant4
import VOA.Moonshine.MoonshineCNRationalGriess

/-!
# The commutant of the generated Monster on the rational Griess space

Every `ℚ`-linear endomorphism of `SpaceB` commuting with `Generated.Gmat` is `a · 1 + b · P₀`, where
`P₀ = griessUnitProj` is the `bform`-orthogonal projection onto the line of `e₁ = (I, 0, 0)`.
This discharges `MonsterAction.GmatCommutantScalar`; with it, the restriction-to-weight-two map is
a group isomorphism from `AutVnat` onto the liftable subgroup of `AutO`, with no hypotheses.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA.Moonshine.AutMonster VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction

/-- The identity-line vector of the coordinate proof is `griessIdentityVec`. -/
theorem commutF_eOne_eq_griessIdentityVec : commutF_eOne = griessIdentityVec := rfl

/-- The identity-line projection of the coordinate proof is `griessUnitProj`. -/
theorem commutF_P₀_eq_griessUnitProj : commutF_P₀ = griessUnitProj := by
  apply LinearMap.ext
  intro u
  rw [commutF_P₀_apply, griessUnitProj_apply, commutF_eOne_eq_griessIdentityVec]

/-- **The commutant lemma.** Every `ℚ`-linear map commuting with `Generated.Gmat` is a
combination of the identity and the projection onto the identity line. -/
theorem gmatCommutantScalar : GmatCommutantScalar := by
  intro T hT
  obtain ⟨a, b, h⟩ := commutF_commutant_Gmat T hT
  exact ⟨a, b, by rw [h, commutF_P₀_eq_griessUnitProj]⟩

/-- `AutVnat` is isomorphic to the liftable subgroup of `AutO`, with no hypotheses. -/
noncomputable def autVnat_mulEquiv_liftable : AutVnat ≃* liftableSubgroup :=
  autVnat_mulEquiv_liftable_of_commutant gmatCommutantScalar

/-- The inverse of `autVnat_mulEquiv_liftable` is `monsterLift`. -/
theorem autVnat_mulEquiv_liftable_symm_apply (g : liftableSubgroup) :
    autVnat_mulEquiv_liftable.symm g = monsterLift g :=
  autVnat_mulEquiv_liftable_of_commutant_symm_apply gmatCommutantScalar g

end VOA.Moonshine.ConwayNorton.M8
