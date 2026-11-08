import VOA.Moonshine.MoonshineCNNearOppositeIterate
import VOA.Moonshine.MoonshineCNMatterAdjointReduction

/-! Lie invariance of the bilinear form on the Monster Lie algebra, with no hypotheses.
The opposite iterate identity of the matter near-VOA is a theorem
(`NearVOA.oppositeIterateIdentity_of_locallyNilpotent`, fed the proved local nilpotence
`moonshineMatterVirasoroOne_locallyNilpotent`), so every matter field is adjoint to its
opposite field and the zero modes of weight-one primaries are skew-adjoint. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

/-- The opposite iterate identity of the actual matter near-VOA. -/
theorem moonshineMatterNearVOA_oppositeIterateIdentity :
    moonshineMatterNearVOA.OppositeIterateIdentity
      moonshineMatterVirasoroOne_locallyNilpotent :=
  moonshineMatterNearVOA.oppositeIterateIdentity_of_locallyNilpotent _

/-- Every actual matter field is adjoint to its opposite field for the matter form. -/
theorem moonshineMatterOppositeModes_adjoint (u : moonshineMatterSpace) (n : ℤ)
    (x y : moonshineMatterSpace) :
    moonshineMatterForm (mode (moonshineMatterNearVOA.Y u) n x) y =
      moonshineMatterForm x (moonshineMatterOppositeModes n u y) :=
  moonshineMatterOppositeModes_adjoint_of_iterate
    moonshineMatterNearVOA_oppositeIterateIdentity u n x y

/-- Zero modes of weight-one primaries are skew-adjoint for the matter form. -/
theorem moonshineMatterForm_primary_zeroMode_skew
    (a : moonshineMatterNearVOA.primaryWeightOne) (b c : moonshineMatterSpace) :
    moonshineMatterForm (moonshineMatterNearVOA.smul a 0 b) c =
      -moonshineMatterForm b (moonshineMatterNearVOA.smul a 0 c) := by
  have h := moonshineMatterOppositeModes_adjoint a 0 b c
  rw [moonshineMatterOppositeModes_primary, LinearMap.neg_apply, map_neg] at h
  exact h

/-- **Lie invariance of the Monster Lie algebra form**, with no hypotheses. -/
theorem monsterLieBilinearForm_invariant (u v w : monsterLieAlgebra) :
    monsterLieBilinearForm ⁅u, v⁆ w = monsterLieBilinearForm u ⁅v, w⁆ :=
  monsterLieBilinearForm_invariant_of_oppositeIterate
    moonshineMatterNearVOA_oppositeIterateIdentity u v w

end VOA.Moonshine.ConwayNorton
