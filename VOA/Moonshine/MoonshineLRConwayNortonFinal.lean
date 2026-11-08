import VOA.Moonshine.MoonshineLRGenerationMonster
import VOA.Moonshine.MoonshineLRFinOrderRigid

/-!
# The Conway–Norton conjecture

`conwayNorton_of_isOfFinOrder` uses the simple-root generation theorem
`monsterLieSimpleRootGeneration` and needs only finite order of every automorphism of `V♮`.
The theorem `autVnat_isOfFinOrder` supplies this remaining input.
-/

namespace VOA.Moonshine.ConwayNorton.M8

/-- **The Conway–Norton conjecture**, with no hypotheses. -/
theorem conwayNortonConjecture_holds : ConwayNortonConjecture :=
  conwayNorton_of_isOfFinOrder autVnat_isOfFinOrder

end VOA.Moonshine.ConwayNorton.M8
