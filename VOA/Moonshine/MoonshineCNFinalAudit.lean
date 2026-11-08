import VOA.Moonshine.MoonshineLRConwayNortonFinal
import VOA.Moonshine.MoonshineCNStatement

/-!
# Final audit of the Conway–Norton conjecture

Coordinator audit, independent of the contributors' audit files: the fixed statement
`VOA.Moonshine.ConwayNorton.ConwayNortonConjecture` (from `MoonshineCNStatement`, unchanged since it was
fixed) holds, and the proof uses only the standard axioms.
-/

namespace VOA.Moonshine.ConwayNorton

/-- The Conway–Norton (Monstrous Moonshine) conjecture for `Aut V♮`, with no hypotheses. -/
theorem conwayNorton : ConwayNortonConjecture :=
  M8.conwayNortonConjecture_holds

example : ConwayNortonConjecture := conwayNorton

/-- The unfolded statement: for every automorphism `g` of `V♮`, the McKay–Thompson series of `g` is the
normalized Hauptmodul of a genus-zero group containing some `Γ₀(N)` and commensurable with `SL₂(ℤ)`. -/
example (g : AutMonster.AutVnat) : ∃ (Γ : Subgroup (GL (Fin 2) ℝ)) (N : ℕ), IsMoonshineGroup Γ N ∧
    IsNormalizedHauptmodul Γ (mckayThompsonFun g) :=
  conwayNorton g

end VOA.Moonshine.ConwayNorton

#print axioms VOA.Moonshine.ConwayNorton.conwayNorton
#print axioms VOA.Moonshine.ConwayNorton.M8.conwayNortonConjecture_holds
#print axioms VOA.Moonshine.ConwayNorton.M8.monsterLieSimpleRootGeneration
#print axioms VOA.Moonshine.ConwayNorton.M8.autVnat_isOfFinOrder
