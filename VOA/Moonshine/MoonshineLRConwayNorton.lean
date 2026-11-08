import VOA.Moonshine.MoonshineLRNontrivial
import VOA.Moonshine.MoonshineLRHecke
import VOA.Moonshine.MoonshineCNGenusZeroMain

/-!
# Conway–Norton from complete replicability and finite order

`conwayNorton_of_completelyReplicable_of_families` (the genus-zero theorem) takes the
prime Hecke identity and non-injectivity modulo translations for every replicable family as
hypotheses. `ReplicableFamily_primeHeckeIdentity` and
`ReplicableFamily_notInjectiveModTranslations` discharge both, unconditionally. What remains for
the Conway–Norton conjecture is exactly
* `hfin : ∀ g : AutVnat, IsOfFinOrder g`, and
* `hrep : CompletelyReplicable`.
-/

namespace VOA.Moonshine.ConwayNorton.M8

open AutMonster

/-- **The Conway–Norton conjecture from finite order and complete replicability.** The prime Hecke
identity and non-injectivity modulo translations are proved for every replicable family. -/
theorem conwayNorton_of_finOrder_of_completelyReplicable
    (hfin : ∀ g : AutVnat, IsOfFinOrder g) (hrep : CompletelyReplicable) :
    ConwayNortonConjecture :=
  conwayNorton_of_completelyReplicable_of_families hfin hrep
    (fun _ F k => ReplicableFamily_primeHeckeIdentity F k)
    (fun _ hN F _ => ReplicableFamily_notInjectiveModTranslations hN F)

end VOA.Moonshine.ConwayNorton.M8
