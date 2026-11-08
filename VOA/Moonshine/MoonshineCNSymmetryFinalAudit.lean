import VOA.Moonshine.MoonshineLRCommutantFinal
import VOA.Moonshine.MoonshineCNMonsterFinalAudit
import VOA.Moonshine.MoonshineCNRationalGriess

/-!
# Final audit: the symmetry group of the moonshine module

Coordinator audit for the converse direction. Every automorphism of `V♮` acts on the Griess algebra
`V♮₂ ≅ ℂ ⊗ SpaceB` through a rational automorphism of AxiomMath's algebra `SpaceB`, and the
resulting map identifies `Aut V♮` with the subgroup of AxiomMath's Monster `AutO` consisting of the
elements that act on `V♮`. That subgroup contains AxiomMath's generated group `Gmat`; with
AxiomMath's generation theorem `Gmat = AutO` (kept as an explicit hypothesis) it is all of `AutO`.

The proof combines the absolutely irreducible action of `Gmat` on the 196883-dimensional part of
`V♮₂` (`M8.gmatCommutantScalar`), the rationality of all traces (`ConwayNorton.rationalTraces`,
itself a consequence of the moonshine theorem) and Schur's span formula; Tits' theorem is not used.
-/

namespace VOA.Moonshine.ConwayNorton

open VOA.Moonshine.AutMonster VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.GriessDictionary

/-- Every automorphism of `V♮` is rational on the Griess algebra: it maps the rational form
`griessNat (SpaceB)` into itself. No hypotheses. -/
theorem autVnat_rational (h : AutVnat) (u : SpaceB) :
    ∃ u' : SpaceB, h (griessNat u : Vnat) = griessNat u' :=
  autVnat_rational_of_commutant M8.gmatCommutantScalar h u

/-- `Aut V♮` is isomorphic to the subgroup of AxiomMath's Monster consisting of the elements that
act on `V♮`; the isomorphism is inverse to `monsterLift`. No hypotheses. -/
theorem nonempty_autVnat_mulEquiv_liftable : Nonempty (AutVnat ≃* liftableSubgroup) :=
  ⟨M8.autVnat_mulEquiv_liftable⟩

/-- `Aut V♮` is isomorphic to AxiomMath's Monster `AutO`, given only AxiomMath's generation
theorem `Gmat = AutO`. -/
theorem autVnat_mulEquiv_autO (hGmat : Generated.Gmat = AutO) : Nonempty (AutVnat ≃* AutO) :=
  autVnat_mulEquiv_autO_of_commutant_of_Gmat M8.gmatCommutantScalar hGmat

end VOA.Moonshine.ConwayNorton

#print axioms VOA.Moonshine.ConwayNorton.autVnat_rational
#print axioms VOA.Moonshine.ConwayNorton.nonempty_autVnat_mulEquiv_liftable
#print axioms VOA.Moonshine.ConwayNorton.autVnat_mulEquiv_autO
#print axioms VOA.Moonshine.ConwayNorton.M8.gmatCommutantScalar
#print axioms VOA.Moonshine.ConwayNorton.M8.autVnat_mulEquiv_liftable
#print axioms VOA.Moonshine.ConwayNorton.rationalTraces
#print axioms VOA.Moonshine.ConwayNorton.conwayNorton
#print axioms VOA.Moonshine.ConwayNorton.conwayNorton_gmat
