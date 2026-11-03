import VOA.Classification.COne.OrbPos11Irreducible
import VOA.Classification.COne.OrbPos11Identity
import VOA.Classification.COne.OrbPos11Projections

/-! # The exact remaining analytic identity for the sector dictionary

The residual below specifies the original action's coefficients, carrier and
denominator. It asks only for twisted Jacobi. Support, truncation, vacuum,
grading, irreducibility and the U-module identification are already proved.
Neither this residual nor the sector-projection residual is asserted here.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbPos11
open VOA VOA.Huang.FusionUnit VOA.Huang.TensorCat VOA.Huang.HKLRational
open CategoryTheory MonoidalCategory OrbPos9 OrbPos10 OrbPos2

/-- An actual irreducible twisted realization gives the unchanged sector
interface, including its separate ordinary alternative at the identity. -/
theorem sectorRealization_of_twisted
    (G : Subgroup (Aut (V2m 1 le_rfl))) (X : Ordinary (orbifoldVOA G))
    (g : G) {N : ℕ} (hN : 0 < N) (ho : orderOf g.1 = N)
    (T : TwistedModule g.1 N X.carrier) (hi : TwistedIrreducible T)
    (e : ModuleEquiv (orbifoldVOA G) X.isMod (orbifoldRestriction G g T hN)) :
    SectorRealization G X := by
  by_cases hg : g = 1
  · subst g
    have hn : N = 1 := by simpa using ho.symm
    clear ho
    subst N
    refine Or.inl ⟨X.carrier, inferInstance, inferInstance,
      identityTwistedOrdinary T, identityTwistedOrdinary_irreducible T hi, ⟨?_⟩⟩
    refine { toLinearEquiv := e.toLinearEquiv, map_act := ?_ }
    intro v k x
    have he := e.map_act v k x
    change e.toLinearEquiv (mode (X.isMod.YM v) k x) =
      mode (restrictedFields T (orbifold G) v) k (e.toLinearEquiv x) at he
    rw [mode_restrictedFields] at he
    change e.toLinearEquiv (mode (X.isMod.YM v) k x) =
      mode ((identityTwistedOrdinary T).YM v.1) k (e.toLinearEquiv x)
    simpa only [identityTwistedOrdinary_mode, Nat.cast_one, one_mul] using he
  · refine Or.inr ⟨g, N, hN, ho, ?_, X.carrier, inferInstance, inferInstance, T, hi, ⟨e⟩⟩
    intro h
    exact hg (Subtype.ext h)

/-- OPEN: McRae's analytic-to-formal step, specialized to simple actions of
the pinned V₂ algebra. This is an identity on explicitly defined modes, with
no unspecified module, equivalence, support or irreducibility witness. -/
def ExceptionalActionTwistedJacobi : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    ∀ (hSR : StronglyRational (orbifoldVOA G)) (E : CanonicalExtensionAlgebra G hSR),
      letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
      letI := E.monoid
      ∀ (Q : SimpleAction (ambient G)) (g : G),
        ActionMonodromyThrough G hSR Q.obj Q.act g →
          TwistedJacobi g.1 (orderOf g.1) (actionModes G hSR Q.obj Q.act (orderOf g.1))

/-- The entire monodromy-to-sector dictionary follows from the single remaining
twisted Jacobi identity for the given action. -/
theorem exceptionalMonodromySectorDictionary_of_jacobi
    (hJ : ExceptionalActionTwistedJacobi) : ExceptionalMonodromySectorDictionary := by
  intro G hG hSR E Q g hm
  letI := monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hSR) hSR
  letI := E.monoid
  have hn := (exceptional_element_order_bounds hG g).1
  have hj := hJ G hG hSR E Q g hm
  exact sectorRealization_of_twisted G Q.obj g hn rfl
    (actionTwistedModule G hSR E Q.obj Q.act Q.laws g hm hn hj)
    (actionTwistedModule_irreducible G hSR E Q g hm hn (pow_orderOf_eq_one _) hj)
    (actionTwistedModule_restriction G hSR E Q.obj Q.act Q.laws g hm hn hj)

/-- Conditional assembly to the unchanged simple-action target. -/
theorem exceptionalSimpleActionTwisted_of_projections_jacobi
    (hP : ExceptionalSectorProjections) (hJ : ExceptionalActionTwistedJacobi) :
    ExceptionalSimpleActionTwisted :=
  exceptionalSimpleActionTwisted_of_monodromy_dictionary
    (exceptionalSimpleActionMonodromy_of_projections hP)
    (exceptionalMonodromySectorDictionary_of_jacobi hJ)

/-- Conditional B5 endpoint with exactly the two still-open obligations. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_projections_jacobi
    (hP : ExceptionalSectorProjections) (hJ : ExceptionalActionTwistedJacobi) :
    ExceptionalOrbifoldPositiveWeightsFact :=
  exceptionalOrbifoldPositiveWeightsFact_of_simpleActionTwisted
    (exceptionalSimpleActionTwisted_of_projections_jacobi hP hJ)

end VOA.Classification.COne.OrbPos11
