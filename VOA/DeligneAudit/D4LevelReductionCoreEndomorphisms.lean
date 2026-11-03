import VOA.DeligneAudit.D4LevelReductionCoreCoverRelations

/-!
The core rank problem reduces to modules with a commuting Grassmannian action.
The finite coefficient cover supplies that action without assuming that it descends to every
cyclic quotient. All parameters are arbitrary nonnegative integers.
-/

namespace VOA.DeligneAudit.D4LevelReduction

noncomputable section

open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A coefficient-ring action commuting with the currents and extending the bottom map. -/
structure CoreCoefficientAction (Q : CurrentModule A3Sector.bracketTable V)
    (a b c : ℕ) (π : CoreBaseRing a b c →ₗ[ℂ] V) where
  action : CoreBaseRing a b c →ₐ[ℂ] Module.End ℂ V
  commute : ∀ σ e r, Commute (action σ) (Q.op e r)
  unit : ∀ σ, action σ (π 1) = π σ

/-- Every finite core has a finite cyclic cover with a commuting coefficient action. -/
def coreCoverCoefficientAction (a b c : ℕ)
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V)
    (h : CoreCartanAction Q a b c π) :
    CoreCoefficientAction (coreCoverCurrent a b c Q π) a b c (coreCoverMap a b c Q π h) where
  action := coreCoverAction a b c Q π h
  commute := coreCoverAction_commute a b c Q π h
  unit := coreCoverAction_unit a b c Q π h

/-- The core rank estimate restricted to modules with a commuting coefficient action. -/
def CoefficientCoreRankBound (a b c : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Q : CurrentModule A3Sector.bracketTable V) (π : CoreBaseRing a b c →ₗ[ℂ] V),
    CoreRelations Q a b c π → cycSubG Q (π 1) = ⊤ →
    (∀ e r, a + b + c ≤ r → Q.op e r = 0) → CoreCoefficientAction Q a b c π →
    Module.finrank ℂ V ≤ levelTarget (a + b + c) b (2 * a + b)

/-- Proving the bound with a commuting coefficient action suffices for the original core. -/
theorem truncatedCoreRankBound_of_coefficientBound (a b c : ℕ)
    (hbound : CoefficientCoreRankBound a b c) : TruncatedCoreRankBound a b c := by
  intro V _ _ _ Q π h hcyclic hhigh
  haveI := coreCoefficientSpan_finite a b c Q π
  have hb := hbound (coreCoefficientSpan a b c Q π) (coreCoverCurrent a b c Q π)
    (coreCoverMap a b c Q π h.cartan) (coreCoverMap_relations a b c Q π h)
    (coreCoverMap_cyclic a b c Q π h.cartan) (coreCoverCurrent_high a b c Q π hhigh)
    (coreCoverCoefficientAction a b c Q π h.cartan)
  exact (LinearMap.finrank_le_finrank_of_surjective
    (coreCoverEvaluation_surjective a b c Q π hcyclic)).trans hb

/-- Adding the commuting coefficient action does not change the rank problem. -/
theorem truncatedCoreRankBound_iff_coefficientBound (a b c : ℕ) :
    TruncatedCoreRankBound a b c ↔ CoefficientCoreRankBound a b c := by
  constructor
  · intro h V _ _ _ Q π hr hc ht _
    exact h V Q π hr hc ht
  · exact truncatedCoreRankBound_of_coefficientBound a b c

end

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.coreCoverCoefficientAction
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedCoreRankBound_of_coefficientBound
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedCoreRankBound_iff_coefficientBound
