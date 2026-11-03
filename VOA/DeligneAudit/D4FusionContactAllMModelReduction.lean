import VOA.DeligneAudit.D4FusionContactAllMFinite
import VOA.DeligneAudit.D4FusionContactZero
import VOA.DeligneAudit.D4FusionContactOne
import VOA.DeligneAudit.D4FusionContactTwo
import VOA.DeligneAudit.D4FusionKernelTheta
import VOA.DeligneAudit.DeligneFusionFiniteGD4

/-! The D4 total-bound input reduced to commutative algebra. `AllM.Model m`
is the explicit quotient of the polynomial ring in the 9m current-mode
variables by the original candidate differential ideal and the proved
high-word cutoff. It maps onto the associated graded of every local-Weyl
module, so a bound on its dimension for m >= 3 gives `FusionTotalDimG D4sector`
(m = 0, 1, 2 are already proved). No count, presentation or completeness
premise is introduced; `ModelBound m` itself is open (not proved here) for m >= 3. -/
namespace VOA.DeligneAudit.D4FusionContact
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.D4
open Polynomial

noncomputable section

/-- The residual commutative statement: the explicit model has dimension at most 28^m. -/
def ModelBound (m : ℕ) : Prop := Module.finrank ℂ (AllM.Model m) ≤ 28 ^ m

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {R : CurrentModule D4sector.f V} {w : V}

/-- A model bound gives the total bound of every local-Weyl module of that multiplicity. -/
theorem localWeyl_total_dim_of_modelBound {m : ℕ} (hm : 1 ≤ m) (hQ : ModelBound m)
    (h : LocalWeylRelG D4sector R w m) (B : ℕ) :
    ∑ d ∈ Finset.range B, Module.finrank ℂ (cycDeg R w d) ≤ 28 ^ m := by
  have hU := univ_localWeylRelG D4sector m
  obtain ⟨-,hsum⟩ := source_degree_bound_of_surjective_model (lwSpec D4sector m)
    (highestRel_of_localWeyl hU) (AllM.modelMap hm hU) (AllM.modelMap_surjective hm hU)
    ((localWeylRelG_iff D4sector R w m).mp h)
  exact (hsum B).trans hQ

/-- The named D4 total-dimension input follows from the model bounds for m >= 3. -/
theorem fusionTotalDimG_of_modelBound (hQ : ∀ m, 3 ≤ m → ModelBound m) :
    FiniteG.FusionTotalDimG D4sector := by
  intro m V _ _ R w h B
  match m, h with
  | 0, h => simpa using localWeyl_zero_total_dim h B
  | 1, h => simpa using localWeyl_one_total_dim h B
  | 2, h => simpa using localWeyl_two_total_dim h B
  | m + 3, h => exact localWeyl_total_dim_of_modelBound (by omega) (hQ (m + 3) (by omega)) h B

/-- D4 classical freeness from the commutative model bounds and the realizations. -/
theorem D4_classicallyFree_of_modelBound (hQ : ∀ m, 3 ≤ m → ModelBound m)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  d4_classicallyFree_of_totalBound
    (FiniteG.D4.d4_fusionTotalBoundG_of_dim (fusionTotalDimG_of_modelBound hQ)) hD

end
#print axioms localWeyl_total_dim_of_modelBound
#print axioms fusionTotalDimG_of_modelBound
#print axioms D4_classicallyFree_of_modelBound
end VOA.DeligneAudit.D4FusionContact
