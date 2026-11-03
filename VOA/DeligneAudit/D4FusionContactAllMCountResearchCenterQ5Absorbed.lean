import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterQ5Slice
import VOA.DeligneAudit.D4FusionContactAllMCountResearchCenterStaticPolarAll

/-! The quintic pivot is absorbed. The static polynomial orbit(5,2,2,2) is a
combination of degree-5 cube words with bit counts (2,2,2), all of which are
certified static templates; hence the single remaining element Q5 of the
quintic slice lies in the literal quadratic/cubic polar ideal J23 for every m,
and the candidate slice is exactly the slice of the powers-2..4 polar ideal.
The kernel check below only verifies that every word of the compiled orbit
row has the template shape; no rank or count is asserted. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
open VOA.DeligneAudit.D4FusionContact.Polynomial
open Cube (polarRangeIdeal quadraticCubicPolarIdeal)
open Cube.CenterStaticPolar (QuinticShape quintic_static_coeff_mem actual_word_prod
  currentMap_wordEval)
open Cube.QuarticReducedRows
noncomputable section

/-- Every word of the compiled quintic orbit row is a quintic template word. -/
theorem quinticOrbitRow_shape :
    ∀ x ∈ Cube.QuarticReduced.orbitRow 5 2 2 2, QuinticShape x.1 := by decide +kernel

/-- Signed static quintic template words lie in J23, for every m. -/
theorem actual_quintic_word_mem (m : ℕ) (w : List (Fin 8)) (hw : QuinticShape w) :
    PowerSeries.coeff (2 * m - 3) ((w.map (Cube.actualCurrent m)).prod) ∈
      quadraticCubicPolarIdeal m := by
  rw [actual_word_prod,PowerSeries.coeff_smul]
  exact Submodule.smul_of_tower_mem _ _ (quintic_static_coeff_mem m w hw)

/-- The quintic pivot Q5 already lies in J23, for every m. -/
theorem quinticStaticPolar_mem_polarIdeal (m : ℕ) :
    quinticStaticPolar m ∈ quadraticCubicPolarIdeal m := by
  have hrow := quinticOrbitRow_shape
  unfold quinticStaticPolar
  rw [← Cube.QuarticReduced.orbitRow_eval ℂ 5 2 2 2]
  generalize Cube.QuarticReduced.orbitRow 5 2 2 2 = row at hrow ⊢
  induction row with
  | nil => simp [eval]
  | cons x row ih =>
      rw [eval_cons,map_add,map_add]
      refine Ideal.add_mem _ ?_ (ih (fun y hy => hrow y (List.mem_cons_of_mem _ hy)))
      rw [map_zsmul,map_zsmul,currentMap_wordEval]
      exact zsmul_mem (actual_quintic_word_mem m x.1 (hrow x List.mem_cons_self)) _

/-- The candidate quintic slice is exactly the slice of the powers-2..4 polar ideal. -/
theorem candidate_quintic_slice_eq_polarRange (m : ℕ) (hm : 2 ≤ m) :
    (AllM.candidateIdeal m).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) =
    (polarRangeIdeal m 4).restrictScalars ℂ ⊓
      MvPolynomial.weightedHomogeneousSubmodule ℂ (colorComponentWeight m)
        (quinticColorDegree m) := by
  rw [candidate_quintic_slice_eq_Q5_sup_polarRange m hm]
  congr 1
  apply sup_eq_right.mpr
  rw [Submodule.span_le,Set.singleton_subset_iff]
  exact Cube.quadraticCubicPolarIdeal_le_polarRange m 4 (by norm_num)
    (quinticStaticPolar_mem_polarIdeal m)

end
#print axioms quinticOrbitRow_shape
#print axioms quinticStaticPolar_mem_polarIdeal
#print axioms candidate_quintic_slice_eq_polarRange
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.LeviRules
