import VOA.DeligneAudit.D4FusionToroidalPresentedEigMaps

/-! Consequences of a finite rank bound for the corrected presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

def PresentedRankBoundE (m : ℕ) (_hm : 1 ≤ m) : Prop :=
  FiniteDimensional ℂ (PTE m) ∧ Module.finrank ℂ (PTE m) ≤ 29 ^ m

theorem toroidalPresentation'_of_presentedRankBoundE (m : ℕ) (hm : 1 ≤ m)
    (h : PresentedRankBoundE m hm) : ToroidalPresentation' m hm := by
  letI : FiniteDimensional ℂ (PTE m) := h.1
  exact ⟨PTE m, inferInstance, inferInstance, h.1, ρPTE m, pTE m,
    PTE_cyclic m, ψPTE m hm, ψPTE_gen m hm, ψPTE_op m hm,
    χPTE m hm, χPTE_gen m hm, χPTE_op m hm, h.2⟩

theorem fusionTotalDimG_of_presentedRankBoundE
    (h : ∀ m, (hm : 1 ≤ m) → PresentedRankBoundE m hm) :
    FiniteG.FusionTotalDimG D4sector :=
  fusionTotalDimG_of_presentations'
    (fun m hm => toroidalPresentation'_of_presentedRankBoundE m hm (h m hm))

theorem D4_classicallyFree_of_presentedRankBoundE
    (h : ∀ m, (hm : 1 ≤ m) → PresentedRankBoundE m hm)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4_classicallyFree_of_presentations'
    (fun m hm => toroidalPresentation'_of_presentedRankBoundE m hm (h m hm)) hD

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.toroidalPresentation'_of_presentedRankBoundE
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_presentedRankBoundE
#print axioms VOA.DeligneAudit.Toroidal.D4_classicallyFree_of_presentedRankBoundE
