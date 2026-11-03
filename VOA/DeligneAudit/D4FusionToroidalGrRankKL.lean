import VOA.DeligneAudit.D4FusionToroidalGrRank

/-! The KL input package after the generic graded-rank theorem. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The remaining KL target data at one multiplicity, without G2. -/
def KLCoreTarget (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∃ (F : Type) (hA : AddCommGroup F),
    letI : AddCommGroup F := hA
    ∃ (hM : Module ℂ F),
      letI : Module ℂ F := hM
      ∃ (hFD : FiniteDimensional ℂ F),
        letI : FiniteDimensional ℂ F := hFD
        KLTarget m hm F

/-- KL-F and the target data imply all fields of `KLInputs`; G2 is proved. -/
theorem kLInputs_of_core (m : ℕ) (hm : 1 ≤ m)
    (hF : DemazureUnivRank) (hE : KLCoreTarget m hm) : KLInputs m hm := by
  obtain ⟨hfd, hrank⟩ := hF m hm
  letI : FiniteDimensional ℂ (UModG D4sector.f (ravFam D4sector m 0)) := hfd
  exact ⟨hfd, gr_finiteDimensional D4sector.f (ravFam D4sector m 0) m hm,
    gr_finrank_le D4sector.f (ravFam D4sector m 0) m hm, hrank, hE⟩

/-- The fusion total-rank bound from KL-F and the remaining target data. -/
theorem fusionTotalDimG_of_KLCore (hF : DemazureUnivRank)
    (hE : ∀ m, (hm : 1 ≤ m) → KLCoreTarget m hm) :
    FiniteG.FusionTotalDimG D4sector := by
  apply fusionTotalDimG_of_KLInputs
  intro m hm
  exact kLInputs_of_core m hm hF (hE m hm)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.kLInputs_of_core
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_KLCore
