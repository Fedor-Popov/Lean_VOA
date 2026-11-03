import VOA.DeligneAudit.D4FusionToroidalFinite
import VOA.DeligneAudit.D4FusionToroidalStarPresentation

/-! The toroidal presentation criterion with universal finiteness discharged. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The existential part of `ToroidalPresentation`. -/
def ToroidalPresentation' (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∃ (P : Type) (hA : AddCommGroup P),
    letI : AddCommGroup P := hA
    ∃ (hM : Module ℂ P),
      letI : Module ℂ P := hM
      ∃ (hFD : FiniteDimensional ℂ P),
        letI : FiniteDimensional ℂ P := hFD
        ∃ (ρP : ToroidalModule D4sector.f m P) (p : P),
          Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
            wordOpT ρP l p) = ⊤ ∧
          ∃ (ψ : P →ₗ[ℂ] Gr D4sector.f (ravFam D4sector m 0) m),
            ψ p = grGenerator D4sector.f (ravFam D4sector m 0) m ∧
            (∀ c i s x, ψ (ρP.op c i s x) =
              (grToroidal_D4 m hm).op c i s (ψ x)) ∧
            ∃ (χ : P →ₗ[ℂ]
                FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m)),
              χ p = D4Fusion.gradedHighest m ∧
              (∀ c i s x, χ (ρP.op c i s x) =
                (D4Fusion.gradedAction m).op c i s (χ x)) ∧
              Module.finrank ℂ P ≤ 29 ^ m

theorem toroidalPresentation_of' (m : ℕ) (hm : 1 ≤ m)
    (h : ToroidalPresentation' m hm) : ToroidalPresentation m hm :=
  ⟨rav_finiteDimensional m hm, h⟩

theorem fusionTotalDimG_of_presentations'
    (h : ∀ m, (hm : 1 ≤ m) → ToroidalPresentation' m hm) :
    FiniteG.FusionTotalDimG D4sector :=
  fusionTotalDimG_of_presentations
    (fun m hm => toroidalPresentation_of' m hm (h m hm))

theorem D4_classicallyFree_of_presentations'
    (h : ∀ m, (hm : 1 ≤ m) → ToroidalPresentation' m hm)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4_classicallyFree_of_presentations
    (fun m hm => toroidalPresentation_of' m hm (h m hm)) hD

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.toroidalPresentation_of'
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_presentations'
#print axioms VOA.DeligneAudit.Toroidal.D4_classicallyFree_of_presentations'
