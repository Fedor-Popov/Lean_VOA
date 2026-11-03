import VOA.DeligneAudit.D4FusionToroidalStarModel
import VOA.DeligneAudit.D4FusionToroidalStarCyclic

/-! The presentation criterion for the toroidal symbol lemma. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

private abbrev U (m : ℕ) := UModG D4sector.f (ravFam D4sector m 0)
private abbrev G (m : ℕ) := Gr D4sector.f (ravFam D4sector m 0) m
private abbrev F (m : ℕ) :=
  FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m)

theorem symbolLemma_of_presentation (m : ℕ) (hm : 1 ≤ m)
    (P : Type) [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P]
    (ρP : ToroidalModule D4sector.f m P) (p : P)
    (_hcyc : Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
      wordOpT ρP l p) = ⊤)
    (ψ : P →ₗ[ℂ] G m) (hψgen : ψ p = grGenerator D4sector.f
      (ravFam D4sector m 0) m)
    (hψeq : ∀ c i s x, ψ (ρP.op c i s x) =
      (grToroidal_D4 m hm).op c i s (ψ x))
    (χ : P →ₗ[ℂ] F m) (hχgen : χ p = D4Fusion.gradedHighest m)
    (hχeq : ∀ c i s x, χ (ρP.op c i s x) =
      (D4Fusion.gradedAction m).op c i s (χ x))
    (hP : Module.finrank ℂ P ≤ 29 ^ m) [FiniteDimensional ℂ (U m)] :
    SymbolLemma m hm ∧ Module.finrank ℂ (U m) ≤ 29 ^ m := by
  letI : FiniteDimensional ℂ (G m) :=
    gr_finiteDimensional D4sector.f (ravFam D4sector m 0) m hm
  letI : FiniteDimensional ℂ (F m) :=
    (D4Fusion.graded_total_rank_bound m).1
  have hψword : ∀ l : List (TLtr 28),
      ψ (wordOpT ρP l p) =
        wordOpT (grToroidal_D4 m hm) l
          (grGenerator D4sector.f (ravFam D4sector m 0) m) := by
    intro l
    induction l with
    | nil => exact hψgen
    | cons a l ih =>
        change ψ (ρP.op a.1 a.2.1 a.2.2 _) = _
        rw [hψeq, ih]
        rfl
  have hψsurj : Function.Surjective ψ := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← gr_cyclic D4sector.f (ravFam D4sector m 0) m hm
      (highModeShift_D4 (ravFam D4sector m 0) m hm), Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨wordOpT ρP l p, hψword l⟩
  have hχword : ∀ l : List (TLtr 28),
      χ (wordOpT ρP l p) =
        wordOpT (D4Fusion.gradedAction m) l (D4Fusion.gradedHighest m) := by
    intro l
    induction l with
    | nil => exact hχgen
    | cons a l ih =>
        change χ (ρP.op a.1 a.2.1 a.2.2 _) = _
        rw [hχeq, ih]
        rfl
  have hχsurj : Function.Surjective χ := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← graded_fusion_cyclic m, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    exact ⟨wordOpT ρP l p, hχword l⟩
  have hG : Module.finrank ℂ (G m) = Module.finrank ℂ (U m) :=
    gr_finrank_eq D4sector.f (ravFam D4sector m 0) m hm
  have hUlow := demazure_rank_ge m
  change 29 ^ m ≤ Module.finrank ℂ (U m) at hUlow
  have hGleP := LinearMap.finrank_le_finrank_of_surjective hψsurj
  have hUeq : Module.finrank ℂ (U m) = 29 ^ m := by omega
  have hPeq : Module.finrank ℂ P = 29 ^ m := by omega
  have hF : Module.finrank ℂ (F m) = 29 ^ m :=
    D4Fusion.graded_total_rank_eq m
  have hψrank : Module.finrank ℂ P = Module.finrank ℂ (G m) := by omega
  have hχrank : Module.finrank ℂ P = Module.finrank ℂ (F m) := by omega
  let ψe : P ≃ₗ[ℂ] G m := LinearEquiv.ofBijective ψ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hψrank).mpr
      hψsurj, hψsurj⟩
  let χe : P ≃ₗ[ℂ] F m := LinearEquiv.ofBijective χ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hχrank).mpr
      hχsurj, hχsurj⟩
  let φ : G m →ₗ[ℂ] F m := χe.toLinearMap.comp ψe.symm.toLinearMap
  have hφgen : φ (grGenerator D4sector.f (ravFam D4sector m 0) m) =
      D4Fusion.gradedHighest m := by
    change χe (ψe.symm (grGenerator D4sector.f (ravFam D4sector m 0) m)) = _
    rw [← hψgen]
    change χe (ψe.symm (ψe p)) = _
    rw [ψe.symm_apply_apply]
    exact hχgen
  have hφeq : ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      (D4Fusion.gradedAction m).op c i s (φ x) := by
    intro c i s x
    have hinv : ψe.symm ((grToroidal_D4 m hm).op c i s x) =
        ρP.op c i s (ψe.symm x) := by
      apply ψe.injective
      change ψ (ψe.symm ((grToroidal_D4 m hm).op c i s x)) =
        ψ (ρP.op c i s (ψe.symm x))
      change ψe (ψe.symm ((grToroidal_D4 m hm).op c i s x)) =
        ψ (ρP.op c i s (ψe.symm x))
      rw [ψe.apply_symm_apply, hψeq]
      change (grToroidal_D4 m hm).op c i s x =
        (grToroidal_D4 m hm).op c i s (ψe (ψe.symm x))
      rw [ψe.apply_symm_apply]
    change χe (ψe.symm ((grToroidal_D4 m hm).op c i s x)) =
      (D4Fusion.gradedAction m).op c i s (χe (ψe.symm x))
    rw [hinv]
    exact hχeq c i s (ψe.symm x)
  exact ⟨⟨φ, hφgen, hφeq⟩, le_of_eq hUeq⟩

/-- A finite cyclic toroidal presentation with maps to both graded targets. -/
def ToroidalPresentation (m : ℕ) (hm : 1 ≤ m) : Prop :=
  (FiniteDimensional ℂ (U m)) ∧
    ∃ (P : Type) (hA : AddCommGroup P),
      letI : AddCommGroup P := hA
      ∃ (hM : Module ℂ P),
        letI : Module ℂ P := hM
        ∃ (hFD : FiniteDimensional ℂ P),
          letI : FiniteDimensional ℂ P := hFD
          ∃ (ρP : ToroidalModule D4sector.f m P) (p : P),
            Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
              wordOpT ρP l p) = ⊤ ∧
            ∃ (ψ : P →ₗ[ℂ] G m),
              ψ p = grGenerator D4sector.f (ravFam D4sector m 0) m ∧
              (∀ c i s x, ψ (ρP.op c i s x) =
                (grToroidal_D4 m hm).op c i s (ψ x)) ∧
              ∃ (χ : P →ₗ[ℂ] F m),
                χ p = D4Fusion.gradedHighest m ∧
                (∀ c i s x, χ (ρP.op c i s x) =
                  (D4Fusion.gradedAction m).op c i s (χ x)) ∧
                Module.finrank ℂ P ≤ 29 ^ m

theorem demazureUnivRank_of_presentations
    (h : ∀ m, (hm : 1 ≤ m) → ToroidalPresentation m hm) :
    DemazureUnivRank := by
  intro m hm
  obtain ⟨hU, P, hA, hM, hFD, ρP, p, hcyc, ψ, hψgen, hψeq,
    χ, hχgen, hχeq, hP⟩ := h m hm
  letI : FiniteDimensional ℂ (U m) := hU
  letI : AddCommGroup P := hA
  letI : Module ℂ P := hM
  letI : FiniteDimensional ℂ P := hFD
  exact ⟨hU, (symbolLemma_of_presentation m hm P ρP p hcyc ψ hψgen
    hψeq χ hχgen hχeq hP).2⟩

theorem fusionTotalDimG_of_presentations
    (h : ∀ m, (hm : 1 ≤ m) → ToroidalPresentation m hm) :
    FiniteG.FusionTotalDimG D4sector := by
  apply fusionTotalDimG_of_symbolLemma (demazureUnivRank_of_presentations h)
  intro m hm
  obtain ⟨hU, P, hA, hM, hFD, ρP, p, hcyc, ψ, hψgen, hψeq,
    χ, hχgen, hχeq, hP⟩ := h m hm
  letI : FiniteDimensional ℂ (U m) := hU
  letI : AddCommGroup P := hA
  letI : Module ℂ P := hM
  letI : FiniteDimensional ℂ P := hFD
  exact (symbolLemma_of_presentation m hm P ρP p hcyc ψ hψgen
    hψeq χ hχgen hχeq hP).1

theorem D4_classicallyFree_of_presentations
    (h : ∀ m, (hm : 1 ≤ m) → ToroidalPresentation m hm)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal := by
  apply D4_classicallyFree_of_symbolLemma (demazureUnivRank_of_presentations h)
  · intro m hm
    obtain ⟨hU, P, hA, hM, hFD, ρP, p, hcyc, ψ, hψgen, hψeq,
      χ, hχgen, hχeq, hP⟩ := h m hm
    letI : FiniteDimensional ℂ (U m) := hU
    letI : AddCommGroup P := hA
    letI : Module ℂ P := hM
    letI : FiniteDimensional ℂ P := hFD
    exact (symbolLemma_of_presentation m hm P ρP p hcyc ψ hψgen
      hψeq χ hχgen hχeq hP).1
  · exact hD

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.symbolLemma_of_presentation
#print axioms VOA.DeligneAudit.Toroidal.demazureUnivRank_of_presentations
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_presentations
#print axioms VOA.DeligneAudit.Toroidal.D4_classicallyFree_of_presentations
