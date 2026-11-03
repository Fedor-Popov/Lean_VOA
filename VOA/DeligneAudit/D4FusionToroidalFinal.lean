import VOA.DeligneAudit.D4FusionToroidalFinalUZero
import VOA.DeligneAudit.D4FusionToroidalFinalRank
import VOA.DeligneAudit.D4FusionToroidalGrRankKL
import VOA.DeligneAudit.D4FusionContactAllMModelReduction

/-! The remaining symbol map and its KL consequence. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.UnivG VOA.DeligneAudit.SectorWeyl

noncomputable section

def SymbolLemma (m : ℕ) (hm : 1 ≤ m) : Prop :=
  ∃ φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ]
      FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m),
    φ (grGenerator D4sector.f (ravFam D4sector m 0) m) =
      D4Fusion.gradedHighest m ∧
    ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      (D4Fusion.gradedAction m).op c i s (φ x)

theorem graded_fusion_cyclic (m : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
      wordOpT (D4Fusion.gradedAction m) l (D4Fusion.gradedHighest m)) = ⊤ := by
  exact FusionGr.gradedCyclic_top (D4Fusion.action m) (D4Fusion.generator m) m
    (FusionGr.evalHighTShift
      (fun _ => D1SiteG.rep
        (VOA.DeligneAudit.DeligneSector.Sparse.fC 28
          VOA.DeligneAudit.DeligneSector.D4.br)
        D1SiteG.D4Check.table_jacobi D1SiteG.D4Check.table_skewC)
      (D1TensorG.points m) (D4Fusion.generator m))

theorem symbolLemma_surjective (m : ℕ) (hm : 1 ≤ m)
    (φ : Gr D4sector.f (ravFam D4sector m 0) m →ₗ[ℂ]
      FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m))
    (hgen : φ (grGenerator D4sector.f (ravFam D4sector m 0) m) =
      D4Fusion.gradedHighest m)
    (heq : ∀ c i s x, φ ((grToroidal_D4 m hm).op c i s x) =
      (D4Fusion.gradedAction m).op c i s (φ x)) :
    Function.Surjective φ := by
  have hword : ∀ l : List (TLtr 28),
      φ (wordOpT (grToroidal_D4 m hm) l
        (grGenerator D4sector.f (ravFam D4sector m 0) m)) =
        wordOpT (D4Fusion.gradedAction m) l (D4Fusion.gradedHighest m) := by
    intro l
    induction l with
    | nil => exact hgen
    | cons a l ih =>
        change φ ((grToroidal_D4 m hm).op a.1 a.2.1 a.2.2 _) = _
        rw [heq, ih]
        rfl
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← graded_fusion_cyclic m, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact ⟨_, hword l⟩

def coadjointGr (m : ℕ) : Submodule ℂ
    (FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m)) :=
  FusionGr.subGr (D4Fusion.action m) (D4Fusion.generator m)
    (D4Fusion.coadjointSource m)

theorem coadjointGr_rank_le (m : ℕ) :
    Module.finrank ℂ (coadjointGr m) ≤ 28 ^ m := by
  exact (FusionGr.d4_evalUZeroGr_rank_le m).2

theorem coadjointGr_generator (m : ℕ) :
    D4Fusion.gradedHighest m ∈ coadjointGr m :=
  FusionGr.subGr_generator (D4Fusion.action m) (D4Fusion.generator m)
    (D4Fusion.coadjointSource m) (D4Fusion.coadjointSource_generator m)

theorem coadjointGr_op (m : ℕ) (c : Fin 28) (s : ℕ) :
    coadjointGr m ≤ (coadjointGr m).comap
      ((D4Fusion.gradedAction m).op c 0 s) := by
  exact FusionGr.subGr_op (D4Fusion.action m) (D4Fusion.generator m) m
    (D4Fusion.coadjointSource m) (D4Fusion.coadjointSource_op m) c s

theorem kLCoreTarget_of_symbolLemma (m : ℕ) (hm : 1 ≤ m)
    (hSymbol : SymbolLemma m hm) : KLCoreTarget m hm := by
  obtain ⟨φ, hgen, heq⟩ := hSymbol
  letI : FiniteDimensional ℂ
      (FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m)) :=
    (D4Fusion.graded_total_rank_bound m).1
  refine ⟨FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m),
    inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨D4Fusion.gradedAction m, D4Fusion.gradedHighest m, φ,
    coadjointGr m, hgen, heq, ?_, ?_, ?_, ?_, ?_⟩
  · exact symbolLemma_surjective m hm φ hgen heq
  · exact coadjointGr_generator m
  · exact coadjointGr_op m
  · exact le_of_eq (D4Fusion.graded_total_rank_eq m).symm
  · exact coadjointGr_rank_le m

theorem fusionTotalDimG_of_symbolLemma
    (hF : DemazureUnivRank)
    (hSymbol : ∀ m, (hm : 1 ≤ m) → SymbolLemma m hm) :
    FiniteG.FusionTotalDimG D4sector := by
  apply fusionTotalDimG_of_KLCore hF
  intro m hm
  exact kLCoreTarget_of_symbolLemma m hm (hSymbol m hm)

theorem D4_classicallyFree_of_symbolLemma
    (hF : DemazureUnivRank)
    (hSymbol : ∀ m, (hm : 1 ≤ m) → SymbolLemma m hm)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  d4_classicallyFree_of_totalBound
    (FiniteG.D4.d4_fusionTotalBoundG_of_dim
      (fusionTotalDimG_of_symbolLemma hF hSymbol)) hD

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.symbolLemma_surjective
#print axioms VOA.DeligneAudit.Toroidal.graded_fusion_cyclic
#print axioms VOA.DeligneAudit.Toroidal.coadjointGr_rank_le
#print axioms VOA.DeligneAudit.Toroidal.coadjointGr_op
#print axioms VOA.DeligneAudit.Toroidal.kLCoreTarget_of_symbolLemma
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_symbolLemma
#print axioms VOA.DeligneAudit.Toroidal.D4_classicallyFree_of_symbolLemma
