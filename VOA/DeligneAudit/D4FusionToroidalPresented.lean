import VOA.DeligneAudit.D4FusionToroidalPresentedQuotient
import VOA.DeligneAudit.D4FusionToroidalGarland3
import VOA.DeligneAudit.D4FusionToroidalStarB2Tuples
import VOA.DeligneAudit.D4FusionToroidalFinitePresentation

/-! The single finite-rank residual for the D4 toroidal presentation. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4

noncomputable section

/-- The universal toroidal module presented by the explicit `Jprime` word relations. -/
abbrev PT (m : ℕ) := PT' D4sector.f m (JprimeSyntax m)

def ρPT (m : ℕ) : ToroidalModule D4sector.f m (PT m) :=
  rhoPT D4sector.f m (JprimeSyntax m)

def pT (m : ℕ) : PT m := pPT D4sector.f m (JprimeSyntax m)

theorem PT_cyclic (m : ℕ) :
    Submodule.span ℂ (Set.range fun l : List (TLtr 28) =>
      wordOpT (ρPT m) l (pT m)) = ⊤ :=
  PT'_cyclic D4sector.f m (JprimeSyntax m)

theorem evalT_rhoPT (m : ℕ) (z : FreeT 28) :
    evalT (ρPT m) (pT m) z = Submodule.Quotient.mk z := by
  have hmap : evalT (ρPT m) (pT m) =
      (JT D4sector.f m (JprimeSyntax m)).mkQ := by
    apply Finsupp.lhom_ext'
    intro l
    apply LinearMap.ext_ring
    change evalT (ρPT m) (pT m) (swT l) =
      (JT D4sector.f m (JprimeSyntax m)).mkQ (swT l)
    rw [evalT_swT]
    exact wordOpT_rhoPT D4sector.f m (JprimeSyntax m) l
  exact LinearMap.congr_fun hmap z

/-- Every `Jprime` operation is represented by its formal word polynomial. -/
theorem Jprime_syntactic (m : ℕ) (r : TRel 28 D4sector.f m)
    (hr : r ∈ Jprime m) :
    ∃ q ∈ JprimeSyntax m,
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
        (ρ : ToroidalModule D4sector.f m W) (v : W),
        r W ρ v = evalT ρ v q := by
  rcases hr with ⟨t, ht, rfl⟩ | ⟨j, N, hj, hjm, hN, rfl⟩
  · refine ⟨swT (symbolLetters m t), Or.inl ⟨t, ht, rfl⟩, ?_⟩
    intro W _ _ ρ v
    exact (evalT_swT ρ v (symbolLetters m t)).symm
  · refine ⟨psymSyntax D4sector.c₀ j N,
      Or.inr ⟨j, N, hj, hjm, hN, rfl⟩, ?_⟩
    intro W _ _ ρ v
    exact (evalT_psymSyntax ρ v D4sector.c₀ j N).symm

theorem Jprime_kills_pT (m : ℕ) :
    Jprime m ⊆ {r | r (PT m) (ρPT m) (pT m) = 0} := by
  intro r hr
  obtain ⟨q, hq, hqr⟩ := Jprime_syntactic m r hr
  change r (PT m) (ρPT m) (pT m) = 0
  rw [hqr (PT m) (ρPT m) (pT m), evalT_rhoPT]
  exact mk_syntax D4sector.f m (JprimeSyntax m) q hq

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem evalT_JprimeSyntax_zero (m : ℕ)
    (ρ : ToroidalModule D4sector.f m V) (v : V)
    (hJ : Jprime m ⊆ {r | r V ρ v = 0}) :
    ∀ q ∈ JprimeSyntax m, evalT ρ v q = 0 := by
  intro q hq
  rcases hq with ⟨t, ht, rfl⟩ | ⟨j, N, hj, hjm, hN, rfl⟩
  · rw [evalT_swT]
    exact hJ (show wordRel (symbolLetters m t) ∈ Jprime m from
      Or.inl ⟨t, ht, rfl⟩)
  · rw [evalT_psymSyntax]
    exact hJ (show PsymRel D4sector.c₀ j N ∈ Jprime m from
      Or.inr ⟨j, N, hj, hjm, hN, rfl⟩)

/-- Word evaluation is the equivariant map out of the presented quotient. -/
def PT_universal (m : ℕ) (ρ : ToroidalModule D4sector.f m V) (v : V)
    (hJ : Jprime m ⊆ {r | r V ρ v = 0}) : PT m →ₗ[ℂ] V :=
  univMapT D4sector.f m (JprimeSyntax m) ρ v
    (evalT_JprimeSyntax_zero m ρ v hJ)

theorem PT_universal_gen (m : ℕ) (ρ : ToroidalModule D4sector.f m V) (v : V)
    (hJ : Jprime m ⊆ {r | r V ρ v = 0}) :
    PT_universal m ρ v hJ (pT m) = v :=
  univMapT_gen D4sector.f m (JprimeSyntax m) ρ v
    (evalT_JprimeSyntax_zero m ρ v hJ)

theorem PT_universal_op (m : ℕ) (ρ : ToroidalModule D4sector.f m V) (v : V)
    (hJ : Jprime m ⊆ {r | r V ρ v = 0})
    (c : Fin 28) (i s : ℕ) (x : PT m) :
    PT_universal m ρ v hJ ((ρPT m).op c i s x) =
      ρ.op c i s (PT_universal m ρ v hJ x) :=
  univMapT_op D4sector.f m (JprimeSyntax m) ρ v
    (evalT_JprimeSyntax_zero m ρ v hJ) c i s x

/-- The map to the graded Ravinder module. -/
def ψPT (m : ℕ) (hm : 1 ≤ m) :
    PT m →ₗ[ℂ] Gr D4sector.f (ravFam D4sector m 0) m :=
  PT_universal m (grToroidal_D4 m hm)
    (grGenerator D4sector.f (ravFam D4sector m 0) m)
    (Jprime_le_annGr m hm)

theorem ψPT_gen (m : ℕ) (hm : 1 ≤ m) :
    ψPT m hm (pT m) =
      grGenerator D4sector.f (ravFam D4sector m 0) m :=
  PT_universal_gen m (grToroidal_D4 m hm)
    (grGenerator D4sector.f (ravFam D4sector m 0) m)
    (Jprime_le_annGr m hm)

theorem ψPT_op (m : ℕ) (hm : 1 ≤ m) (c : Fin 28) (i s : ℕ)
    (x : PT m) :
    ψPT m hm ((ρPT m).op c i s x) =
      (grToroidal_D4 m hm).op c i s (ψPT m hm x) :=
  PT_universal_op m (grToroidal_D4 m hm)
    (grGenerator D4sector.f (ravFam D4sector m 0) m)
    (Jprime_le_annGr m hm) c i s x

/-- The map to the graded fusion module. -/
def χPT (m : ℕ) (hm : 1 ≤ m) :
    PT m →ₗ[ℂ] FusionGr.Gr (D4Fusion.action m) (D4Fusion.generator m) :=
  PT_universal m (D4Fusion.gradedAction m) (D4Fusion.gradedHighest m)
    (StarB2.Jprime_le_annF m hm)

theorem χPT_gen (m : ℕ) (hm : 1 ≤ m) :
    χPT m hm (pT m) = D4Fusion.gradedHighest m :=
  PT_universal_gen m (D4Fusion.gradedAction m) (D4Fusion.gradedHighest m)
    (StarB2.Jprime_le_annF m hm)

theorem χPT_op (m : ℕ) (hm : 1 ≤ m) (c : Fin 28) (i s : ℕ)
    (x : PT m) :
    χPT m hm ((ρPT m).op c i s x) =
      (D4Fusion.gradedAction m).op c i s (χPT m hm x) :=
  PT_universal_op m (D4Fusion.gradedAction m) (D4Fusion.gradedHighest m)
    (StarB2.Jprime_le_annF m hm) c i s x

/-- The remaining dimension assertion for the explicit universal quotient. -/
def PresentedRankBound (m : ℕ) (_hm : 1 ≤ m) : Prop :=
  FiniteDimensional ℂ (PT m) ∧ Module.finrank ℂ (PT m) ≤ 29 ^ m

theorem toroidalPresentation'_of_presentedRankBound (m : ℕ) (hm : 1 ≤ m)
    (h : PresentedRankBound m hm) : ToroidalPresentation' m hm := by
  letI : FiniteDimensional ℂ (PT m) := h.1
  exact ⟨PT m, inferInstance, inferInstance, h.1, ρPT m, pT m,
    PT_cyclic m, ψPT m hm, ψPT_gen m hm, ψPT_op m hm,
    χPT m hm, χPT_gen m hm, χPT_op m hm, h.2⟩

theorem fusionTotalDimG_of_presentedRankBound
    (h : ∀ m, (hm : 1 ≤ m) → PresentedRankBound m hm) :
    FiniteG.FusionTotalDimG D4sector :=
  fusionTotalDimG_of_presentations'
    (fun m hm => toroidalPresentation'_of_presentedRankBound m hm (h m hm))

theorem D4_classicallyFree_of_presentedRankBound
    (h : ∀ m, (hm : 1 ≤ m) → PresentedRankBound m hm)
    (hD : ∀ n, DemazureRealizationG D4sector (ravFam D4sector)
      VOA.DeligneAudit.DeligneCharacter.D4Wp.hilbSeriesZ n) :
    VOA.DeligneHigherRankConditionalCapstone.CaseClassicallyFree .D4 D4Lie.W4
        D4Lie.explicitPresentation4 ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass D4Lie.W4 1 ⟨D4Lie.explicitPresentation4.gen i,
          D4Lie.explicitPresentation4.gen_weight_one i⟩).toRingHom =
        D4Lie.explicitPresentation4.ideal :=
  D4_classicallyFree_of_presentations'
    (fun m hm => toroidalPresentation'_of_presentedRankBound m hm (h m hm)) hD

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.PT_universal
#print axioms VOA.DeligneAudit.Toroidal.PT_cyclic
#print axioms VOA.DeligneAudit.Toroidal.Jprime_syntactic
#print axioms VOA.DeligneAudit.Toroidal.Jprime_kills_pT
#print axioms VOA.DeligneAudit.Toroidal.PT_universal_op
#print axioms VOA.DeligneAudit.Toroidal.toroidalPresentation'_of_presentedRankBound
#print axioms VOA.DeligneAudit.Toroidal.fusionTotalDimG_of_presentedRankBound
#print axioms VOA.DeligneAudit.Toroidal.D4_classicallyFree_of_presentedRankBound
