import VOA.DeligneAudit.D4LeviKSPairSpectatorEval
import VOA.DeligneAudit.D4LeviKSPairFactor

/-! The target kernel after PAIR is exactly the image of source relations. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial
open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The quotient evaluator on the three symmetric target alphabets. -/
noncomputable def pairTargetQuotientEvaluation
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c) :
    pairTargetSymmetric a b c →ₗ[ℂ] V ⧸ keyPrefix ρ w m i :=
  pairSymmetricFactor a b c
    (pairSymmetricWordEvaluation ρ w m i a b c)
    (fun P hP =>
      (pairSymmetricWordEvaluation_eq_zero_iff ρ w m i a b c P).2
        (hPair P hP))

theorem pairTargetQuotientEvaluation_comp
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c)
    (P : pairSourceSymmetric a b c) :
    pairTargetQuotientEvaluation ρ w m i a b c hPair
        (pairSymmetricRestriction a b c P) =
      pairSymmetricWordEvaluation ρ w m i a b c P :=
  pairSymmetricFactor_comp a b c _ _ P

/-- Every target relation is the restriction of a source word relation.
    This uses surjectivity of PAIR, not an injectivity claim for words. -/
theorem pairTargetQuotientEvaluation_ker
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c) :
    (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker =
      (pairSymmetricWordEvaluation ρ w m i a b c).ker.map
        (pairSymmetricRestriction a b c).toLinearMap := by
  apply le_antisymm
  · intro T hT
    obtain ⟨P, rfl⟩ := pairSymmetricRestriction_surjective a b c T
    refine ⟨P, ?_, rfl⟩
    change pairSymmetricWordEvaluation ρ w m i a b c P = 0
    rw [← pairTargetQuotientEvaluation_comp ρ w m i a b c hPair P]
    exact hT
  · rintro T ⟨P, hP, rfl⟩
    change pairTargetQuotientEvaluation ρ w m i a b c hPair
      (pairSymmetricRestriction a b c P) = 0
    rw [pairTargetQuotientEvaluation_comp]
    exact hP

/-- A concrete source presentation of a relation gives a target-kernel
    relation, and every target-kernel relation has such a presentation. -/
theorem pairTargetQuotientEvaluation_mem_ker_iff
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c)
    (T : pairTargetSymmetric a b c) :
    T ∈ (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker ↔
      ∃ P : pairSourceSymmetric a b c,
        pairSymmetricRestriction a b c P = T ∧
        xyzEvaluation ρ w (pairSourceShape a b c) P ∈
          keyPrefix ρ w m i := by
  rw [pairTargetQuotientEvaluation_ker]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P, rfl,
      (pairSymmetricWordEvaluation_eq_zero_iff ρ w m i a b c P).1 hP⟩
  · rintro ⟨P, hPT, hP⟩
    refine ⟨P, ?_, hPT⟩
    exact (pairSymmetricWordEvaluation_eq_zero_iff ρ w m i a b c P).2 hP

/-- The target-kernel criterion at a supported final key. -/
theorem pairTargetQuotientEvaluation_mem_ker_of_sat
    (ρ : CurrentModule D4sector.f V) (w : V)
    (m i a b c deg : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (hkey : keyEnum m ⟨i, hi⟩ = pairFinalKey a b c deg)
    (T : pairTargetSymmetric a b c)
    (P : pairSourceSymmetric a b c)
    (hPT : pairSymmetricRestriction a b c P = T)
    (hP : xyzEvaluation ρ w (pairSourceShape a b c) P ∈
      keyPrefix ρ w m i) :
    T ∈ (pairTargetQuotientEvaluation ρ w m i a b c
      (pairKernelPrefix_of_sat ρ w m i a b c deg h hi hkey)).ker :=
  (pairTargetQuotientEvaluation_mem_ker_iff ρ w m i a b c
    (pairKernelPrefix_of_sat ρ w m i a b c deg h hi hkey) T).2
      ⟨P, hPT, hP⟩

/-- A fixed-shape XYZ relation transports to the PAIR target after its
    polynomial is relabelled into the three symmetric source alphabets. -/
theorem pairTargetRelation_of_shape
    {σ : Type*} [Fintype σ]
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c)
    (shape : σ → Fin 6) (e : σ ≃ PairSource a b c)
    (hshape : pairSourceShape a b c ∘ e = shape)
    (W : MvPolynomial σ ℂ)
    (hmem : rename e W ∈ pairSourceSymmetric a b c)
    (hprefix : xyzEvaluation ρ w shape W ∈ keyPrefix ρ w m i) :
    pairSymmetricRestriction a b c ⟨rename e W, hmem⟩ ∈
      (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker := by
  apply (pairTargetQuotientEvaluation_mem_ker_iff ρ w m i a b c
    hPair _).2
  refine ⟨⟨rename e W, hmem⟩, rfl, ?_⟩
  rw [xyzEvaluation_rename_bijection ρ w (pairSourceShape a b c) e W]
  simpa only [hshape] using hprefix

/-- Once the nested box inclusion is known in a target subspace, its
    quotient image has rank bounded by the number of box polynomials. -/
theorem pairTarget_image_finrank_le_of_span
    (ρ : CurrentModule D4sector.f V) (w : V) (m i a b c : ℕ)
    (hPair : PairKernelPrefix ρ w m i a b c)
    (S : Submodule ℂ (pairTargetSymmetric a b c))
    (B : Finset (pairTargetSymmetric a b c))
    (hspan : S ≤ Submodule.span ℂ (B : Set (pairTargetSymmetric a b c)) ⊔
      (pairTargetQuotientEvaluation ρ w m i a b c hPair).ker) :
    Module.finrank ℂ
      (S.map (pairTargetQuotientEvaluation ρ w m i a b c hPair)) ≤ B.card := by
  classical
  let q := pairTargetQuotientEvaluation ρ w m i a b c hPair
  let E := B.image q
  have himage : S.map q ≤ Submodule.span ℂ (E : Set (V ⧸ keyPrefix ρ w m i)) := by
    rintro v ⟨P, hP, rfl⟩
    obtain ⟨Pbox, hbox, Prel, hrel, hsum⟩ := Submodule.mem_sup.mp (hspan hP)
    rw [← hsum, map_add, (LinearMap.mem_ker.mp hrel), add_zero]
    have hmap : q Pbox ∈
        (Submodule.span ℂ (B : Set (pairTargetSymmetric a b c))).map q :=
      ⟨Pbox, hbox, rfl⟩
    simpa only [Submodule.map_span, E, Finset.coe_image] using hmap
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (E : Set (V ⧸ keyPrefix ρ w m i))) :=
    FiniteDimensional.span_of_finite _ (Finset.finite_toSet E)
  calc
    Module.finrank ℂ (S.map q) ≤
        Module.finrank ℂ
          (Submodule.span ℂ (E : Set (V ⧸ keyPrefix ρ w m i))) :=
      Submodule.finrank_mono himage
    _ ≤ E.card := finrank_span_finset_le_card (R := ℂ) (s := E)
    _ ≤ B.card := Finset.card_image_le

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_comp
#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_ker
#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_mem_ker_iff
#print axioms VOA.DeligneAudit.D4Levi.pairTargetQuotientEvaluation_mem_ker_of_sat
#print axioms VOA.DeligneAudit.D4Levi.pairTargetRelation_of_shape
#print axioms VOA.DeligneAudit.D4Levi.pairTarget_image_finrank_le_of_span
