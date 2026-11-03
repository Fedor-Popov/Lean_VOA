import VOA.DeligneAudit.D4LevelReductionAdjointMultiplicity

/-! Homogeneous finite Grassmannian boxes for the adjoint multiplicity spaces. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The current-degree fiber of the pure adjoint Grassmannian box. -/
noncomputable def adjointGradedBox (m a d : ℕ) : Finset (ℕ →₀ ℕ) :=
  (A3Sector.a2BoxModeSet m a).filter (fun f => (Finsupp.weight om f).2 = d)

private noncomputable def adjointModePolynomial (l : List ℕ) : R := (l.map z).prod

private theorem adjointModePolynomial_homogeneous (l : List ℕ) :
    MvPolynomial.IsWeightedHomogeneous om (adjointModePolynomial l) (l.length, l.sum) := by
  induction l with
  | nil =>
      simpa [adjointModePolynomial] using MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s l ih =>
      have hz : MvPolynomial.IsWeightedHomogeneous om (z s) (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      simpa [adjointModePolynomial, Nat.add_comm] using hz.mul ih

private theorem adjointModePolynomial_evaluation (l : List ℕ) :
    Sl2Weyl.evAlg (rootF ρ 1) (rootF_comm ρ 1) (adjointModePolynomial l) =
      (l.map (rootF ρ 1)).prod := by
  induction l with
  | nil => simp [adjointModePolynomial]
  | cons s l ih =>
      simp only [adjointModePolynomial, List.map_cons, List.prod_cons] at *
      rw [map_mul, Sl2Weyl.evAlg_z, ih]

/-- Garland straightening preserves the current degree of each adjoint key. -/
theorem adjointKey_le_gradedBox (m a d : ℕ) (ha : a ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    keyLayer ρ w (adjointLetterKey a d) ≤
      Submodule.span ℂ (adjointBoxVector ρ w '' (adjointGradedBox m a d : Set _)) := by
  classical
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  have hcol := adjointKey_word_colours a d l hl
  have hlen : l.length = a := by
    have hd := wordKey_depth l
    rw [hl] at hd
    simpa [keyDepth, adjointLetterKey] using hd.symm
  have heval : radicalWord ρ w l = ((l.map Prod.snd).map (rootF ρ 1)).prod w := by
    clear hl hlen
    induction l with
    | nil => rfl
    | cons p l ih =>
        have hp := hcol p (by simp)
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
        change ρ.op (radicalColour p.1) p.2 (radicalWord ρ w l) = _
        rw [hp]
        congr 1
        apply ih
        · intro q hq
          exact hcol q (List.mem_cons_of_mem p hq)
  have hk : ∀ r s, 1 ≤ r → m + 1 ≤ r + s →
      (PowerSeries.coeff s (Garland.Fs (rootF ρ 1) ^ r)) w = 0 := by
    intro r s hr hs
    apply radical_garland_zero ρ w m h 1 r s hr
    simpa [rootWeight] using hs
  have hb := span_box_graded (rootF ρ 1) (rootF_comm ρ 1) w m hk
    (adjointModePolynomial_homogeneous (l.map Prod.snd))
  rw [adjointModePolynomial_evaluation, ← heval] at hb
  apply Submodule.span_mono (t := adjointBoxVector ρ w ''
    (adjointGradedBox m a d : Set _)) ?_ hb
  rintro v ⟨f, hf, hw, rfl⟩
  refine ⟨f, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · refine (A3Sector.mem_a2BoxModeSet m a ha f).mpr ⟨?_, hf⟩
    have hfst := congrArg Prod.fst hw
    simpa [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
      Prod.fst_sum, om, hlen] using hfst
  · have hd : (l.map Prod.snd).sum = d := congrArg RadicalKey.degree hl
    exact (congrArg Prod.snd hw).trans hd

/-- Each exact key is bounded by the corresponding homogeneous box fiber. -/
theorem adjointKey_finrank_le_gradedBox (m a d : ℕ) (ha : a ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    Module.finrank ℂ (keyLayer ρ w (adjointLetterKey a d)) ≤
      (adjointGradedBox m a d).card := by
  classical
  let B := (adjointGradedBox m a d).image (adjointBoxVector ρ w)
  have hle : keyLayer ρ w (adjointLetterKey a d) ≤ Submodule.span ℂ (B : Set V) := by
    simpa only [B, Finset.coe_image] using adjointKey_le_gradedBox ρ w m a d ha h
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (B : Set V)) :=
    FiniteDimensional.span_of_finite ℂ B.finite_toSet
  exact (Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card (R := ℂ) (s := B)).trans Finset.card_image_le)

/-- The sum over any finite collection of degrees is bounded by the whole box. -/
theorem adjointGradedBox_sum_le (m a : ℕ) (ha : a ≤ m) (s : Finset ℕ) :
    (∑ d ∈ s, (adjointGradedBox m a d).card) ≤ m.choose a := by
  classical
  rw [← A3Sector.card_a2BoxModeSet m a ha]
  exact (Finset.sum_card_fiberwise_eq_card_filter (A3Sector.a2BoxModeSet m a)
    s (fun f => (Finsupp.weight om f).2)).le.trans (Finset.card_filter_le _ _)

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_le_gradedBox
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_finrank_le_gradedBox
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointGradedBox_sum_le
