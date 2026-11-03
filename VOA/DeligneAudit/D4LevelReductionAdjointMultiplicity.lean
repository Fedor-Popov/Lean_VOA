import VOA.DeligneAudit.D4LevelReductionAdjointEdge
import VOA.DeligneAudit.LeviTypeA2CertBoxCard

/-! A binomial spanning bound for the pure adjoint-letter multiplicity space. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- Pure adjoint words of fixed length and arbitrary current degree. -/
noncomputable def adjointMultiplicitySpan (a : ℕ) : Submodule ℂ V :=
  ⨆ d : ℕ, keyLayer ρ w (adjointLetterKey a d)

/-- A pure adjoint key has only the adjoint radical colour. -/
theorem adjointKey_word_colours (a d : ℕ) (l : List (Fin 6 × ℕ))
    (h : wordKey l = adjointLetterKey a d) : ∀ p ∈ l, p.1 = 1 := by
  have hl := wordKey_depth l
  have hx := congrArg RadicalKey.x h
  rw [h] at hl
  simp only [adjointLetterKey, keyDepth, zero_add, add_zero] at hl
  simp only [wordKey, adjointLetterKey] at hx
  have hc : l.countP (fun p => p.1 = 1) = l.length := hx.trans hl
  simpa using List.countP_eq_length.mp hc

private noncomputable def modeWordPolynomial (l : List ℕ) : R := (l.map z).prod

private theorem modeWordPolynomial_homogeneous (l : List ℕ) :
    MvPolynomial.IsWeightedHomogeneous om (modeWordPolynomial l) (l.length, l.sum) := by
  induction l with
  | nil =>
      simpa [modeWordPolynomial] using MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s l ih =>
      have hz : MvPolynomial.IsWeightedHomogeneous om (z s) (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      simpa [modeWordPolynomial, Nat.add_comm] using hz.mul ih

private theorem modeWordPolynomial_evaluation (l : List ℕ) :
    Sl2Weyl.evAlg (rootF ρ 1) (rootF_comm ρ 1) (modeWordPolynomial l) =
      (l.map (rootF ρ 1)).prod := by
  induction l with
  | nil => simp [modeWordPolynomial]
  | cons s l ih =>
      simp only [modeWordPolynomial, List.map_cons, List.prod_cons] at *
      rw [map_mul, Sl2Weyl.evAlg_z, ih]

/-- Evaluated monomials of the rank-one Garland box. -/
noncomputable def adjointBoxVector (f : ℕ →₀ ℕ) : V :=
  Sl2Weyl.evAlg (rootF ρ 1) (rootF_comm ρ 1) (MvPolynomial.monomial f 1) w

/-- Garland straightening bounds the whole multiplicity space by one finite mode box. -/
theorem adjointMultiplicitySpan_le_box (m a : ℕ) (ha : a ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    adjointMultiplicitySpan ρ w a ≤
      Submodule.span ℂ (adjointBoxVector ρ w '' (A3Sector.a2BoxModeSet m a : Set _)) := by
  apply iSup_le
  intro d
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
    (modeWordPolynomial_homogeneous (l.map Prod.snd))
  rw [modeWordPolynomial_evaluation, ← heval] at hb
  apply Submodule.span_mono (t := adjointBoxVector ρ w ''
    (A3Sector.a2BoxModeSet m a : Set _)) ?_ hb
  rintro v ⟨f, hf, hw, rfl⟩
  refine ⟨f, (A3Sector.mem_a2BoxModeSet m a ha f).mpr ⟨?_, hf⟩, rfl⟩
  have hfst := congrArg Prod.fst hw
  simpa [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om, hlen] using hfst

/-- The pure adjoint-letter multiplicity space has dimension at most a binomial coefficient. -/
theorem adjointMultiplicitySpan_rank_le (m a : ℕ) (ha : a ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    FiniteDimensional ℂ (adjointMultiplicitySpan ρ w a) ∧
      Module.finrank ℂ (adjointMultiplicitySpan ρ w a) ≤ m.choose a := by
  classical
  let B := (A3Sector.a2BoxModeSet m a).image (adjointBoxVector ρ w)
  have hle : adjointMultiplicitySpan ρ w a ≤ Submodule.span ℂ (B : Set V) := by
    simpa only [B, Finset.coe_image] using adjointMultiplicitySpan_le_box ρ w m a ha h
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (B : Set V)) :=
    FiniteDimensional.span_of_finite ℂ B.finite_toSet
  haveI : FiniteDimensional ℂ (adjointMultiplicitySpan ρ w a) :=
    Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, (Submodule.finrank_mono hle).trans ?_⟩
  exact (finrank_span_finset_le_card (R := ℂ) (s := B)).trans
    (Finset.card_image_le.trans (le_of_eq (A3Sector.card_a2BoxModeSet m a ha)))

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.adjointKey_word_colours
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointMultiplicitySpan_le_box
#print axioms VOA.DeligneAudit.D4LevelReduction.adjointMultiplicitySpan_rank_le
