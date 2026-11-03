import VOA.DeligneAudit.D4LevelReductionCentralRelations
import VOA.DeligneAudit.D4LevelReductionCentralHighest
import VOA.DeligneAudit.LeviTypeA2CertGradedDefectWords

/-! Homogeneous finite Grassmannian boxes for the central multiplicity spaces. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4Levi
open VOA.DeligneAudit.Sl2Weyl

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V)

/-- The current-degree fiber of the pure central Grassmannian box. -/
noncomputable def centralGradedBox (m a d : ℕ) : Finset (ℕ →₀ ℕ) :=
  (A3Sector.a2BoxModeSet m a).filter (fun f => (Finsupp.weight om f).2 = d)

private noncomputable def centralModePolynomial (l : List ℕ) : R := (l.map z).prod

private theorem centralModePolynomial_homogeneous (l : List ℕ) :
    MvPolynomial.IsWeightedHomogeneous om (centralModePolynomial l) (l.length, l.sum) := by
  induction l with
  | nil =>
      simpa [centralModePolynomial] using MvPolynomial.isWeightedHomogeneous_one ℂ om
  | cons s l ih =>
      have hz : MvPolynomial.IsWeightedHomogeneous om (z s) (1, s) :=
        MvPolynomial.isWeightedHomogeneous_X ℂ om s
      simpa [centralModePolynomial, Nat.add_comm] using hz.mul ih

private theorem centralModePolynomial_evaluation (l : List ℕ) :
    Sl2Weyl.evAlg (rootF ρ 5) (rootF_comm ρ 5) (centralModePolynomial l) =
      (l.map (rootF ρ 5)).prod := by
  induction l with
  | nil => simp [centralModePolynomial]
  | cons s l ih =>
      simp only [centralModePolynomial, List.map_cons, List.prod_cons] at *
      rw [map_mul, Sl2Weyl.evAlg_z, ih]

/-- Evaluation of a central box monomial. -/
noncomputable def centralBoxVector (f : ℕ →₀ ℕ) : V :=
  Sl2Weyl.evAlg (rootF ρ 5) (rootF_comm ρ 5) (MvPolynomial.monomial f 1) w

/-- Every homogeneous Garland defect is absorbed by the next level. -/
theorem centralGradedDefect_le_next (m c d : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    A3Sector.a2GradedDefect (rootF ρ 5) (rootF_comm ρ 5) w m (c, d) ≤
      levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1) := by
  rw [A3Sector.a2GradedDefect, Submodule.span_le]
  rintro v ⟨f, r, s, hr, hrs, hw, rfl⟩
  have hlen : (CLAssembly.lst f).length + r = c := by
    have hh := congrArg Prod.fst hw
    simpa [CLAssembly.length_lst, Finsupp.weight_apply, Finsupp.degree_apply,
      Finsupp.sum, Prod.fst_sum, om] using hh
  rw [mul_comm (MvPolynomial.monomial f 1), map_mul, Sl2Weyl.evAlg_xx,
    A3Sector.a2_evAlg_monomial_word]
  have hh := centralGarland_spectator_mem_next ρ w m h (CLAssembly.lst f) r s hr hrs
  have hlen' : ((CLAssembly.lst f).length : ℤ) + r = c := by exact_mod_cast hlen
  rw [hlen'] at hh
  exact hh

/-- Garland straightening preserves the current degree of each central key. -/
theorem centralKey_le_gradedBox_sup_next (m a d : ℕ) (ha : a ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    keyLayer ρ w (centralLetterKey a d) ≤
      Submodule.span ℂ (centralBoxVector ρ w '' (centralGradedBox m a d : Set _)) ⊔
        levelFiltration ρ w m ((m : ℤ) - a) ((m : ℤ) - a + 1) := by
  classical
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  have hcol := centralKey_word_colours a d l hl
  have hlen : l.length = a := by
    have hd := wordKey_depth l
    rw [hl] at hd
    simpa [keyDepth, centralLetterKey] using hd.symm
  have heval : radicalWord ρ w l = ((l.map Prod.snd).map (rootF ρ 5)).prod w := by
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
  have hb := A3Sector.a2_span_box_graded_explicit_eval (rootF ρ 5) (rootF_comm ρ 5)
    w m (centralModePolynomial_homogeneous (l.map Prod.snd))
  rw [centralModePolynomial_evaluation, ← heval] at hb
  have hd : (l.map Prod.snd).sum = d := congrArg RadicalKey.degree hl
  simp only [List.length_map, hlen, hd] at hb
  apply (show _ ≤ Submodule.span ℂ (centralBoxVector ρ w ''
    (centralGradedBox m a d : Set _)) ⊔
      levelFiltration ρ w m ((m : ℤ) - a) ((m : ℤ) - a + 1) from
    sup_le_sup ?_ (centralGradedDefect_le_next ρ w m a d h)) hb
  apply Submodule.span_mono
  rintro v ⟨f, hf, hw, rfl⟩
  refine ⟨f, Finset.mem_filter.mpr ⟨?_, ?_⟩, rfl⟩
  · refine (A3Sector.mem_a2BoxModeSet m a ha f).mpr ⟨?_, hf⟩
    have hfst := congrArg Prod.fst hw
    simpa [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
      Prod.fst_sum, om, hlen] using hfst
  · have hd : (l.map Prod.snd).sum = d := congrArg RadicalKey.degree hl
    exact congrArg Prod.snd hw

/-- A homogeneous central multiplicity quotient has the finite Grassmannian box bound. -/
theorem centralKey_quotient_finrank_le_gradedBox (m c d : ℕ) (hc : c ≤ m)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    let N := levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1)
    Module.finrank ℂ (keyLayer ρ w (centralLetterKey c d) ⧸
      N.comap (keyLayer ρ w (centralLetterKey c d)).subtype) ≤
        (centralGradedBox m c d).card := by
  classical
  let N := levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1)
  let B := (centralGradedBox m c d).image (fun f => N.mkQ (centralBoxVector ρ w f))
  have hle : (keyLayer ρ w (centralLetterKey c d)).map N.mkQ ≤
      Submodule.span ℂ (B : Set (V ⧸ N)) := by
    have hh := Submodule.map_mono (f := N.mkQ)
      (centralKey_le_gradedBox_sup_next ρ w m c d hc h)
    rw [Submodule.map_sup, Submodule.map_span, Submodule.mkQ_map_self, sup_bot_eq] at hh
    simpa only [B, Finset.coe_image, Set.image_image, Function.comp_def] using hh
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (B : Set (V ⧸ N))) :=
    FiniteDimensional.span_of_finite ℂ B.finite_toSet
  dsimp only
  rw [ksKey_quot_finrank_eq_image]
  exact (Submodule.finrank_mono hle).trans
    ((finrank_span_finset_le_card (R := ℂ) (s := B)).trans Finset.card_image_le)

/-- The homogeneous central boxes together have at most the Grassmannian binomial count. -/
theorem centralGradedBox_sum_le (m c : ℕ) (hc : c ≤ m) (s : Finset ℕ) :
    (∑ d ∈ s, (centralGradedBox m c d).card) ≤ m.choose c := by
  exact adjointGradedBox_sum_le m c hc s

/-- More central letters than the multiplicity vanish modulo the next level. -/
theorem centralKey_le_next_of_overfull (m c d : ℕ) (hc : m < c)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) :
    keyLayer ρ w (centralLetterKey c d) ≤
      levelFiltration ρ w m ((m : ℤ) - c) ((m : ℤ) - c + 1) := by
  classical
  rw [keyLayer, Submodule.span_le]
  rintro v ⟨l, hl, rfl⟩
  have hcol := centralKey_word_colours c d l hl
  have hlen : l.length = c := by
    have hd := wordKey_depth l
    rw [hl] at hd
    simpa [keyDepth, centralLetterKey] using hd.symm
  have heval : radicalWord ρ w l = ((l.map Prod.snd).map (rootF ρ 5)).prod w := by
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
  have hb := A3Sector.a2_span_box_graded_explicit_eval (rootF ρ 5) (rootF_comm ρ 5)
    w m (centralModePolynomial_homogeneous (l.map Prod.snd))
  rw [centralModePolynomial_evaluation, ← heval] at hb
  have hd : (l.map Prod.snd).sum = d := congrArg RadicalKey.degree hl
  simp only [List.length_map, hlen, hd] at hb
  obtain ⟨vB, hB, vD, hD, hsum⟩ := Submodule.mem_sup.mp hb
  have hzero : vB = 0 := by
    clear hsum
    induction hB using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨f, hf, hw, _⟩ := hv
        have hbound := A3Sector.a3_box_degree_le m f hf
        have hweight := congrArg Prod.fst hw
        rw [A3Sector.a3_box_weight_first] at hweight
        omega
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul t x _ hx => simp [hx]
  rw [← hsum, hzero, zero_add]
  exact centralGradedDefect_le_next ρ w m c d h hD

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.centralGradedDefect_le_next
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_le_gradedBox_sup_next
#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_quotient_finrank_le_gradedBox
#print axioms VOA.DeligneAudit.D4LevelReduction.centralGradedBox_sum_le

#print axioms VOA.DeligneAudit.D4LevelReduction.centralKey_le_next_of_overfull
