import VOA.DeligneAudit.D4LeviKSBoxCountEnum

/-! A finite graded version of the one-alphabet Garland box spanning lemma. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.Sl2Weyl
open VOA.DeligneAudit.A3Sector

noncomputable def ksOneBoxPolys (q n d : ℕ) : Finset R := by
  classical
  exact ((a2BoxModeSet q n).filter
    (fun f => Finsupp.weight om f = (n, d))).image
      (fun f => MvPolynomial.monomial f 1)

theorem ksOneBoxPolys_card_le (q n d : ℕ) (hn : n ≤ q) :
    (ksOneBoxPolys q n d).card ≤ q.choose n := by
  classical
  calc
    (ksOneBoxPolys q n d).card ≤
        ((a2BoxModeSet q n).filter
          (fun f => Finsupp.weight om f = (n, d))).card := by
      exact Finset.card_image_le
    _ ≤ (a2BoxModeSet q n).card := Finset.card_filter_le _ _
    _ = q.choose n := card_a2BoxModeSet q n hn

private theorem weight_first (f : ℕ →₀ ℕ) :
    (Finsupp.weight om f).1 = Finsupp.degree f := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum,
    Prod.fst_sum, om]

/-- Each homogeneous component of the one-colour quotient is spanned by
the finite set of box monomials with that exact degree. -/
theorem ksOneBox_span_graded (q n d : ℕ) (hn : n ≤ q)
    (p : R) (hp : MvPolynomial.IsWeightedHomogeneous om p (n, d)) :
    p ∈ Submodule.span ℂ (ksOneBoxPolys q n d : Set R) ⊔
      (J q).restrictScalars ℂ := by
  have hle : Submodule.span ℂ
      {v : R | ∃ f, BoxP q f ∧ Finsupp.weight om f = (n, d) ∧
        v = MvPolynomial.monomial f 1} ≤
      Submodule.span ℂ (ksOneBoxPolys q n d : Set R) := by
    apply Submodule.span_mono
    intro v hv
    obtain ⟨f, hf, hw, rfl⟩ := hv
    have hdegree : Finsupp.degree f = n := by
      rw [← weight_first f, hw]
    change MvPolynomial.monomial f 1 ∈ ksOneBoxPolys q n d
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_filter.mpr ⟨?_, hw⟩, rfl⟩
    exact (mem_a2BoxModeSet q n hn f).mpr ⟨hdegree, hf⟩
  exact (sup_le_sup_right hle _) (box_span_graded q hp)

private theorem ksBox_degree_le (q : ℕ) (f : ℕ →₀ ℕ)
    (hf : BoxP q f) : Finsupp.degree f ≤ q := by
  by_cases hz : f = 0
  · subst f
    simp
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hz
    have hbound := hf i hi
    omega

/-- The degree-`n` quotient vanishes when the number of letters exceeds
the Garland weight `q`. -/
theorem ksOneBox_J_of_length_gt (q n d : ℕ) (hn : q < n)
    (p : R) (hp : MvPolynomial.IsWeightedHomogeneous om p (n, d)) :
    p ∈ (J q).restrictScalars ℂ := by
  have hgen :
      {v : R | ∃ f, BoxP q f ∧ Finsupp.weight om f = (n, d) ∧
        v = MvPolynomial.monomial f 1} = ∅ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨f, hf, hw, _⟩
    have hd : Finsupp.degree f = n := by
      rw [← weight_first f, hw]
    have hq := ksBox_degree_le q f hf
    omega
  have h := box_span_graded q hp
  simpa only [hgen, Submodule.span_empty, bot_sup_eq] using h

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksOneBox_span_graded
#print axioms VOA.DeligneAudit.D4Levi.ksOneBox_J_of_length_gt
#print axioms VOA.DeligneAudit.D4Levi.ksOneBoxPolys_card_le
