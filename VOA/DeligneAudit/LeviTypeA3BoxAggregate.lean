import VOA.DeligneAudit.LeviTypeA3BoxCard
import VOA.DeligneAudit.LeviTypeA2CertGradedAggregate

/-! Distinct key degrees partition the three-colour mode box. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

noncomputable def a3BoxDegree
    (fg : ((ℕ →₀ ℕ) × (ℕ →₀ ℕ)) × (ℕ →₀ ℕ)) : ℕ :=
  (Finsupp.weight om fg.1.1).2 +
    (Finsupp.weight om fg.1.2).2 + (Finsupp.weight om fg.2).2

theorem a3KeyEnum_injective (a b c : ℕ) :
    Function.Injective (a3KeyEnum a b c) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hless := a3KeyEnum_descending a b c i j hlt
    exact False.elim ((a3KeyLess_irrefl b c (a3KeyEnum a b c i))
      (by simpa [hij] using hless))
  · exact heq
  · have hless := a3KeyEnum_descending a b c j i hgt
    exact False.elim ((a3KeyLess_irrefl b c (a3KeyEnum a b c i))
      (by simpa [hij] using hless))

/-- For fixed colour counts, no two distinct keys claim the same box degree. -/
theorem a3_boxTriples_aggregate (a b c n d₁ d₂ d₃ : ℕ)
    (key : Fin n → A3RadicalKey) (hinj : Function.Injective key) :
    (∑ i : Fin n,
      if (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃ then
        ((a3ThreeBoxModeSet a b c d₁ d₂ d₃).filter
          (fun fg => a3BoxDegree fg = (key i).degree)).card else 0) ≤
      (a3ThreeBoxModeSet a b c d₁ d₂ d₃).card := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter
    (fun i => (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃)
  let T := a3ThreeBoxModeSet a b c d₁ d₂ d₃
  have hI : (∑ i : Fin n,
      if (key i).d₁ = d₁ ∧ (key i).d₂ = d₂ ∧ (key i).d₃ = d₃ then
        (T.filter (fun fg => a3BoxDegree fg = (key i).degree)).card else 0) =
      ∑ i ∈ I, (T.filter (fun fg => a3BoxDegree fg = (key i).degree)).card := by
    rw [Finset.sum_filter]
  have hinjDegree : ∀ i ∈ I, ∀ j ∈ I,
      (key i).degree = (key j).degree → i = j := by
    intro i hi j hj hd
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply hinj
    cases hiKey : key i with
    | mk ai bi ci di =>
      cases hjKey : key j with
      | mk aj bj cj dj =>
        simp only [hiKey, hjKey] at hi' hj' hd ⊢
        simp only [A3RadicalKey.mk.injEq]
        exact ⟨hi'.1.trans hj'.1.symm,
          hi'.2.1.trans hj'.2.1.symm,
          hi'.2.2.trans hj'.2.2.symm, hd⟩
  rw [hI]
  calc
    (∑ i ∈ I, (T.filter (fun fg => a3BoxDegree fg = (key i).degree)).card) =
        ∑ d ∈ I.image (fun i => (key i).degree),
          (T.filter (fun fg => a3BoxDegree fg = d)).card := by
      let cardDegree : ℕ → ℕ := fun d =>
        (T.filter (fun fg => a3BoxDegree fg = d)).card
      change (∑ i ∈ I, cardDegree ((key i).degree)) =
        ∑ d ∈ I.image (fun i => (key i).degree), cardDegree d
      exact (Finset.sum_image hinjDegree).symm
    _ = (T.filter (fun fg => a3BoxDegree fg ∈
        I.image (fun i => (key i).degree))).card := by
      exact Finset.sum_card_fiberwise_eq_card_filter T
        (I.image fun i => (key i).degree) a3BoxDegree
    _ ≤ T.card := Finset.card_filter_le _ _

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyEnum_injective
#print axioms VOA.DeligneAudit.A3Sector.a3_boxTriples_aggregate
