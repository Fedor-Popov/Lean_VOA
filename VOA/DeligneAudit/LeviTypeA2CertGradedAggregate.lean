import VOA.DeligneAudit.LeviTypeA2CertGradedQuotRank
import VOA.DeligneAudit.LeviTypeA2CertCount

/-! Distinct key degrees partition the finite two-box monomials. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.Sl2Weyl

theorem a2KeyEnum_injective (p q : ℕ) :
    Function.Injective (a2KeyEnum p q) := by
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hless := a2KeyEnum_descending p q i j hlt
    exact False.elim ((a2KeyLess_irrefl q (a2KeyEnum p q i))
      (by simpa [hij] using hless))
  · exact heq
  · have hless := a2KeyEnum_descending p q j i hgt
    exact False.elim ((a2KeyLess_irrefl q (a2KeyEnum p q i))
      (by simpa [hij] using hless))

/-- Across distinct keys with fixed colour counts, each two-box pair
contributes to at most one degree. -/
theorem a2_boxPairs_aggregate (p q n a b : ℕ)
    (key : Fin n → A2RadicalKey) (hinj : Function.Injective key) :
    (∑ i : Fin n,
      if (key i).d₁ = a ∧ (key i).d₂ = b then
        (a2TwoBoxKeyPairs p q a b (key i).degree).card else 0) ≤
      (a2BoxModeSet p a ×ˢ a2BoxModeSet q b).card := by
  classical
  let I : Finset (Fin n) := Finset.univ.filter
    (fun i => (key i).d₁ = a ∧ (key i).d₂ = b)
  let T := a2BoxModeSet p a ×ˢ a2BoxModeSet q b
  let degree (fg : (ℕ →₀ ℕ) × (ℕ →₀ ℕ)) : ℕ :=
    (Finsupp.weight om fg.1).2 + (Finsupp.weight om fg.2).2
  have hI : (∑ i : Fin n,
      if (key i).d₁ = a ∧ (key i).d₂ = b then
        (a2TwoBoxKeyPairs p q a b (key i).degree).card else 0) =
      ∑ i ∈ I, (T.filter (fun fg => degree fg = (key i).degree)).card := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (key i).d₁ = a ∧ (key i).d₂ = b <;>
      simp [hi, T, degree, a2TwoBoxKeyPairs]
  have hinjDegree : ∀ i ∈ I, ∀ j ∈ I,
      (key i).degree = (key j).degree → i = j := by
    intro i hi j hj hd
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply hinj
    cases hiKey : key i with
    | mk ai bi di =>
      cases hjKey : key j with
      | mk aj bj dj =>
        simp only [hiKey, hjKey] at hi' hj' hd ⊢
        simp only [A2RadicalKey.mk.injEq]
        exact ⟨hi'.1.trans hj'.1.symm,
          hi'.2.trans hj'.2.symm, hd⟩
  rw [hI]
  calc
    (∑ i ∈ I, (T.filter (fun fg => degree fg = (key i).degree)).card) =
        ∑ d ∈ I.image (fun i => (key i).degree),
          (T.filter (fun fg => degree fg = d)).card := by
      let cardDegree : ℕ → ℕ := fun d =>
        (T.filter (fun fg => degree fg = d)).card
      change (∑ i ∈ I, cardDegree ((key i).degree)) =
        ∑ d ∈ I.image (fun i => (key i).degree), cardDegree d
      exact (Finset.sum_image hinjDegree).symm
    _ = (T.filter (fun fg => degree fg ∈
        I.image (fun i => (key i).degree))).card := by
      exact Finset.sum_card_fiberwise_eq_card_filter T
        (I.image fun i => (key i).degree) degree
    _ ≤ T.card := Finset.card_filter_le _ _

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2KeyEnum_injective
#print axioms VOA.DeligneAudit.A3Sector.a2_boxPairs_aggregate
