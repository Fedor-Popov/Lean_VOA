import VOA.DeligneAudit.D4LeviKSBoxCountKey

/-! The graded fibres of one three-colour box cannot exceed its cardinality. -/

namespace VOA.DeligneAudit.D4Levi

theorem ksGradedBoxCount_sum_le (m a b c : ℕ)
    (I : Finset RadicalKey)
    (hshape : ∀ k ∈ I, k = pairFinalKey a b c k.degree) :
    (∑ k ∈ I, ksGradedBoxCount m a b c k.degree) ≤
      (ksBoxTriples m a b c).card := by
  classical
  let T := ksBoxTriples m a b c
  have hinj : ∀ k ∈ I, ∀ l ∈ I, k.degree = l.degree → k = l := by
    intro k hk l hl hd
    calc
      k = pairFinalKey a b c k.degree := hshape k hk
      _ = pairFinalKey a b c l.degree := by rw [hd]
      _ = l := (hshape l hl).symm
  calc
    (∑ k ∈ I, ksGradedBoxCount m a b c k.degree) =
        ∑ d ∈ I.image RadicalKey.degree,
          (T.filter fun t => ksBoxDegree t = d).card := by
      exact (Finset.sum_image hinj).symm
    _ = (T.filter fun t => ksBoxDegree t ∈ I.image RadicalKey.degree).card := by
      exact Finset.sum_card_fiberwise_eq_card_filter T
        (I.image RadicalKey.degree) ksBoxDegree
    _ ≤ T.card := Finset.card_filter_le _ _

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksGradedBoxCount_sum_le
