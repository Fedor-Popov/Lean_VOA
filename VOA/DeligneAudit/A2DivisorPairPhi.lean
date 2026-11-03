import VOA.DeligneAudit.A2DivisorPairData

namespace VOA.DeligneAudit.A2.PairCert

/-- Delta contraction, proved algebraically for the table rather than by a large decision. -/
theorem phiZ_symT_generic (r : Option (Fin 8)) (c d : Fin 8) :
    phiZ r (symT c d) = qZ r c d + qZ r d c := by
  simp only [phiZ, symT, eT, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single c]
    · rw [Finset.sum_eq_single d]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      simp [ha]
    · simp
  · rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single c]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro b _
      simp [ha]
    · simp

end VOA.DeligneAudit.A2.PairCert
