import VOA.DeligneAudit.D4CharPieriStatement

/-! Invalid dominant-weight additions have zero e-Pieri coefficient. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

/-- The vanishing needed to restrict later normalized Pieri sums to valid partitions. -/
theorem pieriCoeff_zero_of_not_dominant {R : Type*} [CommRing R] (q : R) {N : ℕ}
    (lam : Fin N → ℤ) (S : Finset (Fin N)) (hlam : Antitone lam)
    (hbad : ¬ Antitone (pieriWeight lam S)) : pieriCoeff q lam S = 0 := by
  classical
  cases N with
  | zero => exact (hbad (fun i => Fin.elim0 i)).elim
  | succ N =>
      have hn : ¬ ∀ i : Fin N,
          pieriWeight lam S i.succ ≤ pieriWeight lam S i.castSucc := by
        intro h
        exact hbad (Fin.antitone_iff_succ_le.mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hle : lam i.succ ≤ lam i.castSucc :=
        hlam (show i.castSucc ≤ i.succ by change i.val ≤ i.val + 1; omega)
      have hs : i.castSucc ∉ S := by
        intro hs
        by_cases ht : i.succ ∈ S <;> simp only [pieriWeight, hs, ht, ↓reduceIte] at hi
        all_goals omega
      have ht : i.succ ∈ S := by
        by_contra ht
        simp only [pieriWeight, hs, ht, ↓reduceIte] at hi
        omega
      have he : lam i.castSucc = lam i.succ := by
        simp only [pieriWeight, hs, ht, ↓reduceIte] at hi
        omega
      have hp : pieriPrevious i.succ = i.castSucc := by
        ext
        simp [pieriPrevious]
      unfold pieriCoeff
      apply Finset.prod_eq_zero ht
      simp [hp, hs, he]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriCoeff_zero_of_not_dominant
