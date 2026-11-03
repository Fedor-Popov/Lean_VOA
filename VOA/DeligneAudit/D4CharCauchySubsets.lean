import VOA.DeligneAudit.D4CharCauchyLocal

/-! The local C(2,N) identity in the exact finite-subset notation of e-Pieri. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem pieriLower_indicator {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    pieriLower lam (pieriIndicator S) = gtLowerSubset lam S := by
  ext i
  simp [pieriLower, gtLowerSubset, pieriIndicator, pieriBit]

/-- No dominance assumption is needed when the edge is expressed at the output row. -/
theorem gtCauchyBond_indicator (q : R) (N : ℕ) (lam : Fin (N + 1) → ℤ)
    (S : Finset (Fin (N + 1))) :
    (∏ i : Fin N, gtCauchyBond q (lam i.castSucc) (lam i.succ)
      (pieriIndicator S i.castSucc) (pieriIndicator S i.succ)) =
        pieriCoeff q (gtLowerSubset lam S) S := by
  classical
  unfold pieriCoeff
  rw [← Fintype.prod_extend_by_one S, Fin.prod_univ_succ]
  simp only [Fin.val_zero, true_or, ↓reduceIte, ite_self, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  have hp : pieriPrevious i.succ = i.castSucc := by ext; simp [pieriPrevious]
  simp only [hp, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or]
  by_cases hs : i.castSucc ∈ S <;> by_cases ht : i.succ ∈ S <;>
    simp [gtCauchyBond, pieriIndicator, gtLowerSubset, hs, ht]
  congr 2
  omega

theorem gtCauchyBitCoeff_indicator (q : R) (N : ℕ) (lam : Fin N → ℤ)
    (S : Finset (Fin N)) :
    gtCauchyBitCoeff q N lam (pieriIndicator S) =
      (-1) ^ S.card * pieriCoeff q (gtLowerSubset lam S) S := by
  cases N with
  | zero =>
      have hS : S = ∅ := Subsingleton.elim _ _
      simp [gtCauchyBitCoeff, hS, pieriCoeff]
  | succ N =>
      rw [gtCauchyBitCoeff, pieriStateSize_indicator, gtCauchyBond_indicator]

/-- The coefficient identity needed in C(2,N), including every bad output shape. -/
theorem gtCauchySeed_subsets (q : R) (h : PochhammerUnits q) (c : ℤ) (N : ℕ)
    (lam : Fin (N + 2) → ℤ) :
    (∑ S : Finset (Fin (N + 2)), (-1) ^ S.card *
      gtCauchySeed q h c (gtLowerSubset lam S) *
        pieriCoeff q (gtLowerSubset lam S) S) =
      q ^ ((∑ i, lam i) - c).toNat * gtCauchySeed q h c lam := by
  have hh := gtCauchySeed_bits q h c N lam
  rw [← (pieriIndicatorEquiv (N + 2)).sum_comp] at hh
  change (∑ S : Finset (Fin (N + 2)),
    gtCauchyBitCoeff q (N + 2) lam (pieriIndicator S) *
      gtCauchySeed q h c (pieriLower lam (pieriIndicator S))) = _ at hh
  simp only [gtCauchyBitCoeff_indicator, pieriLower_indicator] at hh
  rw [← hh]
  apply Finset.sum_congr rfl
  intro S _
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriLower_indicator
#print axioms VOA.DeligneAudit.D4Char.gtCauchyBond_indicator
#print axioms VOA.DeligneAudit.D4Char.gtCauchyBitCoeff_indicator
#print axioms VOA.DeligneAudit.D4Char.gtCauchySeed_subsets
