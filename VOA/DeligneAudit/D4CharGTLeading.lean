import VOA.DeligneAudit.D4CharGTDominance

/-! The leading GT monomial has coefficient one, in every rank and coefficient ring. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators
open VOA.DeligneGaussian

noncomputable section

variable {R : Type*} [CommRing R]

/-- Equality in the top partial sum forces the unique top interlacing row. -/
theorem gtRows_eq_top_of_sum {N : ℕ} {lam : Fin (N + 1) → ℤ} {μ : Fin N → ℤ}
    (hμ : μ ∈ gtRows lam) (hs : (∑ i, μ i) = ∑ i : Fin N, lam i.castSucc) :
    μ = fun i => lam i.castSucc := by
  funext i
  exact (Finset.sum_eq_sum_iff_of_le
    (fun j _ => ((mem_gtRows lam μ).mp hμ j).2)).mp hs i (Finset.mem_univ i)

/-- Splitting off the last coordinate of a highest weight. -/
theorem gtExponent_split (N : ℕ) (lam : Fin (N + 1) → ℤ) :
    gtExponent lam = gtExponent (fun i : Fin N => lam i.castSucc) +
      Finsupp.single N (lam (Fin.last N)) := by
  simp only [gtExponent, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

/-- Only the top interlacing row contributes to the top Laurent coefficient. -/
theorem gtPoly_top_branch_zero (q : R) (N : ℕ) (lam : Fin (N + 1) → ℤ)
    (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam) (hne : μ ≠ fun i => lam i.castSucc) :
    gtPoly q N μ
      (-Finsupp.single N ((∑ i, lam i) - ∑ i, μ i) + gtExponent lam) = 0 := by
  by_contra h
  have hs := (gtPoly_support_bounds q N μ _ h).2.1
  rw [gtPrefix_add, gtPrefix_neg, gtPrefix_single_of_le N N _ le_rfl,
    neg_zero, zero_add, ← gtPrefix_restrict N lam N le_rfl, gtPrefix_exponent] at hs
  exact hne (gtRows_eq_top_of_sum hμ hs.symm)

/-- Lemma 3.2(a): leading coefficient one, without any hypothesis on q. -/
theorem gtPoly_leading_coeff (q : R) (N : ℕ) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    gtPoly q N lam (gtExponent lam) = 1 := by
  classical
  induction N with
  | zero => simp [gtPoly, gtExponent, AddMonoidAlgebra.one_def]
  | succ N ih =>
      rw [gtPoly_coeff_succ]
      let μ : Fin N → ℤ := fun i => lam i.castSucc
      have hμ : μ ∈ gtRows lam := by
        rw [mem_gtRows]
        intro i
        exact ⟨hlam (show i.castSucc ≤ i.succ by
          change i.val ≤ i.val + 1; omega), le_rfl⟩
      rw [Finset.sum_eq_single μ]
      · have hpsi : gtPsi q lam μ = 1 := by simp [gtPsi, μ]
        rw [hpsi, one_mul]
        have he : -Finsupp.single N ((∑ i, lam i) - ∑ i, μ i) + gtExponent lam =
            gtExponent μ := by
          rw [gtExponent_split N lam, Fin.sum_univ_castSucc]
          simp [μ, add_comm, add_left_comm]
        rw [he]
        exact ih μ (gtRows_dominant hlam hμ)
      · intro ν hν hne
        rw [gtPoly_top_branch_zero q N lam ν hν hne, mul_zero]
      · exact fun h => (h hμ).elim

/-- Leading coefficient one for the original Laurent polynomials over ℤ[q]. -/
theorem gtP_leading_coeff (N : ℕ) (lam : Fin N → ℤ) (hlam : Antitone lam) :
    gtP N lam (gtExponent lam) = 1 := by
  rw [← gtPoly_X_eq_gtP]
  exact gtPoly_leading_coeff _ _ _ hlam

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtRows_eq_top_of_sum
#print axioms VOA.DeligneAudit.D4Char.gtPoly_top_branch_zero
#print axioms VOA.DeligneAudit.D4Char.gtPoly_leading_coeff
#print axioms VOA.DeligneAudit.D4Char.gtP_leading_coeff
