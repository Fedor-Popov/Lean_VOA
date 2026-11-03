import VOA.DeligneAudit.D4CharGTLeading

/-! Leading-monomial independence over any commutative coefficient ring. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- An integer statistic strictly increasing along strict dominance. -/
def gtDominanceHeight {N : ℕ} (lam : Fin N → ℤ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), gtPrefix (gtExponent lam) k

/-- At equal or smaller dominance height, a different top row cannot contribute. -/
theorem gtPoly_coeff_zero_of_height (q : R) (N : ℕ) (lam ν : Fin N → ℤ)
    (hne : lam ≠ ν) (hh : gtDominanceHeight ν ≤ gtDominanceHeight lam) :
    gtPoly q N ν (gtExponent lam) = 0 := by
  by_contra h
  have hd := (gtPoly_support_bounds q N ν (gtExponent lam) h).2.2
  have hs : gtDominanceHeight lam ≤ gtDominanceHeight ν := by
    apply Finset.sum_le_sum
    intro k hk
    exact hd k (by simp only [Finset.mem_range] at hk; omega)
  have he : ∀ k ∈ Finset.range (N + 1),
      gtPrefix (gtExponent lam) k = gtPrefix (gtExponent ν) k :=
    (Finset.sum_eq_sum_iff_of_le (fun k hk =>
      hd k (by simp only [Finset.mem_range] at hk; omega))).mp (le_antisymm hs hh)
  apply hne
  funext i
  have h₀ := he i.val (by simp)
  have h₁ := he (i.val + 1) (by simp)
  rw [gtPrefix_succ, gtPrefix_succ, gtExponent_apply, gtExponent_apply] at h₁
  omega

/-- GT polynomials at dominant integer rows are linearly independent over any ring. -/
theorem gtPoly_linearIndependent (q : R) (N : ℕ) :
    LinearIndependent R (fun lam : {lam : Fin N → ℤ // Antitone lam} =>
      gtPoly q N lam.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  by_contra hgi
  let T := s.filter fun lam => g lam ≠ 0
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨lam, hlamT, hmax⟩ := T.exists_max_image
    (fun lam => gtDominanceHeight lam.val) hT
  obtain ⟨hlam, hglam⟩ := Finset.mem_filter.mp hlamT
  have he := congrArg
    (fun p : AddMonoidAlgebra R (ℕ →₀ ℤ) => p.coeff (gtExponent lam.val)) hg
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
  have hsum : (∑ ν ∈ s, g ν * (gtPoly q N ν.val).coeff (gtExponent lam.val)) = g lam := by
    rw [Finset.sum_eq_single lam]
    · change g lam * gtPoly q N lam.val (gtExponent lam.val) = g lam
      rw [gtPoly_leading_coeff q N lam.val lam.property, mul_one]
    · intro ν hν hne
      by_cases hgv : g ν = 0
      · rw [hgv, zero_mul]
      · change g ν * gtPoly q N ν.val (gtExponent lam.val) = 0
        rw [gtPoly_coeff_zero_of_height q N lam.val ν.val
          (fun h => hne (Subtype.ext h.symm))
          (hmax ν (Finset.mem_filter.mpr ⟨hν, hgv⟩)), mul_zero]
    · exact fun h => (h hlam).elim
  exact hglam (hsum.symm.trans he)

/-- Lemma 3.2(a) for the existing polynomials over ℤ[q]. -/
theorem gtP_linearIndependent (N : ℕ) :
    LinearIndependent (Polynomial ℤ)
      (fun lam : {lam : Fin N → ℤ // Antitone lam} => gtP N lam.val) := by
  simpa only [gtPoly_X_eq_gtP] using
    gtPoly_linearIndependent (Polynomial.X : Polynomial ℤ) N

/-- The same coefficient comparison remains available after arbitrary specialization of q. -/
theorem gtEval_formal_linearIndependent (q : R) (N : ℕ) :
    LinearIndependent R (fun lam : {lam : Fin N → ℤ // Antitone lam} =>
      gtEval (AddMonoidAlgebra.single 0 q) (gtLaurentVariable R) N lam.val) := by
  simpa only [gtPoly_eq_gtEval] using gtPoly_linearIndependent q N

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtPoly_coeff_zero_of_height
#print axioms VOA.DeligneAudit.D4Char.gtPoly_linearIndependent
#print axioms VOA.DeligneAudit.D4Char.gtP_linearIndependent
#print axioms VOA.DeligneAudit.D4Char.gtEval_formal_linearIndependent
