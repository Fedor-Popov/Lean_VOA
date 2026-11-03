import VOA.DeligneAudit.D4CharGTBoundary

/-! The coefficient comparison of Lemma E in GT row notation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

/-- The e-Pieri coefficient on Boolean subsets, with integer exponents. -/
def pieriRowCoeff (q : Rˣ) : (N : ℕ) → (Fin N → ℤ) → (Fin N → Bool) → R
  | 0, _, _ => 1
  | N + 1, lam, s =>
      ∏ i : Fin N, pieriBond q (lam i.castSucc - lam i.succ) (s i.castSucc) (s i.succ)

theorem pieri_left_row_product (q : Rˣ) (N : ℕ) (lam : Fin (N + 1) → ℤ)
    (μ : Fin N → ℤ) (s : Fin (N + 1) → Bool) :
    pieriRowCoeff q (N + 1) lam s * gtPsiZero (q : R) (pieriRaise lam s) μ =
      ∏ i : Fin N, pieriW q (lam i.castSucc - lam i.succ) (lam i.castSucc - μ i)
        (s i.castSucc) (s i.succ) := by
  simp only [pieriRowCoeff, gtPsiZero, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have h₁ : pieriRaise lam s i.castSucc - pieriRaise lam s i.succ =
      lam i.castSucc - lam i.succ + pieriBit (s i.castSucc) - pieriBit (s i.succ) := by
    dsimp [pieriRaise]
    ring
  have h₂ : pieriRaise lam s i.castSucc - μ i =
      lam i.castSucc - μ i + pieriBit (s i.castSucc) := by
    dsimp [pieriRaise]
    ring
  simp only [pieriW, pieriBond, h₁, h₂, mul_comm]

theorem pieri_right_row_product (q : Rˣ) (N : ℕ) (lam : Fin (N + 2) → ℤ)
    (μ : Fin (N + 1) → ℤ) (t : Fin (N + 1) → Bool) :
    gtPsiZero (q : R) lam (pieriLower μ t) * pieriRowCoeff q (N + 1) (pieriLower μ t) t =
      (∏ i, intQbinom (q : R) (lam i.castSucc - lam i.succ)
        (lam i.castSucc - μ i + pieriBit (t i))) *
      ∏ i : Fin N, pieriBond q
        ((lam i.castSucc.castSucc - lam i.castSucc.succ) -
          (lam i.castSucc.castSucc - μ i.castSucc) + (lam i.succ.castSucc - μ i.succ) + 1)
        (t i.castSucc) (t i.succ) := by
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    congr 1
    dsimp [pieriLower]
    ring
  · apply Finset.prod_congr rfl
    intro i _
    cases h₁ : t i.castSucc <;> cases h₂ : t i.succ <;>
      simp [pieriBond, pieriLower, pieriBit, h₁, h₂]
    congr 2
    ring

/-- Equality of the two GT branching coefficients, summed over all elementary degrees. -/
theorem pieri_e_step_rows (q : Rˣ) (z : R) (N : ℕ) (lam : Fin (N + 1) → ℤ)
    (hlam : Antitone lam) (μ : Fin N → ℤ) :
    (∑ s : Fin (N + 1) → Bool, z ^ pieriStateSize s *
      (pieriRowCoeff q (N + 1) lam s * gtPsiZero (q : R) (pieriRaise lam s) μ)) =
    (1 + z) * ∑ t : Fin N → Bool, z ^ pieriStateSize t *
      (gtPsiZero (q : R) lam (pieriLower μ t) * pieriRowCoeff q N (pieriLower μ t) t) := by
  classical
  cases N with
  | zero =>
      rw [← (Fin.consEquiv fun _ : Fin 1 => Bool).sum_comp]
      simp [pieriRowCoeff, gtPsiZero, pieriStateSize, Fintype.sum_prod_type, add_comm]
  | succ N =>
      have ha : ∀ i : Fin (N + 1), 0 ≤ lam i.castSucc - lam i.succ := by
        intro i
        have := hlam (show i.castSucc ≤ i.succ by change i.val ≤ i.val + 1; omega)
        omega
      simp_rw [pieri_left_row_product, pieri_right_row_product]
      simpa only [mul_assoc] using pieri_e_step q z N
        (fun i => lam i.castSucc - lam i.succ) (fun i => lam i.castSucc - μ i) ha

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieri_left_row_product
#print axioms VOA.DeligneAudit.D4Char.pieri_right_row_product
#print axioms VOA.DeligneAudit.D4Char.pieri_e_step_rows
