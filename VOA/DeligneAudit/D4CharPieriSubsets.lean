import VOA.DeligneAudit.D4CharPieriGenerating

/-! Translate the Boolean-state generating identity to the existing finite-subset API. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

def pieriIndicator {N : ℕ} (S : Finset (Fin N)) : Fin N → Bool := fun i => decide (i ∈ S)

def pieriIndicatorEquiv (N : ℕ) : Finset (Fin N) ≃ (Fin N → Bool) where
  toFun := pieriIndicator
  invFun := fun s => Finset.univ.filter fun i => s i = true
  left_inv := by intro S; ext i; simp [pieriIndicator]
  right_inv := by intro s; funext i; cases h : s i <;> simp [pieriIndicator, h]

theorem pieriStateSize_indicator {N : ℕ} (S : Finset (Fin N)) :
    pieriStateSize (pieriIndicator S) = S.card := by
  have h : ∀ i : Fin N, (pieriIndicator S i).toNat = if i ∈ S then 1 else 0 := by
    intro i
    by_cases hi : i ∈ S <;> simp [pieriIndicator, hi]
  simp only [pieriStateSize, h]
  simp

theorem pieriRaise_indicator {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    pieriRaise lam (pieriIndicator S) = pieriWeight lam S := by
  ext i
  simp [pieriRaise, pieriWeight, pieriIndicator, pieriBit]

/-- Dominance makes the integer powers agree with the natural exponents in `pieriCoeff`. -/
theorem pieriRowCoeff_indicator (q : Rˣ) (N : ℕ) (lam : Fin N → ℤ)
    (hlam : Antitone lam) (S : Finset (Fin N)) :
    pieriRowCoeff q N lam (pieriIndicator S) = pieriCoeff (q : R) lam S := by
  classical
  unfold pieriCoeff
  rw [← Fintype.prod_extend_by_one S]
  cases N with
  | zero => simp [pieriRowCoeff]
  | succ N =>
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, true_or, if_true, ite_self, one_mul]
      apply Finset.prod_congr rfl
      intro i _
      have hp : pieriPrevious i.succ = i.castSucc := by
        ext
        simp [pieriPrevious]
      have hd : 0 ≤ lam i.castSucc - lam i.succ := by
        have := hlam (show i.castSucc ≤ i.succ by change i.val ≤ i.val + 1; omega)
        omega
      simp only [pieriBond, pieriIndicator, hp, Fin.val_succ, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, false_or, pieriPower_nonneg q _ hd]
      by_cases hs : i.succ ∈ S <;> by_cases ht : i.castSucc ∈ S <;> simp [hs, ht]

/-- Generating e-Pieri on the original subset weights and coefficients. -/
theorem gtEval_pieri_subsets (q : Rˣ) (u : ℕ → Rˣ) (z : R) (N : ℕ)
    (lam : Fin N → ℤ) (hlam : Antitone lam) :
    (∏ i : Fin N, (1 + z * (u i : R))) * gtEval (q : R) u N lam =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
        z ^ S.card * pieriCoeff (q : R) lam S * gtEval (q : R) u N (pieriWeight lam S) := by
  classical
  have h := gtEval_pieri_generating q u z N lam hlam
  unfold pieriRaiseSum at h
  rw [← (pieriIndicatorEquiv N).sum_comp] at h
  change _ = ∑ S : Finset (Fin N), z ^ pieriStateSize (pieriIndicator S) *
    pieriRowCoeff q N lam (pieriIndicator S) * gtEval (q : R) u N
      (pieriRaise lam (pieriIndicator S)) at h
  simp only [pieriStateSize_indicator, pieriRowCoeff_indicator q N lam hlam,
    pieriRaise_indicator] at h
  have hp : (Finset.univ : Finset (Finset (Fin N))) =
      (Finset.univ : Finset (Fin N)).powerset := by ext S; simp
  rwa [hp] at h

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriStateSize_indicator
#print axioms VOA.DeligneAudit.D4Char.pieriRaise_indicator
#print axioms VOA.DeligneAudit.D4Char.pieriRowCoeff_indicator
#print axioms VOA.DeligneAudit.D4Char.gtEval_pieri_subsets
