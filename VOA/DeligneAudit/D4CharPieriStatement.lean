import VOA.DeligneAudit.D4CharPieriGaussian

/-! The exact e-Pieri target and its uniform boundary cases. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

def pieriPrevious {N : ℕ} (i : Fin N) : Fin N := ⟨i.val - 1, by omega⟩

/-- Addition of the indicator of S to an integer highest weight. -/
def pieriWeight {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) : Fin N → ℤ :=
  fun i => lam i + if i ∈ S then 1 else 0

/-- Elementary symmetric polynomial in the first N variables. -/
def pieriElementary (u : ℕ → Rˣ) (N r : ℕ) : R :=
  ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard r, ∏ i ∈ S, ((u i) : R)

/-- The e-Pieri coefficient of STEP2 section 4. -/
def pieriCoeff (q : R) {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) : R :=
  ∏ i ∈ S, if i.val = 0 ∨ pieriPrevious i ∈ S then 1
    else 1 - q ^ (lam (pieriPrevious i) - lam i).toNat

def pieriRHS (q : R) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ) (r : ℕ) : R :=
  ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
    pieriCoeff q lam S * gtEval q u N (pieriWeight lam S)

/-- Lemma E as a precise target, with no upper bound on rank or highest weight. -/
def EPieri (q : R) (u : ℕ → Rˣ) : Prop :=
  ∀ (N : ℕ) (lam : Fin N → ℤ), Antitone lam → ∀ r : ℕ,
    pieriElementary u N r * gtEval q u N lam = pieriRHS q u N lam r

theorem ePieri_zero (q : R) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ) :
    pieriElementary u N 0 * gtEval q u N lam = pieriRHS q u N lam 0 := by
  have he : pieriWeight lam ∅ = lam := by ext i; simp [pieriWeight]
  simp [pieriElementary, pieriRHS, pieriCoeff, he]

/-- The top elementary symmetric function is the central shift, in every rank. -/
theorem ePieri_top (q : R) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ) :
    pieriElementary u N N * gtEval q u N lam = pieriRHS q u N lam N := by
  have hs : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
    simpa using (Finset.powersetCard_self (Finset.univ : Finset (Fin N)))
  simp only [pieriElementary, pieriRHS, hs, Finset.sum_singleton]
  simp only [pieriCoeff, Finset.mem_univ, or_true, ↓reduceIte, Finset.prod_const_one,
    one_mul]
  have he : pieriWeight lam Finset.univ = fun i => lam i + 1 := by
    ext i
    simp [pieriWeight]
  rw [he, gtEval_central_shift]
  simp

theorem ePieri_above_rank (q : R) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ)
    (r : ℕ) (hr : N < r) :
    pieriElementary u N r * gtEval q u N lam = pieriRHS q u N lam r := by
  have hs : (Finset.univ : Finset (Fin N)).powersetCard r = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hr)
  simp [pieriElementary, pieriRHS, hs]

/-- The complete rank-one base, for all integer highest weights and all r. -/
theorem ePieri_rank_one (q : R) (u : ℕ → Rˣ) (lam : Fin 1 → ℤ) (r : ℕ) :
    pieriElementary u 1 r * gtEval q u 1 lam = pieriRHS q u 1 lam r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ePieri_zero q u 1 lam
  · rcases eq_or_lt_of_le (show 1 ≤ r by omega) with hr | hr
    · subst r
      exact ePieri_top q u 1 lam
    · exact ePieri_above_rank q u 1 lam r hr

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.ePieri_zero
#print axioms VOA.DeligneAudit.D4Char.ePieri_top
#print axioms VOA.DeligneAudit.D4Char.ePieri_above_rank
#print axioms VOA.DeligneAudit.D4Char.ePieri_rank_one
