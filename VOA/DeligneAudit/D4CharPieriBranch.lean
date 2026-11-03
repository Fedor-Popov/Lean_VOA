import VOA.DeligneAudit.D4CharPieriRows

/-! GT branching commutes with the generating form of the e-Pieri rule. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

theorem pieriRaise_sum {N : ℕ} (lam : Fin N → ℤ) (s : Fin N → Bool) :
    (∑ i, pieriRaise lam s i) = (∑ i, lam i) + (pieriStateSize s : ℤ) := by
  have h : ∀ b : Bool, pieriBit b = (b.toNat : ℤ) := by
    intro b
    cases b <;> rfl
  simp [pieriRaise, pieriStateSize, Finset.sum_add_distrib, h]

theorem pieriLower_sum {N : ℕ} (lam : Fin N → ℤ) (s : Fin N → Bool) :
    (∑ i, pieriLower lam s i) = (∑ i, lam i) - (pieriStateSize s : ℤ) := by
  have h : ∀ b : Bool, pieriBit b = (b.toNat : ℤ) := by
    intro b
    cases b <;> rfl
  simp [pieriLower, pieriStateSize, Finset.sum_sub_distrib, h]

@[simp] theorem pieriLower_raise {N : ℕ} (lam : Fin N → ℤ) (s : Fin N → Bool) :
    pieriLower (pieriRaise lam s) s = lam := by
  ext i
  simp [pieriLower, pieriRaise]

theorem pieri_power_size (v : Rˣ) (z : R) (d : ℤ) (k : ℕ) :
    pieriPower v (d + k) * z ^ k = pieriPower v d * (z * (v : R)) ^ k := by
  rw [pieriPower_add, pieriPower_nat, mul_pow]
  ring

/-- A branching operator with an arbitrary function on the lower row. -/
def gtBranch (q : R) (v : Rˣ) {N : ℕ} (lam : Fin (N + 1) → ℤ)
    (f : (Fin N → ℤ) → R) : R :=
  ∑ μ ∈ gtRows lam, gtPsi q lam μ *
    pieriPower v ((∑ i, lam i) - ∑ i, μ i) * f μ

/-- All elementary degrees at once. -/
def pieriRaiseSum (q : Rˣ) (z : R) (N : ℕ) (f : (Fin N → ℤ) → R)
    (lam : Fin N → ℤ) : R :=
  ∑ s : Fin N → Bool, z ^ pieriStateSize s * pieriRowCoeff q N lam s * f (pieriRaise lam s)

theorem gtBranch_box (q : R) (v : Rˣ) {N : ℕ} (lam : Fin (N + 1) → ℤ)
    (f : (Fin N → ℤ) → R) (B : Finset (Fin N → ℤ)) (hB : gtRows lam ⊆ B) :
    gtBranch q v lam f = ∑ μ ∈ B, gtPsiZero q lam μ *
      pieriPower v ((∑ i, lam i) - ∑ i, μ i) * f μ := by
  classical
  unfold gtBranch
  calc
    _ = ∑ μ ∈ gtRows lam, gtPsiZero q lam μ *
        pieriPower v ((∑ i, lam i) - ∑ i, μ i) * f μ := by
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [gtPsiZero_of_mem q lam μ hμ]
    _ = _ := Finset.sum_subset hB fun μ _ hμ => by
      rw [gtPsiZero_of_not_mem q lam μ hμ, zero_mul, zero_mul]

theorem gtBranch_one_raise (q : Rˣ) (z : R) (v : Rˣ) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (f : (Fin N → ℤ) → R) (t : Fin N → Bool) :
    (∑ μ ∈ gtRows lam, gtPsi (q : R) lam μ *
      pieriPower v ((∑ i, lam i) - ∑ i, μ i) *
        (z ^ pieriStateSize t * pieriRowCoeff q N μ t * f (pieriRaise μ t))) =
    ∑ ν ∈ pieriRowBox lam, pieriPower v ((∑ i, lam i) - ∑ i, ν i) *
      ((z * (v : R)) ^ pieriStateSize t *
        (gtPsiZero (q : R) lam (pieriLower ν t) * pieriRowCoeff q N (pieriLower ν t) t)) *
      f ν := by
  have h := gtPsiZero_raise_sum (q : R) lam t (fun ν =>
    pieriPower v ((∑ i, lam i) - ∑ i, pieriLower ν t i) *
      (z ^ pieriStateSize t * pieriRowCoeff q N (pieriLower ν t) t * f ν))
  simp only [pieriLower_raise] at h
  calc
    _ = _ := by simpa only [mul_assoc] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ν _
      rw [pieriLower_sum, show (∑ i, lam i) - ((∑ i, ν i) -
        (pieriStateSize t : ℤ)) = ((∑ i, lam i) - ∑ i, ν i) + pieriStateSize t by ring]
      have hp := pieri_power_size v z ((∑ i, lam i) - ∑ i, ν i) (pieriStateSize t)
      linear_combination
        (gtPsiZero (q : R) lam (pieriLower ν t) *
          pieriRowCoeff q N (pieriLower ν t) t * f ν) * hp

theorem gtBranch_raise_sum (q : Rˣ) (z : R) (v : Rˣ) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (f : (Fin N → ℤ) → R) :
    gtBranch (q : R) v lam (pieriRaiseSum q z N f) =
    ∑ ν ∈ pieriRowBox lam, pieriPower v ((∑ i, lam i) - ∑ i, ν i) *
      (∑ t : Fin N → Bool, (z * (v : R)) ^ pieriStateSize t *
        (gtPsiZero (q : R) lam (pieriLower ν t) * pieriRowCoeff q N (pieriLower ν t) t)) *
      f ν := by
  unfold gtBranch pieriRaiseSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [gtBranch_one_raise]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem pieriRaiseSum_branch (q : Rˣ) (z : R) (v : Rˣ) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (f : (Fin N → ℤ) → R) :
    pieriRaiseSum q z (N + 1) (fun l => gtBranch (q : R) v l f) lam =
    ∑ ν ∈ pieriRowBox lam, pieriPower v ((∑ i, lam i) - ∑ i, ν i) *
      (∑ s : Fin (N + 1) → Bool, (z * (v : R)) ^ pieriStateSize s *
        (pieriRowCoeff q (N + 1) lam s * gtPsiZero (q : R) (pieriRaise lam s) ν)) * f ν := by
  unfold pieriRaiseSum
  simp_rw [gtBranch_box _ v _ f _ (gtRows_raise_subset_box lam _), Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ν _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [pieriRaise_sum, show (∑ i, lam i) + (pieriStateSize s : ℤ) - (∑ i, ν i) =
    ((∑ i, lam i) - ∑ i, ν i) + pieriStateSize s by ring]
  have hp := pieri_power_size v z ((∑ i, lam i) - ∑ i, ν i) (pieriStateSize s)
  linear_combination
    (pieriRowCoeff q (N + 1) lam s * gtPsiZero (q : R) (pieriRaise lam s) ν * f ν) * hp

/-- The complete coefficient-comparison step needed for the GT induction. -/
theorem pieri_branch_intertwine (q : Rˣ) (z : R) (v : Rˣ) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (hlam : Antitone lam) (f : (Fin N → ℤ) → R) :
    (1 + z * (v : R)) * gtBranch (q : R) v lam (pieriRaiseSum q z N f) =
      pieriRaiseSum q z (N + 1) (fun l => gtBranch (q : R) v l f) lam := by
  rw [gtBranch_raise_sum, pieriRaiseSum_branch, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  rw [pieri_e_step_rows q (z * (v : R)) N lam hlam ν]
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriRaise_sum
#print axioms VOA.DeligneAudit.D4Char.pieriLower_sum
#print axioms VOA.DeligneAudit.D4Char.gtBranch_box
#print axioms VOA.DeligneAudit.D4Char.gtBranch_one_raise
#print axioms VOA.DeligneAudit.D4Char.gtBranch_raise_sum
#print axioms VOA.DeligneAudit.D4Char.pieriRaiseSum_branch
#print axioms VOA.DeligneAudit.D4Char.pieri_branch_intertwine
