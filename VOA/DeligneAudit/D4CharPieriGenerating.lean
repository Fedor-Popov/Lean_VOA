import VOA.DeligneAudit.D4CharPieriBranch

/-! The all-rank GT induction for the generating e-Pieri identity. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

variable {R : Type*} [CommRing R]

noncomputable section

/-- Lemma E in generating form, for every dominant integer weight and every rank. -/
theorem gtEval_pieri_generating (q : Rˣ) (u : ℕ → Rˣ) (z : R) (N : ℕ)
    (lam : Fin N → ℤ) (hlam : Antitone lam) :
    (∏ i : Fin N, (1 + z * (u i : R))) * gtEval (q : R) u N lam =
      pieriRaiseSum q z N (gtEval (q : R) u N) lam := by
  classical
  induction N with
  | zero => simp [gtEval, pieriRaiseSum, pieriRowCoeff, pieriStateSize]
  | succ N ih =>
      change (∏ i : Fin (N + 1), (1 + z * (u i : R))) *
        gtBranch (q : R) (u N) lam (gtEval (q : R) u N) =
        pieriRaiseSum q z (N + 1)
          (fun l => gtBranch (q : R) (u N) l (gtEval (q : R) u N)) lam
      rw [← pieri_branch_intertwine q z (u N) lam hlam, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      unfold gtBranch
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [← ih μ (gtRows_dominant hlam hμ)]
      ring

variable {S : Type*} [CommRing S]

theorem pieriPower_map (φ : R →+* S) (v : Rˣ) (d : ℤ) :
    φ (pieriPower v d) = pieriPower (Units.map φ v) d := by
  simp only [pieriPower, ← map_zpow]
  rfl

theorem gtEval_map (φ : R →+* S) (q : R) (u : ℕ → Rˣ) (N : ℕ) (lam : Fin N → ℤ) :
    φ (gtEval q u N lam) = gtEval (φ q) (fun i => Units.map φ (u i)) N lam := by
  induction N with
  | zero => simp [gtEval]
  | succ N ih =>
      simp only [gtEval, map_sum, map_mul, ih]
      apply Finset.sum_congr rfl
      intro μ _
      congr 2
      · simp [gtPsi, map_prod, A2.map_qbinom]
      · exact pieriPower_map φ (u N) _

theorem pieriRowCoeff_map (φ : R →+* S) (q : Rˣ) (N : ℕ) (lam : Fin N → ℤ)
    (s : Fin N → Bool) :
    φ (pieriRowCoeff q N lam s) = pieriRowCoeff (Units.map φ q) N lam s := by
  cases N with
  | zero => exact φ.map_one
  | succ N =>
      simp only [pieriRowCoeff, map_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [pieriBond]
      split_ifs <;> simp [pieriPower_map]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtEval_pieri_generating
#print axioms VOA.DeligneAudit.D4Char.gtEval_map
#print axioms VOA.DeligneAudit.D4Char.pieriRowCoeff_map
