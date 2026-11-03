import VOA.DeligneAudit.D4CharCauchySlice

/-! Raising operators on the free module of integer rows and their GT evaluation. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem pieriWeight_lowerSubset {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    pieriWeight (gtLowerSubset lam S) S = lam := by
  ext i
  simp [pieriWeight, gtLowerSubset]

theorem gtLowerSubset_pieriWeight {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    gtLowerSubset (pieriWeight lam S) S = lam := by
  ext i
  simp [pieriWeight, gtLowerSubset]

theorem gtLowerSubset_sum {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) :
    (∑ i, gtLowerSubset lam S i) = (∑ i, lam i) - S.card := by
  simp [gtLowerSubset, Finset.sum_sub_distrib]

/-- One vertical strip, acting on finitely supported row coefficients. -/
def gtPieriUp (q : R) {N : ℕ} (S : Finset (Fin N)) :
    ((Fin N → ℤ) →₀ R) →ₗ[R] ((Fin N → ℤ) →₀ R) :=
  Finsupp.linearCombination R fun lam =>
    Finsupp.single (pieriWeight lam S) (pieriCoeff q lam S)

/-- Reindexing a raising operator at an output row has a unique preimage. -/
theorem gtPieriUp_apply (q : R) {N : ℕ} (S : Finset (Fin N))
    (v : (Fin N → ℤ) →₀ R) (lam : Fin N → ℤ) :
    gtPieriUp q S v lam = v (gtLowerSubset lam S) *
      pieriCoeff q (gtLowerSubset lam S) S := by
  classical
  change (∑ nu ∈ v.support,
    v nu • Finsupp.single (pieriWeight nu S) (pieriCoeff q nu S)) lam = _
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  rw [Finset.sum_eq_single (gtLowerSubset lam S)]
  · simp [pieriWeight_lowerSubset]
  · intro nu _ hn
    have he : pieriWeight nu S ≠ lam := by
      intro he
      have hh := congrArg (fun row => gtLowerSubset row S) he
      dsimp only at hh
      rw [gtLowerSubset_pieriWeight] at hh
      exact hn hh
    simp [he]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

theorem gtPieriUp_eval (q : R) (u : ℕ → Rˣ) {N : ℕ} (S : Finset (Fin N))
    (v : (Fin N → ℤ) →₀ R) :
    Finsupp.linearCombination R (gtEval q u N) (gtPieriUp q S v) =
      ∑ lam ∈ v.support, v lam * pieriCoeff q lam S *
        gtEval q u N (pieriWeight lam S) := by
  classical
  have he : gtPieriUp q S v = ∑ lam ∈ v.support,
      v lam • Finsupp.single (pieriWeight lam S) (pieriCoeff q lam S) := rfl
  rw [he, map_sum]
  simp only [map_smul, Finsupp.linearCombination_single, smul_eq_mul, mul_assoc]

/-- e-Pieri after evaluating any finite linear combination of dominant rows. -/
theorem gtPieriUp_eval_card (q : R) (u : ℕ → Rˣ) {N : ℕ} (j : ℕ)
    (v : (Fin N → ℤ) →₀ R) (hv : ∀ lam ∈ v.support, Antitone lam) :
    Finsupp.linearCombination R (gtEval q u N)
      (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, gtPieriUp q S v) =
        pieriElementary u N j * Finsupp.linearCombination R (gtEval q u N) v := by
  classical
  rw [map_sum]
  simp_rw [gtPieriUp_eval]
  rw [Finset.sum_comm, Finsupp.linearCombination_apply, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro lam hm
  simp only [smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have he := ePieri q u N lam (hv lam hm) j
  change pieriElementary u N j * gtEval q u N lam =
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      pieriCoeff q lam S * gtEval q u N (pieriWeight lam S) at he
  rw [← he]
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.pieriWeight_lowerSubset
#print axioms VOA.DeligneAudit.D4Char.gtLowerSubset_pieriWeight
#print axioms VOA.DeligneAudit.D4Char.gtLowerSubset_sum
#print axioms VOA.DeligneAudit.D4Char.gtPieriUp_apply
#print axioms VOA.DeligneAudit.D4Char.gtPieriUp_eval
#print axioms VOA.DeligneAudit.D4Char.gtPieriUp_eval_card
