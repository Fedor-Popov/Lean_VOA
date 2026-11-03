import VOA.DeligneAudit.D4CharQYFactors

/-!
Identity Y in every rank. Both rows are partitions, as required by referee repair R2.
Its normalized e-Pieri consequence is restricted to dominant raised rows.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Identity Y before cancelling the normalization unit of the raised partition. -/
theorem gtY_normalized (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin N → ℤ) (S : Finset (Fin N)) (hlam : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hraise : Antitone (pieriWeight lam S)) :
    pieriCoeff q lam S * (gtNormUnit q h lam : R) =
      gtExitCoeff q (pieriWeight lam S) S * (gtNormUnit q h (pieriWeight lam S) : R) := by
  have hpos' : ∀ i, 0 ≤ pieriWeight lam S i := by
    intro i
    have hi := hpos i
    simp only [pieriWeight]
    split_ifs <;> omega
  rw [pieriCoeff_enter_product, gtNormUnit_product q h lam hlam hpos,
    gtNormUnit_product q h (pieriWeight lam S) hraise hpos', gtExitCoeff,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [gtGapInt_pieriWeight]
  exact gtY_local q h _ _ _

/-- STEP2 identity Y, with unit division and no field-of-fractions assumption. -/
theorem gtY (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin N → ℤ) (S : Finset (Fin N)) (hlam : Antitone lam)
    (hpos : ∀ i, 0 ≤ lam i) (hraise : Antitone (pieriWeight lam S)) :
    gtExitCoeff q (pieriWeight lam S) S = pieriCoeff q lam S *
      (gtNormUnit q h lam : R) * ((gtNormUnit q h (pieriWeight lam S))⁻¹ : Rˣ) := by
  rw [gtY_normalized q h lam S hlam hpos hraise, mul_assoc, Units.mul_inv, mul_one]

/-- Normalized e-Pieri with the exiting-edge coefficients used in mixed Cauchy. -/
theorem gtQ_ePieri (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ) (N : ℕ)
    (lam : Fin N → ℤ) (hlam : Antitone lam) (hpos : ∀ i, 0 ≤ lam i) (r : ℕ) :
    pieriElementary u N r * gtQ q h u N lam =
      ∑ S ∈ ((Finset.univ : Finset (Fin N)).powersetCard r).filter
        (fun S => Antitone (pieriWeight lam S)),
        gtExitCoeff q (pieriWeight lam S) S * gtQ q h u N (pieriWeight lam S) := by
  classical
  rw [gtQ, mul_left_comm, ePieri q u N lam hlam r, pieriRHS, Finset.mul_sum]
  have hf : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard r,
      (gtNormUnit q h lam : R) *
        (pieriCoeff q lam S * gtEval q u N (pieriWeight lam S))) =
      ∑ S ∈ ((Finset.univ : Finset (Fin N)).powersetCard r).filter
        (fun S => Antitone (pieriWeight lam S)),
        (gtNormUnit q h lam : R) *
          (pieriCoeff q lam S * gtEval q u N (pieriWeight lam S)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hbad
    have hn : ¬ Antitone (pieriWeight lam S) := by
      intro hn
      exact hbad (Finset.mem_filter.mpr ⟨hS, hn⟩)
    rw [pieriCoeff_zero_of_not_dominant q lam S hlam hn, zero_mul, mul_zero]
  rw [hf]
  apply Finset.sum_congr rfl
  intro S hS
  have hraise := (Finset.mem_filter.mp hS).2
  simp only [gtQ, ← mul_assoc]
  rw [← gtY_normalized q h lam S hlam hpos hraise]
  ring

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtY_normalized
#print axioms VOA.DeligneAudit.D4Char.gtY
#print axioms VOA.DeligneAudit.D4Char.gtQ_ePieri
