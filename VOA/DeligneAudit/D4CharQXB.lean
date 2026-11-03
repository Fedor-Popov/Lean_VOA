import VOA.DeligneAudit.D4CharQTwoStates

/-!
Identities X and B in the subset notation used by e-Pieri. Ranks one and two suffice
for all Cauchy and mixed-Cauchy instances needed in the D4 character proof. The entries
are unrestricted integers, so these statements include all non-interlaced partitions.
-/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Remove one box at each selected position. -/
def gtLowerSubset {N : ℕ} (lam : Fin N → ℤ) (S : Finset (Fin N)) : Fin N → ℤ :=
  fun i => lam i - if i ∈ S then 1 else 0

/-- The signed summand F(S) in STEP2 section 5. -/
def gtXTerm (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (S : Finset (Fin (N + 1))) : R :=
  (-1) ^ S.card * gtQCoeff q h (gtLowerSubset lam S) μ *
    pieriCoeff q (gtLowerSubset lam S) S

/-- The left side of identity X. -/
def gtXSum (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R := ∑ S, gtXTerm q h lam μ S

/-- The left side of identity B, including the last-position boundary factor. -/
def gtBSum (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R :=
  ∑ S, gtXTerm q h lam μ S *
    if Fin.last N ∈ S then 1 else 1 - q ^ (lam (Fin.last N)).toNat

theorem gtX_rank_one (q : R) (h : PochhammerUnits q)
    (lam : Fin 1 → ℤ) (μ : Fin 0 → ℤ) :
    gtXSum q h lam μ = q ^ ((∑ i, lam i) - ∑ i, μ i).toNat * gtQCoeff q h lam μ := by
  have hs : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [gtXSum, hs, gtXTerm, gtQCoeff_one, gtLowerSubset, pieriCoeff]
  rw [gtInvPoch_lower]
  ring

theorem gtB_rank_one (q : R) (h : PochhammerUnits q)
    (lam : Fin 1 → ℤ) (μ : Fin 0 → ℤ) : gtBSum q h lam μ = 0 := by
  have hs : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [gtBSum, hs, gtXTerm, gtQCoeff_one, gtLowerSubset, pieriCoeff]
  rw [gtInvPoch_lower]
  ring

theorem gtX_rank_two (q : R) (h : PochhammerUnits q)
    (lam : Fin 2 → ℤ) (μ : Fin 1 → ℤ) :
    gtXSum q h lam μ = q ^ ((∑ i, lam i) - ∑ i, μ i).toNat * gtQCoeff q h lam μ := by
  have hs : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have ht := gtQ_two_state_total q h (lam 0) (lam 1) (μ 0)
  simp only [gtQCoeff_two, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  rw [gtXSum, hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [gtXTerm, gtQCoeff_two, gtLowerSubset, pieriCoeff, pieriPrevious, Fin.sum_univ_two]
  convert ht using 1 <;> ring

theorem gtB_rank_two (q : R) (h : PochhammerUnits q)
    (lam : Fin 2 → ℤ) (μ : Fin 1 → ℤ) : gtBSum q h lam μ = 0 := by
  have hs : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have ht := gtQ_two_state_boundary q h (lam 0) (lam 1) (μ 0)
  simp only [gtQCoeff_two, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  rw [gtBSum, hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [gtXTerm, gtQCoeff_two, gtLowerSubset, pieriCoeff, pieriPrevious]
  convert ht using 1 <;> ring

/-- Identity X for precisely the ranks consumed by the D4 mixed-Cauchy proof. -/
theorem gtX_small_rank (q : R) (h : PochhammerUnits q) {N : ℕ} (hN : N ≤ 1)
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) :
    gtXSum q h lam μ = q ^ ((∑ i, lam i) - ∑ i, μ i).toNat * gtQCoeff q h lam μ := by
  interval_cases N
  · exact gtX_rank_one q h lam μ
  · exact gtX_rank_two q h lam μ

/-- Identity B for precisely the ranks consumed by the D4 mixed-Cauchy proof. -/
theorem gtB_small_rank (q : R) (h : PochhammerUnits q) {N : ℕ} (hN : N ≤ 1)
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : gtBSum q h lam μ = 0 := by
  interval_cases N
  · exact gtB_rank_one q h lam μ
  · exact gtB_rank_two q h lam μ

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtX_rank_one
#print axioms VOA.DeligneAudit.D4Char.gtB_rank_one
#print axioms VOA.DeligneAudit.D4Char.gtX_rank_two
#print axioms VOA.DeligneAudit.D4Char.gtB_rank_two
#print axioms VOA.DeligneAudit.D4Char.gtX_small_rank
#print axioms VOA.DeligneAudit.D4Char.gtB_small_rank
