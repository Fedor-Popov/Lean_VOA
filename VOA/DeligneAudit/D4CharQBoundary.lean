import VOA.DeligneAudit.D4CharQBranching

/-! The zero-extended normalized branching coefficient needed by identities X and B. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- Reciprocal Pochhammer, with the integer boundary convention of STEP2. -/
def gtInvPoch (q : R) (h : PochhammerUnits q) (d : ℤ) : R :=
  if 0 ≤ d then ((gtPochUnit q h d.toNat)⁻¹ : Rˣ) else 0

/-- The normalized coefficient as a product valid on every integer row. -/
def gtQCoeff (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) : R :=
  (∏ i, CarrierChain.qpochGen q (gtGap μ i) *
    gtInvPoch q h (lam i.castSucc - μ i) * gtInvPoch q h (μ i - lam i.succ)) *
      gtInvPoch q h (lam (Fin.last N))

/-- On the allowed region the zero extension is the normalized GT coefficient. -/
theorem gtQCoeff_of_mem (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∈ gtRows lam)
    (hlast : 0 ≤ lam (Fin.last N)) : gtQCoeff q h lam μ = gtQBranch q h lam μ := by
  rw [gtQBranch_product q h lam μ hμ, gtQCoeff, gtInvPoch, if_pos hlast]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hi := (mem_gtRows lam μ).mp hμ i
  simp only [gtInvPoch, if_pos (sub_nonneg.mpr hi.1),
    if_pos (sub_nonneg.mpr hi.2)]

/-- Negative last parts contribute zero, even at rank one. -/
theorem gtQCoeff_of_last_neg (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hlast : lam (Fin.last N) < 0) :
    gtQCoeff q h lam μ = 0 := by
  simp [gtQCoeff, gtInvPoch, not_le.mpr hlast]

/-- Failure of either interlacing inequality kills the corresponding factor. -/
theorem gtQCoeff_of_not_mem (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) (hμ : μ ∉ gtRows lam) :
    gtQCoeff q h lam μ = 0 := by
  classical
  have hn : ¬ ∀ i, lam i.succ ≤ μ i ∧ μ i ≤ lam i.castSucc := by
    simpa only [mem_gtRows] using hμ
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have hz : (∏ j : Fin N, CarrierChain.qpochGen q (gtGap μ j) *
      gtInvPoch q h (lam j.castSucc - μ j) * gtInvPoch q h (μ j - lam j.succ)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hu : μ i ≤ lam i.castSucc
    · have hl : ¬ 0 ≤ μ i - lam i.succ := by omega
      have hz : gtInvPoch q h (μ i - lam i.succ) = 0 := if_neg hl
      rw [hz, mul_zero]
    · have hl : ¬ 0 ≤ lam i.castSucc - μ i := by omega
      have hz : gtInvPoch q h (lam i.castSucc - μ i) = 0 := if_neg hl
      rw [hz, mul_zero, zero_mul]
  exact mul_eq_zero_of_left hz _

/-- Complete boundary description, with no omitted negative integer cases. -/
theorem gtQCoeff_eq_ite (q : R) (h : PochhammerUnits q) {N : ℕ}
    (lam : Fin (N + 1) → ℤ) (μ : Fin N → ℤ) :
    gtQCoeff q h lam μ =
      if μ ∈ gtRows lam ∧ 0 ≤ lam (Fin.last N) then gtQBranch q h lam μ else 0 := by
  classical
  by_cases hm : μ ∈ gtRows lam
  · by_cases hl : 0 ≤ lam (Fin.last N)
    · rw [if_pos ⟨hm, hl⟩, gtQCoeff_of_mem q h lam μ hm hl]
    · rw [if_neg (by tauto), gtQCoeff_of_last_neg q h lam μ (by omega)]
  · rw [if_neg (by tauto), gtQCoeff_of_not_mem q h lam μ hm]

/-- Normalized branching with the explicit zero-extended product coefficient. -/
theorem gtQ_branching_product (q : R) (h : PochhammerUnits q) (u : ℕ → Rˣ)
    (N : ℕ) (lam : Fin (N + 1) → ℤ) (hlast : 0 ≤ lam (Fin.last N)) :
    gtQ q h u (N + 1) lam = ∑ μ ∈ gtRows lam,
      gtQCoeff q h lam μ * (((u N) ^ ((∑ i, lam i) - ∑ i, μ i) : Rˣ) : R) *
        gtQ q h u N μ := by
  rw [gtQ_branching]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [gtQCoeff_of_mem q h lam μ hμ hlast]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_of_mem
#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_of_last_neg
#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_of_not_mem
#print axioms VOA.DeligneAudit.D4Char.gtQCoeff_eq_ite
#print axioms VOA.DeligneAudit.D4Char.gtQ_branching_product
