import VOA.DeligneAudit.D4CharMixedFive

/-! Exact GL_5 to GL_4 mixed GT branching for the constant-term down-step. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

/-- The mixed GL_4 row, with no separating zero. -/
def gtMixedFourRow (a b c d : ℤ) : Fin 4 → ℤ := ![a, b, -d, -c]

theorem gtMixedFourRow_sum (a b c d : ℤ) :
    (∑ i, gtMixedFourRow a b c d i) = a + b - c - d := by
  simp [gtMixedFourRow, Fin.sum_univ_succ]
  ring

theorem gtMixedFourRow_eta (μ : Fin 4 → ℤ) :
    gtMixedFourRow (μ 0) (μ 1) (-μ 3) (-μ 2) = μ := by
  ext i
  fin_cases i <;> simp [gtMixedFourRow]

/-- Interlacing across the middle zero is two independent rank-three interlacings. -/
theorem gtMixedFour_mem_five (a b c d A B C D : ℤ) :
    gtMixedFourRow A B C D ∈ gtRows (gtMixedFiveRow a b c d) ↔
      (![A, B] : Fin 2 → ℤ) ∈ gtRows ![a, b, 0] ∧
        (![C, D] : Fin 2 → ℤ) ∈ gtRows ![c, d, 0] := by
  simp only [mem_gtRows]
  constructor
  · intro hh
    have h₀ := hh 0
    have h₁ := hh 1
    have h₂ := hh 2
    have h₃ := hh 3
    change b ≤ A ∧ A ≤ a at h₀
    change 0 ≤ B ∧ B ≤ b at h₁
    change -d ≤ -D ∧ -D ≤ 0 at h₂
    change -c ≤ -C ∧ -C ≤ -d at h₃
    constructor
    · intro i
      fin_cases i
      · exact h₀
      · exact h₁
    · intro i
      fin_cases i
      · change d ≤ C ∧ C ≤ c
        omega
      · change 0 ≤ D ∧ D ≤ d
        omega
  · rintro ⟨hh, ht⟩ i
    have h₀ := hh 0
    have h₁ := hh 1
    have h₂ := ht 0
    have h₃ := ht 1
    change b ≤ A ∧ A ≤ a at h₀
    change 0 ≤ B ∧ B ≤ b at h₁
    change d ≤ C ∧ C ≤ c at h₂
    change 0 ≤ D ∧ D ≤ d at h₃
    fin_cases i
    · exact h₀
    · exact h₁
    · change -d ≤ -D ∧ -D ≤ 0
      omega
    · change -c ≤ -C ∧ -C ≤ -d
      omega

/-- The entire finite GL_5 branching set, with neither missing nor repeated lower rows. -/
theorem sum_gtMixedFiveRows {A : Type*} [AddCommMonoid A] (a b c d : ℤ)
    (f : (Fin 4 → ℤ) → A) :
    (∑ μ ∈ gtRows (gtMixedFiveRow a b c d), f μ) =
      ∑ α ∈ gtRows ![a, b, 0], ∑ β ∈ gtRows ![c, d, 0],
        f (gtMixedFourRow (α 0) (α 1) (β 0) (β 1)) := by
  classical
  have hη (α : Fin 2 → ℤ) : (![α 0, α 1] : Fin 2 → ℤ) = α := by
    ext i
    fin_cases i <;> rfl
  calc
    _ = ∑ p ∈ (gtRows ![a, b, 0]).product (gtRows ![c, d, 0]),
        f (gtMixedFourRow (p.1 0) (p.1 1) (p.2 0) (p.2 1)) := by
      refine Finset.sum_bij'
        (fun μ _ => ((![μ 0, μ 1] : Fin 2 → ℤ), (![-μ 3, -μ 2] : Fin 2 → ℤ)))
        (fun p _ => gtMixedFourRow (p.1 0) (p.1 1) (p.2 0) (p.2 1))
        ?_ ?_ ?_ ?_ ?_
      · intro μ hμ
        apply Finset.mem_product.mpr
        apply (gtMixedFour_mem_five a b c d (μ 0) (μ 1) (-μ 3) (-μ 2)).mp
        rwa [gtMixedFourRow_eta]
      · intro p hp
        apply (gtMixedFour_mem_five a b c d _ _ _ _).mpr
        simpa only [hη] using Finset.mem_product.mp hp
      · intro μ _
        exact gtMixedFourRow_eta μ
      · intro p _
        apply Prod.ext <;> ext i <;> fin_cases i <;> simp [gtMixedFourRow]
      · intro μ _
        change f μ = f (gtMixedFourRow (μ 0) (μ 1) (-μ 3) (-μ 2))
        rw [gtMixedFourRow_eta]
    _ = _ := by rw [Finset.product_eq_sprod, Finset.sum_product]

/-- The GT branching coefficient factors, including the reversed negative block. -/
theorem gtMixedFive_psi_factor (q : R) (a b c d : ℤ) (α β : Fin 2 → ℤ)
    (hβ : β ∈ gtRows ![c, d, 0]) :
    gtPsi q (gtMixedFiveRow a b c d)
      (gtMixedFourRow (α 0) (α 1) (β 0) (β 1)) =
        gtPsi q ![a, b, 0] α * gtPsi q ![c, d, 0] β := by
  have hlam : gtDual (![c, d, 0] : Fin 3 → ℤ) = ![0, -d, -c] := by
    ext i
    fin_cases i <;> simp [gtDual]
  have hμ : gtDual β = (![-β 1, -β 0] : Fin 2 → ℤ) := by
    ext i
    fin_cases i <;> simp [gtDual]
  have ht := gtPsi_dual q ![c, d, 0] β hβ
  rw [hlam, hμ] at ht
  rw [← ht]
  simp [gtPsi, gtMixedFiveRow, gtMixedFourRow, Fin.prod_univ_succ]
  ring

/-- The fifth-variable exponent is the difference of the positive and negative size gains. -/
theorem gtMixedFive_branch_degree (a b c d : ℤ) (α β : Fin 2 → ℤ) :
    (∑ i, gtMixedFiveRow a b c d i) -
        (∑ i, gtMixedFourRow (α 0) (α 1) (β 0) (β 1) i) =
      (a + b - ∑ i, α i) - (c + d - ∑ i, β i) := by
  rw [gtMixedFiveRow_sum, gtMixedFourRow_sum]
  simp only [Fin.sum_univ_two]
  ring

/-- The full mixed branching formula used before taking the fifth-variable constant term. -/
theorem gtMixedFive_branching (q : R) (u : ℕ → Rˣ) (a b c d : ℤ) :
    gtEval q u 5 (gtMixedFiveRow a b c d) =
      ∑ α ∈ gtRows ![a, b, 0], ∑ β ∈ gtRows ![c, d, 0],
        (gtPsi q ![a, b, 0] α * gtPsi q ![c, d, 0] β) *
          ((u 4) ^ ((a + b - ∑ i, α i) - (c + d - ∑ i, β i)) : Rˣ) *
            gtEval q u 4 (gtMixedFourRow (α 0) (α 1) (β 0) (β 1)) := by
  rw [gtEval, sum_gtMixedFiveRows]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β hβ
  rw [gtMixedFive_psi_factor q a b c d α β hβ, gtMixedFive_branch_degree]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtMixedFourRow_sum
#print axioms VOA.DeligneAudit.D4Char.gtMixedFourRow_eta
#print axioms VOA.DeligneAudit.D4Char.gtMixedFour_mem_five
#print axioms VOA.DeligneAudit.D4Char.sum_gtMixedFiveRows
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_psi_factor
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_branch_degree
#print axioms VOA.DeligneAudit.D4Char.gtMixedFive_branching
