import VOA.DeligneAudit.D4CharMixedDownCT

/-! Finite, exhaustive reindexing of the rank-two branches in the mixed down-step. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

/-- All two-part partitions of a fixed size, including trailing zero parts. -/
def gtPartitionsTwo (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.antidiagonal n).filter fun p => p.2 ≤ p.1

@[simp] theorem mem_gtPartitionsTwo (n : ℕ) (p : ℕ × ℕ) :
    p ∈ gtPartitionsTwo n ↔ p.1 + p.2 = n ∧ p.2 ≤ p.1 := by
  simp [gtPartitionsTwo]

/-- The natural coordinates of every row below (a,b,0). -/
def gtDownRowsTwo (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc b a).product (Finset.Icc 0 b)

@[simp] theorem mem_gtDownRowsTwo (a b : ℕ) (p : ℕ × ℕ) :
    p ∈ gtDownRowsTwo a b ↔ b ≤ p.1 ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [gtDownRowsTwo, and_assoc]

theorem sum_gtRows_three_nat {A : Type*} [AddCommMonoid A] (a b : ℕ)
    (f : (Fin 2 → ℤ) → A) :
    (∑ μ ∈ gtRows ![(a : ℤ), (b : ℤ), 0], f μ) =
      ∑ p ∈ gtDownRowsTwo a b, f ![(p.1 : ℤ), (p.2 : ℤ)] := by
  classical
  refine Finset.sum_bij' (fun μ _ => ((μ 0).toNat, (μ 1).toNat))
    (fun p _ => ![(p.1 : ℤ), (p.2 : ℤ)]) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    have h₀ := (mem_gtRows _ _).mp hμ 0
    have h₁ := (mem_gtRows _ _).mp hμ 1
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at h₀
    change (0 : ℤ) ≤ μ 1 ∧ μ 1 ≤ b at h₁
    rw [mem_gtDownRowsTwo]
    dsimp
    omega
  · intro p hp
    have hp := (mem_gtDownRowsTwo a b p).mp hp
    apply (mem_gtRows _ _).mpr
    intro i
    fin_cases i
    · change (b : ℤ) ≤ p.1 ∧ (p.1 : ℤ) ≤ a
      omega
    · change (0 : ℤ) ≤ p.2 ∧ (p.2 : ℤ) ≤ b
      omega
  · intro μ hμ
    have h₀ := (mem_gtRows _ _).mp hμ 0
    have h₁ := (mem_gtRows _ _).mp hμ 1
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at h₀
    change (0 : ℤ) ≤ μ 1 ∧ μ 1 ≤ b at h₁
    ext i
    fin_cases i <;> simp <;> omega
  · intro p _
    simp
  · intro μ hμ
    have h₀ := (mem_gtRows _ _).mp hμ 0
    have h₁ := (mem_gtRows _ _).mp hμ 1
    change (b : ℤ) ≤ μ 0 ∧ μ 0 ≤ a at h₀
    change (0 : ℤ) ≤ μ 1 ∧ μ 1 ≤ b at h₁
    congr 1
    ext i
    fin_cases i <;> simp <;> omega

/-- Reversing all branches of a fixed size introduces precisely their nonnegative gain. -/
theorem sum_gtDownRowsTwo_reverse {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : (ℕ × ℕ) → (ℕ × ℕ) → A) :
    (∑ p ∈ gtPartitionsTwo n, ∑ c ∈ gtDownRowsTwo p.1 p.2, f p c) =
      ∑ k ∈ Finset.range (n + 1), ∑ c ∈ gtPartitionsTwo (n - k),
        ∑ p ∈ gtGPUppersTwo c.1 c.2 k, f p c := by
  classical
  simp_rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun z _ => ⟨n - (z.2.1 + z.2.2), ⟨z.2, z.1⟩⟩)
    (fun z _ => ⟨z.2.2, z.2.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hp, hc⟩
    have hp := (mem_gtPartitionsTwo n z.1).mp hp
    have hc := (mem_gtDownRowsTwo z.1.1 z.1.2 z.2).mp hc
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr (by dsimp; omega), Finset.mem_sigma.mpr ⟨?_, ?_⟩⟩
    · rw [mem_gtPartitionsTwo]
      dsimp
      omega
    · rw [mem_gtGPUppersTwo]
      dsimp
      omega
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hk, hc⟩
    rcases Finset.mem_sigma.mp hc with ⟨hc, hp⟩
    have hk := Finset.mem_range.mp hk
    have hc := (mem_gtPartitionsTwo (n - z.1) z.2.1).mp hc
    have hp := (mem_gtGPUppersTwo z.2.1.1 z.2.1.2 z.1 z.2.2).mp hp
    apply Finset.mem_sigma.mpr
    constructor
    · rw [mem_gtPartitionsTwo]
      dsimp
      omega
    · rw [mem_gtDownRowsTwo]
      dsimp
      omega
  · intro z _
    rfl
  · intro z hz
    rcases Finset.mem_sigma.mp hz with ⟨hk, hc⟩
    rcases Finset.mem_sigma.mp hc with ⟨hc, _⟩
    have hk := Finset.mem_range.mp hk
    have hc := (mem_gtPartitionsTwo (n - z.1) z.2.1).mp hc
    have he : n - (z.2.1.1 + z.2.1.2) = z.1 := by omega
    dsimp
    simp only [he]
  · intro z _
    rfl

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.sum_gtRows_three_nat
#print axioms VOA.DeligneAudit.D4Char.sum_gtDownRowsTwo_reverse
