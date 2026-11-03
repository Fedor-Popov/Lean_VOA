import VOA.DeligneAudit.LeviTypeA3GradedKS
import VOA.DeligneAudit.A3SectorCount

/-! Orbit weights and the abstract aggregate three-box count. -/

namespace VOA.DeligneAudit.A3Sector

theorem a3KeyOrbitLength_le_power (b c : ℕ) (k : A3RadicalKey) :
    a3KeyOrbitLength b c k ≤ 3 ^ (b + c + k.d₁ - k.d₃) := by
  by_cases hp : a3KeyLabelInt b c 0 k < 0
  · simp [a3KeyOrbitLength, hp]
  · by_cases hq : a3KeyLabelInt b c 1 k < 0
    · simp [a3KeyOrbitLength, hq]
    · have hp0 : 0 ≤ a3KeyLabelInt b c 0 k := by omega
      have hq0 : 0 ≤ a3KeyLabelInt b c 1 k := by omega
      have hsum : a3KeyLabelInt b c 0 k +
          a3KeyLabelInt b c 1 k =
            (b : ℤ) + c + k.d₁ - k.d₃ := by
        simp [a3KeyLabelInt]
        omega
      have he : (a3KeyLabelInt b c 0 k).toNat +
          (a3KeyLabelInt b c 1 k).toNat = b + c + k.d₁ - k.d₃ := by
        omega
      simp [a3KeyOrbitLength, hp, hq, ← pow_add, he]

/-- Support and aggregate multiplicity imply the unrestricted A₃ Levi count. -/
theorem a3_count_of_aggregate_multiplicity (a b c n : ℕ)
    (d₁ d₂ d₃ L r : Fin n → ℕ)
    (hsupport : ∀ i, r i ≠ 0 → d₁ i ≤ a ∧ d₂ i ≤ b ∧ d₃ i ≤ c)
    (hL : ∀ i, L i ≤ 3 ^ (b + c + d₁ i - d₃ i))
    (hKS : ∀ x ∈ Finset.range (a + 1), ∀ y ∈ Finset.range (b + 1),
      ∀ z ∈ Finset.range (c + 1),
        (∑ i : Fin n,
          if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then r i else 0) ≤
          a.choose x * b.choose y * c.choose z) :
    (∑ i : Fin n, L i * r i) ≤ leviCount a b c := by
  have hpart (i : Fin n) :
      (∑ x ∈ Finset.range (a + 1),
        ∑ y ∈ Finset.range (b + 1),
          ∑ z ∈ Finset.range (c + 1),
            if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then
              3 ^ (b + c + d₁ i - d₃ i) * r i else 0) =
        3 ^ (b + c + d₁ i - d₃ i) * r i := by
    by_cases hr : r i = 0
    · simp [hr]
    · obtain ⟨ha, hb, hc⟩ := hsupport i hr
      classical
      let W := 3 ^ (b + c + d₁ i - d₃ i) * r i
      calc
        _ = ∑ x ∈ Finset.range (a + 1),
              if d₁ i = x then
                (∑ y ∈ Finset.range (b + 1),
                  if d₂ i = y then
                    (∑ z ∈ Finset.range (c + 1),
                      if d₃ i = z then W else 0)
                  else 0)
              else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : d₁ i = x
          · subst x
            simp only [true_and, ite_true]
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : d₂ i = y
            · subst y
              simp [W]
            · simp [hy]
          · simp [hx]
        _ = W := by simp [Finset.mem_range, ha, hb, hc]
        _ = _ := rfl
  calc
    (∑ i : Fin n, L i * r i) ≤
        ∑ i : Fin n, 3 ^ (b + c + d₁ i - d₃ i) * r i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right _ (hL i)
    _ = ∑ x ∈ Finset.range (a + 1),
          ∑ y ∈ Finset.range (b + 1),
            ∑ z ∈ Finset.range (c + 1),
              3 ^ (b + c + x - z) *
                (∑ i : Fin n,
                  if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then r i else 0) := by
      calc
        _ = ∑ i : Fin n, ∑ x ∈ Finset.range (a + 1),
              ∑ y ∈ Finset.range (b + 1),
                ∑ z ∈ Finset.range (c + 1),
                  if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then
                    3 ^ (b + c + d₁ i - d₃ i) * r i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hpart i).symm
        _ = ∑ x ∈ Finset.range (a + 1),
              ∑ y ∈ Finset.range (b + 1),
                ∑ z ∈ Finset.range (c + 1),
                  ∑ i : Fin n,
                    if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then
                      3 ^ (b + c + d₁ i - d₃ i) * r i else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs with hxyz
          · rcases hxyz with ⟨hx, hy, hz⟩
            subst x
            subst y
            subst z
            rfl
          · simp
    _ ≤ leviCount a b c := by
      unfold leviCount
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      apply Finset.sum_le_sum
      intro z hz
      calc
        3 ^ (b + c + x - z) *
            (∑ i : Fin n,
              if d₁ i = x ∧ d₂ i = y ∧ d₃ i = z then r i else 0) ≤
          3 ^ (b + c + x - z) * (a.choose x * b.choose y * c.choose z) :=
            Nat.mul_le_mul_left _ (hKS x hx y hy z hz)
        _ = a.choose x * b.choose y * c.choose z *
              3 ^ (b + c + x - z) := by ac_rfl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a3KeyOrbitLength_le_power
#print axioms VOA.DeligneAudit.A3Sector.a3_count_of_aggregate_multiplicity
