import VOA.DeligneAudit.LeviTypeA2CertStepRank

/-! The binomial count from aggregate key multiplicities. -/

namespace VOA.DeligneAudit.A3Sector

open VOA.DeligneAudit.LeviTypeA

/-- The needed form of (KS) counts all degrees with the same two radical
letter counts together. A separate bound at each degree does not imply it. -/
def A2AggregateKeyMultiplicity (p q n : ℕ)
    (d₁ d₂ r : Fin n → ℕ) : Prop :=
  ∀ a ∈ Finset.range (p + 1), ∀ b ∈ Finset.range (q + 1),
    (∑ i : Fin n, if d₁ i = a ∧ d₂ i = b then r i else 0) ≤
      p.choose a * q.choose b

/-- The all-weight count, conditional on aggregate (KS) and support in the
binomial box. Here `r` is the effective multiplicity: keys with `L i = 0`
may be assigned `r i = 0` even if their raw key quotient is nonzero. -/
theorem a2_count_of_aggregate_multiplicity (p q n : ℕ)
    (d₁ d₂ L r : Fin n → ℕ)
    (hsupport : ∀ i, r i ≠ 0 → d₁ i ≤ p ∧ d₂ i ≤ q)
    (hL : ∀ i, L i ≤ 2 ^ (q + d₁ i - d₂ i))
    (hKS : A2AggregateKeyMultiplicity p q n d₁ d₂ r) :
    (∑ i : Fin n, L i * r i) ≤ a2LeviCount p q := by
  have hpart (i : Fin n) :
      (∑ a ∈ Finset.range (p + 1),
        ∑ b ∈ Finset.range (q + 1),
          if d₁ i = a ∧ d₂ i = b then
            2 ^ (q + d₁ i - d₂ i) * r i else 0) =
        2 ^ (q + d₁ i - d₂ i) * r i := by
    by_cases hr : r i = 0
    · simp [hr]
    · obtain ⟨ha, hb⟩ := hsupport i hr
      calc
        _ = ∑ a ∈ Finset.range (p + 1),
              if d₁ i = a then
                (∑ b ∈ Finset.range (q + 1),
                  if d₂ i = b then 2 ^ (q + d₁ i - d₂ i) * r i else 0)
              else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases heq : d₁ i = a <;> simp [heq]
        _ = _ := by simp [Finset.mem_range, ha, hb]
  calc
    (∑ i : Fin n, L i * r i) ≤
        ∑ i : Fin n, 2 ^ (q + d₁ i - d₂ i) * r i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right _ (hL i)
    _ = ∑ a ∈ Finset.range (p + 1),
          ∑ b ∈ Finset.range (q + 1),
            2 ^ (q + a - b) *
              (∑ i : Fin n, if d₁ i = a ∧ d₂ i = b then r i else 0) := by
      calc
        _ = ∑ i : Fin n, ∑ a ∈ Finset.range (p + 1),
              ∑ b ∈ Finset.range (q + 1),
                if d₁ i = a ∧ d₂ i = b then
                  2 ^ (q + d₁ i - d₂ i) * r i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hpart i).symm
        _ = ∑ a ∈ Finset.range (p + 1),
              ∑ b ∈ Finset.range (q + 1),
                ∑ i : Fin n,
                  if d₁ i = a ∧ d₂ i = b then
                    2 ^ (q + d₁ i - d₂ i) * r i else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs with hab
          · rcases hab with ⟨h₁, h₂⟩
            subst a
            subst b
            rfl
          · simp
    _ ≤ a2LeviCount p q := by
      unfold a2LeviCount
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      have h := hKS a ha b hb
      calc
        2 ^ (q + a - b) *
            (∑ i : Fin n, if d₁ i = a ∧ d₂ i = b then r i else 0) ≤
          2 ^ (q + a - b) * (p.choose a * q.choose b) :=
            Nat.mul_le_mul_left _ h
        _ = p.choose a * q.choose b * 2 ^ (q + a - b) := by ac_rfl

end VOA.DeligneAudit.A3Sector

#print axioms VOA.DeligneAudit.A3Sector.a2_count_of_aggregate_multiplicity
