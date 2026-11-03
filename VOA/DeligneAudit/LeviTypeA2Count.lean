import Mathlib.Data.Nat.Choose.Sum

/-! The unrestricted binomial count for the node-one `sl₃` Levi step. -/

namespace VOA.DeligneAudit.LeviTypeA

open Finset

def a2LeviCount (p q : ℕ) : ℕ :=
  ∑ d₁ ∈ range (p + 1), ∑ d₂ ∈ range (q + 1),
    p.choose d₁ * q.choose d₂ * 2 ^ (q + d₁ - d₂)

private theorem sum_choose_two (n : ℕ) :
    (∑ d ∈ range (n + 1), n.choose d * 2 ^ d) = 3 ^ n := by
  simpa [mul_comm] using (add_pow (2 : ℕ) 1 n).symm

private theorem sum_choose_two_rev (n : ℕ) :
    (∑ d ∈ range (n + 1), n.choose d * 2 ^ (n - d)) = 3 ^ n := by
  simpa [mul_comm] using (add_pow (1 : ℕ) 2 n).symm

/-- The full count includes every pair of letter counts; restricting to
dominant Levi keys can only decrease it. -/
theorem a2LeviCount_eq (p q : ℕ) : a2LeviCount p q = 3 ^ p * 3 ^ q := by
  have hterm (d₁ d₂ : ℕ) (hd₂ : d₂ ∈ range (q + 1)) :
      p.choose d₁ * q.choose d₂ * 2 ^ (q + d₁ - d₂) =
        (p.choose d₁ * 2 ^ d₁) * (q.choose d₂ * 2 ^ (q - d₂)) := by
    have hle : d₂ ≤ q := by simpa using hd₂
    have he : q + d₁ - d₂ = d₁ + (q - d₂) := by omega
    rw [he, pow_add]
    ring
  calc
    a2LeviCount p q =
        ∑ d₁ ∈ range (p + 1), ∑ d₂ ∈ range (q + 1),
          (p.choose d₁ * 2 ^ d₁) * (q.choose d₂ * 2 ^ (q - d₂)) := by
      unfold a2LeviCount
      apply sum_congr rfl
      intro d₁ _
      apply sum_congr rfl
      intro d₂ hd₂
      exact hterm d₁ d₂ hd₂
    _ = ∑ d₁ ∈ range (p + 1), (p.choose d₁ * 2 ^ d₁) *
          (∑ d₂ ∈ range (q + 1), q.choose d₂ * 2 ^ (q - d₂)) := by
      apply sum_congr rfl
      intro d₁ _
      rw [Finset.mul_sum]
    _ = (∑ d₁ ∈ range (p + 1), p.choose d₁ * 2 ^ d₁) *
          (∑ d₂ ∈ range (q + 1), q.choose d₂ * 2 ^ (q - d₂)) := by
      rw [Finset.sum_mul]
    _ = 3 ^ p * 3 ^ q := by rw [sum_choose_two, sum_choose_two_rev]

end VOA.DeligneAudit.LeviTypeA

#print axioms VOA.DeligneAudit.LeviTypeA.a2LeviCount_eq
