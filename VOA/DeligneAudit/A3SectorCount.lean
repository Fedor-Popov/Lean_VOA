import VOA.DeligneAudit.A3SectorWeights
import Mathlib.Data.Nat.Choose.Sum

/-! The unrestricted all-weight count for the node-1 Levi step in type A₃. -/

namespace VOA.DeligneAudit.A3Sector

open Finset

/-- The unrestricted sum over radical letter counts.  The middle count cancels
from the power of three; the exponents are natural since `d₂ ≤ c`. -/
def leviCount (a b c : ℕ) : ℕ :=
  ∑ d₀ ∈ range (a + 1), ∑ d₁ ∈ range (b + 1), ∑ d₂ ∈ range (c + 1),
    a.choose d₀ * b.choose d₁ * c.choose d₂ * 3 ^ (b + c + d₀ - d₂)

private theorem sum_choose_three (n : ℕ) :
    (∑ d ∈ range (n + 1), n.choose d * 3 ^ d) = 4 ^ n := by
  simpa [mul_comm] using (add_pow (3 : ℕ) 1 n).symm

private theorem sum_choose_three_rev (n : ℕ) :
    (∑ d ∈ range (n + 1), n.choose d * 3 ^ (n - d)) = 4 ^ n := by
  simpa [mul_comm] using (add_pow (1 : ℕ) 3 n).symm

/-- The type-A₃ binomial count, for every fundamental-weight triple. -/
theorem leviCount_eq (a b c : ℕ) : leviCount a b c = 4 ^ a * 6 ^ b * 4 ^ c := by
  have hterm (d₀ d₁ d₂ : ℕ) (hd₂ : d₂ ∈ range (c + 1)) :
      a.choose d₀ * b.choose d₁ * c.choose d₂ * 3 ^ (b + c + d₀ - d₂) =
        (a.choose d₀ * 3 ^ d₀) * b.choose d₁ *
          (c.choose d₂ * 3 ^ (c - d₂)) * 3 ^ b := by
    have hle : d₂ ≤ c := by simpa using hd₂
    have he : b + c + d₀ - d₂ = d₀ + (c - d₂) + b := by omega
    rw [he, pow_add, pow_add]
    ring
  calc
    leviCount a b c =
        ∑ d₀ ∈ range (a + 1), ∑ d₁ ∈ range (b + 1), ∑ d₂ ∈ range (c + 1),
          (a.choose d₀ * 3 ^ d₀) * b.choose d₁ *
            (c.choose d₂ * 3 ^ (c - d₂)) * 3 ^ b := by
      unfold leviCount
      apply sum_congr rfl
      intro d₀ _
      apply sum_congr rfl
      intro d₁ _
      apply sum_congr rfl
      intro d₂ hd₂
      exact hterm d₀ d₁ d₂ hd₂
    _ = (∑ d₂ ∈ range (c + 1), c.choose d₂ * 3 ^ (c - d₂)) *
          (∑ d₁ ∈ range (b + 1), b.choose d₁) *
          (∑ d₀ ∈ range (a + 1), a.choose d₀ * 3 ^ d₀) * 3 ^ b := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply sum_congr rfl
      intro d₀ _
      apply sum_congr rfl
      intro d₁ _
      apply sum_congr rfl
      intro d₂ _
      ring
    _ = 4 ^ a * 6 ^ b * 4 ^ c := by
      rw [sum_choose_three, Nat.sum_range_choose, sum_choose_three_rev]
      rw [show 6 ^ b = 2 ^ b * 3 ^ b by rw [← mul_pow]; norm_num]
      ring

#print axioms leviCount_eq

end VOA.DeligneAudit.A3Sector
