/-
Ravinder's mixed fusion recursion and its Gaussian closed form.
Pure combinatorics, Mathlib only.  The closed form was also checked symbolically (sympy) for
a ≤ 6, b ≤ 5 (outside Lean).
-/
import Mathlib

namespace VOA.DeligneGaussian

variable {R : Type*} [CommRing R] (q : R)

/-- Gaussian binomial coefficients, defined by the q-Pascal rule
`[n+1,k+1] = q^(n-k) [n,k] + [n,k+1]` (this rule characterizes the usual `[n,k]_q`). -/
def qbinom : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => q ^ (n - k) * qbinom n k + qbinom n (k + 1)

@[simp] theorem qbinom_zero_right (n : ℕ) : qbinom q n 0 = 1 := by
  cases n <;> rfl

theorem qbinom_succ_succ (n k : ℕ) :
    qbinom q (n + 1) (k + 1) = q ^ (n - k) * qbinom q n k + qbinom q n (k + 1) := rfl

theorem qbinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → qbinom q n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      rw [qbinom_succ_succ, qbinom_eq_zero_of_lt (by omega),
        qbinom_eq_zero_of_lt (n := n) (k := k + 1) (by omega)]
      ring

/-- Ravinder's mixed fusion recursion, with `f b = M 0 b`. -/
def mixed (f : ℕ → R) : ℕ → ℕ → R
  | 0, b => f b
  | a + 1, b => mixed f a (b + 1) + q ^ (2 * a + b + 1) * mixed f a b

/-- Closed form of the mixed recursion. -/
theorem mixed_eq (f : ℕ → R) : ∀ a b : ℕ,
    mixed q f a b =
      ∑ d ∈ Finset.range (a + 1), q ^ (d * (a + b)) * qbinom q a d * f (a + b - d)
  | 0, b => by simp [mixed]
  | a + 1, b => by
      rw [mixed, mixed_eq f a (b + 1), mixed_eq f a b]
      set h : ℕ → R := fun d => q ^ (d * (a + (b + 1))) * qbinom q a d * f (a + (b + 1) - d)
        with hh
      set k : ℕ → R := fun d => q ^ (d * (a + b)) * qbinom q a d * f (a + b - d) with hk
      set g : ℕ → R := fun d => q ^ (d * (a + 1 + b)) * qbinom q (a + 1) d * f (a + 1 + b - d)
        with hg
      have hC : ∑ d ∈ Finset.range (a + 1 + 1), g d =
          (∑ d ∈ Finset.range a, g (d + 1) + g (a + 1)) + g 0 := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have hA : ∑ d ∈ Finset.range (a + 1), h d = ∑ d ∈ Finset.range a, h (d + 1) + h 0 :=
        Finset.sum_range_succ' _ _
      have hB : ∑ d ∈ Finset.range (a + 1), k d = ∑ d ∈ Finset.range a, k d + k a :=
        Finset.sum_range_succ _ _
      have hterm : ∀ d, d ≤ a → g (d + 1) = h (d + 1) + q ^ (2 * a + b + 1) * k d := by
        intro d hd
        simp only [hg, hh, hk]
        rw [qbinom_succ_succ q a d]
        have e1 : a + 1 + b - (d + 1) = a + b - d := by omega
        have e2 : a + (b + 1) - (d + 1) = a + b - d := by omega
        have e3 : (d + 1) * (a + (b + 1)) = (d + 1) * (a + 1 + b) := by ring
        have e4 : (d + 1) * (a + 1 + b) + (a - d) = 2 * a + b + 1 + d * (a + b) := by
          obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hd
          rw [Nat.add_sub_cancel_left]
          ring
        rw [e1, e2, e3]
        have e5 : q ^ ((d + 1) * (a + 1 + b)) * q ^ (a - d) =
            q ^ (2 * a + b + 1) * q ^ (d * (a + b)) := by
          rw [← pow_add, ← pow_add, e4]
        linear_combination (qbinom q a d * f (a + b - d)) * e5
      have h0 : g 0 = h 0 := by
        simp only [hg, hh, qbinom_zero_right, zero_mul, pow_zero, one_mul, Nat.sub_zero]
        rw [show a + 1 + b = a + (b + 1) by omega]
      have hlast : h (a + 1) = 0 := by
        simp only [hh, qbinom_eq_zero_of_lt q (Nat.lt_succ_self a), mul_zero, zero_mul]
      have hsum : ∑ d ∈ Finset.range a, g (d + 1) =
          ∑ d ∈ Finset.range a, (h (d + 1) + q ^ (2 * a + b + 1) * k d) :=
        Finset.sum_congr rfl fun d hd => hterm d (by have := Finset.mem_range.mp hd; omega)
      rw [hC, hA, hB, hsum, Finset.sum_add_distrib, ← Finset.mul_sum, hterm a le_rfl, hlast, h0]
      ring

/-- The Gaussian transform used in the manuscript: `d_n = ∑_d q^(nd) [n,d] f_(n-d)`. -/
theorem demazure_eq_gaussian (f : ℕ → R) (n : ℕ) :
    mixed q f n 0 =
      ∑ d ∈ Finset.range (n + 1), q ^ (n * d) * qbinom q n d * f (n - d) := by
  rw [mixed_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [mul_comm d n]

end VOA.DeligneGaussian

section AxiomAudit
#print axioms VOA.DeligneGaussian.mixed_eq
#print axioms VOA.DeligneGaussian.demazure_eq_gaussian
end AxiomAudit
