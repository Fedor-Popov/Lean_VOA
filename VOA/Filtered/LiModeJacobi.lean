import VOA.Filtered.LiGradedModeLeibniz

/-!
# A fixed finite commutator formula for nonnegative vertex modes

The binomial support gives the exact range `0,...,m`, independent of a chosen
locality bound. This form is adapted to Jacobi descent to the Li graded algebra.
-/

namespace VOA
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The nonnegative-mode commutator formula in a fixed natural finite range. -/
theorem smul_nonneg_commutator (W : VertexOperatorAlgebra V)
    (m n : ℕ) (x y z : V) :
    W.smul x (m : ℤ) (W.smul y (n : ℤ) z) -
        W.smul y (n : ℤ) (W.smul x (m : ℤ) z) =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℂ) •
        W.smul (W.smul x (j : ℤ) y) ((m + n - j : ℕ) : ℤ) z := by
  let F : ℤ → V := fun j => cbz (m : ℤ) j •
    W.smul (W.smul x j y) ((m : ℤ) + n - j) z
  have hsupport : Function.support F ⊆ (Finset.Icc 0 (m : ℤ) : Set ℤ) := by
    intro j hj
    by_contra hj'
    simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hj'
    apply hj
    rcases hj' with hneg | hlarge
    · simp only [F, cbz_apply_neg _ hneg, zero_smul]
    · simp only [F, cbz_eq_zero_of_lt (by positivity) hlarge, zero_smul]
  have hcomm := mode_commutator (adjointWeakModule W) x y z (m : ℤ) (n : ℤ)
  change W.smul x (m : ℤ) (W.smul y (n : ℤ) z) -
    W.smul y (n : ℤ) (W.smul x (m : ℤ) z) = ∑ᶠ j, F j at hcomm
  rw [hcomm, finsum_eq_finsetSum_of_support_subset F hsupport]
  apply Finset.sum_bij (fun j _ => j.toNat)
  · intro j hj
    obtain ⟨hj0, hjm⟩ := Finset.mem_Icc.mp hj
    simp only [Finset.mem_range]
    omega
  · intro j hj k hk heq
    have hj0 := (Finset.mem_Icc.mp hj).1
    have hk0 := (Finset.mem_Icc.mp hk).1
    omega
  · intro j hj
    refine ⟨(j : ℤ), ?_, by simp⟩
    simp only [Finset.mem_Icc]
    exact ⟨by positivity, by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))⟩
  · intro j hj
    obtain ⟨hj0, hjm⟩ := Finset.mem_Icc.mp hj
    have hjnat : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj0
    have hjle : j.toNat ≤ m := by omega
    have heq : ((m + n - j.toNat : ℕ) : ℤ) = (m : ℤ) + n - j := by
      rw [Nat.cast_sub (by omega : j.toNat ≤ m + n), Nat.cast_add, hjnat]
    have hc : cbz (m : ℤ) j = (m.choose j.toNat : ℂ) := by
      conv_lhs => rw [← hjnat]
      exact cbz_natCast_eq_choose hjle
    simp only [F, hc, heq, hjnat]

end VOA
