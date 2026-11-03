import VOA.Classification.COne.QExpThetaDivisors

/-! # Reindexing a residue Lambert sum as one Euler-product Lambert sum -/

open Complex Nat

noncomputable section
namespace VOA.Classification.COne.SSHecke

/-- The least positive representative parametrizes the whole positive residue class. -/
theorem theta_positive_residue_progression {N a t : ℕ}
    (_hN : 0 < N) (ha : 0 < a) (haN : a ≤ N) (ht : 0 < t)
    (hmod : t % N = a % N) : ∃ n : ℕ, N * n + a = t := by
  have hdiv := Nat.mod_add_div t N
  by_cases he : a = N
  · subst a
    have hm : t % N = 0 := by simpa using hmod
    have hd : N * (t / N) = t := by omega
    have hq : 0 < t / N := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, mul_zero] at hd
      omega
    refine ⟨t / N - 1, ?_⟩
    rw [Nat.mul_sub_left_distrib, mul_one, Nat.sub_add_cancel (by nlinarith)]
    exact hd
  · have haN' : a < N := by omega
    rw [Nat.mod_eq_of_lt haN'] at hmod
    exact ⟨t / N, by omega⟩

/-- Exact progression-to-product identity, without any rearrangement assumptions. -/
theorem thetaResidueLambert_eq_thetaLambert {N a : ℕ}
    (hN : 0 < N) (ha : 0 < a) (haN : a ≤ N) (u q : ℂ) :
    thetaResidueLambert N (a % N) u q = thetaLambert (q ^ N) (u * q ^ a) := by
  let e : ℕ → ℕ+ := fun n => ⟨N * n + a, by omega⟩
  have he : Function.Injective e := by
    intro n m h
    have hh : N * n + a = N * m + a := congrArg PNat.val h
    exact Nat.eq_of_mul_eq_mul_left hN (Nat.add_right_cancel hh)
  let f : ℕ+ → ℂ := fun t =>
    if (t : ℕ) % N = a % N then u * q ^ (t : ℕ) / (1 - u * q ^ (t : ℕ)) else 0
  have hsupp : Function.support f ⊆ Set.range e := by
    intro t ht
    have hm : (t : ℕ) % N = a % N := by
      by_contra hn
      exact ht (if_neg hn)
    obtain ⟨n, hn⟩ := theta_positive_residue_progression hN ha haN t.pos hm
    exact ⟨n, Subtype.ext hn⟩
  have heq := he.tsum_eq hsupp
  change (∑' n : ℕ, f (e n)) = thetaResidueLambert N (a % N) u q at heq
  rw [← heq]
  apply tsum_congr
  intro n
  simp [f, e, pow_add, pow_mul, mul_assoc, mul_comm]

end VOA.Classification.COne.SSHecke
