import VOA.DeligneAudit.SL4TFullFlagRing

/-! # Power relations for the filtration by the last full-flag root -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- Isolating the boundary term of a two-root complete relation lowers the cutoff
on one root in every sufficiently high layer of the other root. -/
theorem twoRoot_boundary_power_mem (x z : A) (N k : ℕ) (hN : 0 < N)
    (hx : x ^ N = 0)
    (hc : ∑ a ∈ Finset.range (N + k), x ^ a * z ^ (N + k - 1 - a) = 0) :
    x ^ (N - 1) * z ^ k ∈ Ideal.span {z ^ (k + 1)} := by
  classical
  let I : Ideal A := Ideal.span {z ^ (k + 1)}
  let q := Ideal.Quotient.mk I
  have hz : q z ^ (k + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hqx : q x ^ N = 0 := by rw [← map_pow, hx, map_zero]
  have h := congrArg q hc
  simp only [map_sum, map_mul, map_pow, map_zero] at h
  rw [Finset.sum_eq_single (N - 1)] at h
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (x ^ (N - 1) * z ^ k) = 0
    simpa only [map_mul, map_pow, show N + k - 1 - (N - 1) = k by omega] using h
  · intro a ha hne
    by_cases hax : N ≤ a
    · rw [pow_eq_zero_of_le hax hqx, zero_mul]
    · rw [pow_eq_zero_of_le (show k + 1 ≤ N + k - 1 - a by omega) hz, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

/-- The full-alphabet relation supplies the boundary power relation for any
two distinguished roots and any complementary alphabet. -/
theorem fullFlag_boundary_power_mem (x z : A) (xs : List A) (N k : ℕ)
    (hN : 0 < N) (hlen : xs.length + 2 = N + k)
    (he : D4Levi.ksEPoly ([x, z] ++ xs) = 1) (hx : x ^ N = 0) :
    x ^ (N - 1) * z ^ k ∈ Ideal.span {z ^ (k + 1)} := by
  apply twoRoot_boundary_power_mem x z N k hN hx
  have h := twoRoot_complete_vanish x z xs he (N + k - 1) (by omega)
  simpa only [show N + k - 1 + 1 = N + k by omega] using h

/-- Multiplication transports the cutoff improvement to all later power layers. -/
theorem fullFlag_boundary_power_layer (x z : A) (xs : List A) (N k i : ℕ)
    (hN : 0 < N) (hlen : xs.length + 2 = N + k)
    (he : D4Levi.ksEPoly ([x, z] ++ xs) = 1) (hx : x ^ N = 0) (hi : k ≤ i) :
    x ^ (N - 1) * z ^ i ∈ Ideal.span {z ^ (i + 1)} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (fullFlag_boundary_power_mem x z xs N k hN hlen he hx)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  have hp := congrArg (fun y => y * z ^ (i - k)) ha
  calc
    x ^ (N - 1) * z ^ i = (x ^ (N - 1) * z ^ k) * z ^ (i - k) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hi]
    _ = (z ^ (k + 1) * a) * z ^ (i - k) := hp
    _ = z ^ (i + 1) * a := by
      rw [mul_right_comm, ← pow_add, show k + 1 + (i - k) = i + 1 by omega]

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.twoRoot_boundary_power_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlag_boundary_power_mem
#print axioms VOA.DeligneAudit.SL4T.fullFlag_boundary_power_layer
