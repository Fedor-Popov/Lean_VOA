import VOA.DeligneAudit.SL4TFullFlagPowerLayers

/-! # The factorial upper bound for a truncated full flag -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

theorem fullFlag_empty_rank_le (N : ℕ) : Module.finrank ℂ (FullFlagRing 0 N) ≤ 1 := by
  let e := MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)
  letI : FiniteDimensional ℂ (MvPolynomial (Fin 0) ℂ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := (Ideal.Quotient.mkₐ ℂ (fullFlagTruncationIdeal 0 N)).toLinearMap)
    (Ideal.Quotient.mkₐ_surjective ℂ _)
  rw [e.toLinearEquiv.finrank_eq] at h
  simpa using h

/-- The root-deletion recursion gives the factorial bound with all powers of two cleared. -/
theorem fullFlag_finrank_mul_pow_two_le (B k : ℕ) (hk : 2 * k ≤ B) :
    2 ^ k * Module.finrank ℂ (FullFlagRing B (B - k)) ≤ B.factorial := by
  induction B generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simpa using fullFlag_empty_rank_le 0
  | succ B ih =>
      cases k with
      | zero =>
          have h := fullFlag_finrank_recursion B (B + 1) 0 (by omega) (by omega) (by omega)
          have hsmall := ih 0 (by omega)
          simp only [Nat.sub_zero, pow_zero, one_mul] at hsmall ⊢
          simp only [zero_mul, Nat.sub_zero, zero_add] at h
          exact h.trans (by simpa only [Nat.factorial_succ] using
            Nat.mul_le_mul_left (B + 1) hsmall)
      | succ k =>
          let N := B - k
          have hN : 0 < N := by dsimp [N]; omega
          have hlen : B + 1 = N + (k + 1) := by dsimp [N]; omega
          have hkN : k + 1 ≤ N := by omega
          have hrec := fullFlag_finrank_recursion B N (k + 1) hN hlen hkN
          have hfirst := ih k (by omega)
          have hfirst' : 2 ^ (k + 1) * Module.finrank ℂ (FullFlagRing B N) ≤
              2 * B.factorial := by
            simpa only [pow_succ, N, mul_assoc, mul_left_comm, mul_comm] using
              Nat.mul_le_mul_left 2 hfirst
          have hsecond : (N - (k + 1)) *
              (2 ^ (k + 1) * Module.finrank ℂ (FullFlagRing B (N - 1))) ≤
              (N - (k + 1)) * B.factorial := by
            by_cases hvalid : 2 * (k + 1) ≤ B
            · have h := ih (k + 1) hvalid
              have hn : N - 1 = B - (k + 1) := by dsimp [N]; omega
              rw [hn]
              exact Nat.mul_le_mul_left _ h
            · have hz : N - (k + 1) = 0 := by omega
              simp only [hz, zero_mul, le_refl]
          have hsource : B + 1 - (k + 1) = N := by dsimp [N]; omega
          rw [hsource]
          calc
            _ ≤ 2 ^ (k + 1) * ((k + 1) * Module.finrank ℂ (FullFlagRing B N) +
                (N - (k + 1)) * Module.finrank ℂ (FullFlagRing B (N - 1))) :=
              Nat.mul_le_mul_left _ hrec
            _ = (k + 1) * (2 ^ (k + 1) * Module.finrank ℂ (FullFlagRing B N)) +
                (N - (k + 1)) *
                  (2 ^ (k + 1) * Module.finrank ℂ (FullFlagRing B (N - 1))) := by ring
            _ ≤ (k + 1) * (2 * B.factorial) + (N - (k + 1)) * B.factorial :=
              Nat.add_le_add (Nat.mul_le_mul_left _ hfirst') hsecond
            _ = (B + 1).factorial := by
              rw [Nat.factorial_succ]
              have hn : 2 * (k + 1) + (N - (k + 1)) = B + 1 := by omega
              nlinarith

/-- The truncated full-flag ring has dimension at most the number of paired configurations. -/
theorem fullFlag_finrank_le (B k : ℕ) (hk : 2 * k ≤ B) :
    Module.finrank ℂ (FullFlagRing B (B - k)) ≤ B.factorial / 2 ^ k := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ k)).mpr
  simpa only [mul_comm] using fullFlag_finrank_mul_pow_two_le B k hk

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.fullFlag_empty_rank_le
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_mul_pow_two_le
#print axioms VOA.DeligneAudit.SL4T.fullFlag_finrank_le
