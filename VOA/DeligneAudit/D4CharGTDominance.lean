import VOA.DeligneAudit.D4CharGTMonomials

/-! Dominance triangularity of every GT monomial, with integer highest weights. -/

namespace VOA.DeligneAudit.D4Char

open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R]

theorem gtPrefix_restrict (N : ℕ) (lam : Fin (N + 1) → ℤ) (k : ℕ) (hk : k ≤ N) :
    gtPrefix (gtExponent (fun i : Fin N => lam i.castSucc)) k =
      gtPrefix (gtExponent lam) k := by
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  exact (gtExponent_apply _ ⟨i, hiN⟩).trans
    (gtExponent_apply lam ⟨i, by omega⟩).symm

/-- Interlacing bounds every partial sum of the shorter row. -/
theorem gtRows_prefix_le {N : ℕ} {lam : Fin (N + 1) → ℤ} {μ : Fin N → ℤ}
    (hμ : μ ∈ gtRows lam) (k : ℕ) (hk : k ≤ N) :
    gtPrefix (gtExponent μ) k ≤ gtPrefix (gtExponent lam) k := by
  apply Finset.sum_le_sum
  intro i hi
  have hiN : i < N := lt_of_lt_of_le (Finset.mem_range.mp hi) hk
  rw [gtExponent_apply μ ⟨i, hiN⟩, gtExponent_apply lam ⟨i, by omega⟩]
  exact ((mem_gtRows lam μ).mp hμ ⟨i, hiN⟩).2

/-- Every nonzero coefficient has the correct total weight and is dominated by the top row. -/
theorem gtPoly_support_bounds (q : R) (N : ℕ) (lam : Fin N → ℤ) (a : ℕ →₀ ℤ)
    (ha : gtPoly q N lam a ≠ 0) :
    (∀ i, N ≤ i → a i = 0) ∧ gtPrefix a N = ∑ i, lam i ∧
      ∀ k, k ≤ N → gtPrefix a k ≤ gtPrefix (gtExponent lam) k := by
  classical
  induction N generalizing a with
  | zero =>
      have ha0 : a = 0 := by
        by_contra h
        exact ha (by simp [gtPoly, AddMonoidAlgebra.one_def,
          Ne.symm h])
      subst a
      refine ⟨fun _ _ => rfl, by simp, ?_⟩
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
  | succ N ih =>
      rw [gtPoly_coeff_succ] at ha
      obtain ⟨μ, hμ, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      let d : ℤ := (∑ i, lam i) - ∑ i, μ i
      let b : ℕ →₀ ℤ := -Finsupp.single N d + a
      have hb : gtPoly q N μ b ≠ 0 := fun h => hterm (by rw [h, mul_zero])
      obtain ⟨hout, htotal, hdom⟩ := ih μ b hb
      have hab : a = b + Finsupp.single N d := by simp [b, add_comm]
      have htotal' : gtPrefix a (N + 1) = ∑ i, lam i := by
        rw [hab, gtPrefix_add, gtPrefix_succ b, hout N le_rfl, htotal]
        rw [gtPrefix_succ, gtPrefix_single_of_le N N d le_rfl]
        simp [d]
      refine ⟨?_, htotal', ?_⟩
      · intro i hi
        rw [hab, Finsupp.add_apply, hout i (by omega), Finsupp.single_eq_of_ne (by omega)]
        simp
      · intro k hk
        rcases eq_or_lt_of_le hk with rfl | hk
        · rw [htotal', gtPrefix_exponent]
        · have hkN : k ≤ N := by omega
          rw [hab, gtPrefix_add, gtPrefix_single_of_le N k d hkN, add_zero]
          exact (hdom k hkN).trans (gtRows_prefix_le hμ k hkN)

/-- Lemma 3.2(a), dominance half, for the original integral GT polynomials. -/
theorem gtP_support_bounds (N : ℕ) (lam : Fin N → ℤ) (a : ℕ →₀ ℤ)
    (ha : gtP N lam a ≠ 0) :
    (∀ i, N ≤ i → a i = 0) ∧ gtPrefix a N = ∑ i, lam i ∧
      ∀ k, k ≤ N → gtPrefix a k ≤ gtPrefix (gtExponent lam) k := by
  apply gtPoly_support_bounds (Polynomial.X : Polynomial ℤ) N lam a
  rwa [gtPoly_X_eq_gtP]

end

end VOA.DeligneAudit.D4Char

#print axioms VOA.DeligneAudit.D4Char.gtRows_prefix_le
#print axioms VOA.DeligneAudit.D4Char.gtPoly_support_bounds
#print axioms VOA.DeligneAudit.D4Char.gtP_support_bounds
