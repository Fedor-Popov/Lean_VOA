import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePower

/-! Cleared variable-power product identities for the differential
monomial spanning argument. No inverse of the variable or commutation
hypothesis on the derivations is needed in these identities. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.VariablePower
noncomputable section

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem mixed_deriv_pow_add_two (DA DB : Derivation K A A) (u : A) (k : ℕ) :
    DA (DB (u ^ (k + 2))) =
      ((k + 2 : ℕ) : A) * ((k + 1 : ℕ) : A) * u ^ k * DA u * DB u +
        ((k + 2 : ℕ) : A) * u ^ (k + 1) * DA (DB u) := by
  have hB : DB (u ^ (k + 2)) =
      ((k + 2 : ℕ) : A) * u ^ (k + 1) * DB u := by
    simpa only [Nat.add_assoc] using deriv_pow_succ DB u (k + 1)
  rw [hB]
  simp only [Derivation.leibniz,Derivation.map_natCast,deriv_pow_succ,
    smul_eq_mul,mul_zero,add_zero]
  ring

/-- The cubic product of three first derivatives is a difference of
products whose source powers remain exactly n and n+1. -/
theorem third_product_difference (DA DB DC : Derivation K A A) (u : A)
    (n : ℕ) (hn : 1 ≤ n) :
    DC (u ^ n) * DA (DB (u ^ (n + 1))) -
        DA (DB (u ^ n)) * DC (u ^ (n + 1)) =
      ((n * (n + 1) : ℕ) : A) * u ^ (2 * n - 2) * DA u * DB u * DC u := by
  by_cases h1 : n = 1
  · subst n
    simp only [pow_one,mul_one]
    rw [mixed_deriv_pow_add_two DA DB u 0,deriv_pow_succ DC u 1]
    simp only [pow_zero,pow_one,mul_one]
    ring
  · obtain ⟨k,he⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2,by omega⟩
    subst n
    have hAB : DA (DB (u ^ (k + 3))) =
        ((k + 3 : ℕ) : A) * ((k + 2 : ℕ) : A) * u ^ (k + 1) * DA u * DB u +
          ((k + 3 : ℕ) : A) * u ^ (k + 2) * DA (DB u) := by
      simpa only [Nat.add_assoc] using mixed_deriv_pow_add_two DA DB u (k + 1)
    have hC : DC (u ^ (k + 2)) =
        ((k + 2 : ℕ) : A) * u ^ (k + 1) * DC u := by
      simpa only [Nat.add_assoc] using deriv_pow_succ DC u (k + 1)
    have hC' : DC (u ^ (k + 3)) =
        ((k + 3 : ℕ) : A) * u ^ (k + 2) * DC u := by
      simpa only [Nat.add_assoc] using deriv_pow_succ DC u (k + 2)
    have hpow : u ^ (2 * (k + 2) - 2) = (u ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    simp only [Nat.add_assoc]
    rw [hAB,mixed_deriv_pow_add_two DA DB u k,hC,hC',hpow]
    simp only [pow_succ,pow_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

/-- The second mixed derivative is recovered by a cleared source-power
n/n+1 product identity, without cancelling any power of u. -/
theorem second_product_cleared (DA DB : Derivation K A A) (u : A)
    (n : ℕ) (hn : 1 ≤ n) :
    ((n * (n + 1) : ℕ) : A) * u ^ (2 * n) * DA (DB u) =
      ((n + 1 : ℕ) : A) * (DA (DB (u ^ n)) * u ^ (n + 1)) -
        ((n - 1 : ℕ) : A) * (DA (u ^ n) * DB (u ^ (n + 1))) := by
  by_cases h1 : n = 1
  · subst n
    simp only [pow_one]
    ring
  · obtain ⟨k,he⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2,by omega⟩
    subst n
    have hA : DA (u ^ (k + 2)) =
        ((k + 2 : ℕ) : A) * u ^ (k + 1) * DA u := by
      simpa only [Nat.add_assoc] using deriv_pow_succ DA u (k + 1)
    have hB : DB (u ^ (k + 3)) =
        ((k + 3 : ℕ) : A) * u ^ (k + 2) * DB u := by
      simpa only [Nat.add_assoc] using deriv_pow_succ DB u (k + 2)
    have hpow : u ^ (2 * (k + 2)) = (u ^ (k + 2)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    have hsub : k + 2 - 1 = k + 1 := by omega
    simp only [Nat.add_assoc,hsub]
    rw [mixed_deriv_pow_add_two DA DB u k,hA,hB,hpow]
    simp only [pow_succ,pow_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

/-- A second-derivative/first-derivative source product has exactly the
two universal third-order differential monomials. -/
theorem mixed_first_product_expand (DA DB DC : Derivation K A A) (u : A)
    (n : ℕ) (hn : 1 ≤ n) :
    DA (DB (u ^ n)) * DC (u ^ (n + 1)) =
      ((n * (n + 1) : ℕ) : A) * u ^ (2 * n - 1) * DA (DB u) * DC u +
        ((n - 1 : ℕ) : A) *
          (((n * (n + 1) : ℕ) : A) * u ^ (2 * n - 2) * DA u * DB u * DC u) := by
  by_cases h1 : n = 1
  · subst n
    simp only [pow_one]
    rw [deriv_pow_succ DC u 1]
    ring
  · obtain ⟨k,he⟩ : ∃ k : ℕ, n = k + 2 := ⟨n - 2,by omega⟩
    subst n
    have hC : DC (u ^ (k + 3)) =
        ((k + 3 : ℕ) : A) * u ^ (k + 2) * DC u := by
      simpa only [Nat.add_assoc] using deriv_pow_succ DC u (k + 2)
    have hpow : u ^ (2 * (k + 2) - 1) = u ^ (k + 1) * u ^ (k + 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hpow' : u ^ (2 * (k + 2) - 2) = (u ^ (k + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    have hsub : k + 2 - 1 = k + 1 := by omega
    simp only [Nat.add_assoc,hsub]
    rw [mixed_deriv_pow_add_two DA DB u k,hC,hpow,hpow']
    simp only [pow_succ,pow_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

/-- The mixed second/first derivative monomial is recovered with the
same clearing factor n(n+1), keeping the labelled operator split. -/
theorem third_mixed_product_cleared (DA DB DC : Derivation K A A) (u : A)
    (n : ℕ) (hn : 1 ≤ n) :
    ((n * (n + 1) : ℕ) : A) * u ^ (2 * n - 1) * DA (DB u) * DC u =
      (n : A) * (DA (DB (u ^ n)) * DC (u ^ (n + 1))) -
        ((n - 1 : ℕ) : A) * (DC (u ^ n) * DA (DB (u ^ (n + 1)))) := by
  have hC : DC (u ^ n) * DA (DB (u ^ (n + 1))) =
      ((n * (n + 1) : ℕ) : A) * u ^ (2 * n - 2) * DA u * DB u * DC u +
        DA (DB (u ^ n)) * DC (u ^ (n + 1)) :=
    sub_eq_iff_eq_add.mp (third_product_difference DA DB DC u n hn)
  rw [hC,mixed_first_product_expand DA DB DC u n hn,Nat.cast_sub hn]
  ring

/-- Third mixed derivative of a power, with all small-power boundaries
avoided by writing the exponent as k+3. -/
theorem triple_deriv_pow_add_three (DA DB DC : Derivation K A A) (u : A) (k : ℕ) :
    DA (DB (DC (u ^ (k + 3)))) =
      (((k + 3) * (k + 2) * (k + 1) : ℕ) : A) *
          u ^ k * DA u * DB u * DC u +
        (((k + 3) * (k + 2) : ℕ) : A) * u ^ (k + 1) *
          (DA (DB u) * DC u + DA (DC u) * DB u + DB (DC u) * DA u) +
        ((k + 3 : ℕ) : A) * u ^ (k + 2) * DA (DB (DC u)) := by
  have hBC : DB (DC (u ^ (k + 3))) =
      ((k + 3 : ℕ) : A) * ((k + 2 : ℕ) : A) * u ^ (k + 1) * DB u * DC u +
        ((k + 3 : ℕ) : A) * u ^ (k + 2) * DB (DC u) := by
    simpa only [Nat.add_assoc] using mixed_deriv_pow_add_two DB DC u (k + 1)
  rw [hBC]
  simp only [map_add,Derivation.leibniz,Derivation.map_natCast,deriv_pow_succ,
    smul_eq_mul,mul_zero,add_zero]
  simp only [pow_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  ring

end
#print axioms mixed_deriv_pow_add_two
#print axioms third_product_difference
#print axioms second_product_cleared
#print axioms mixed_first_product_expand
#print axioms third_mixed_product_cleared
#print axioms triple_deriv_pow_add_three
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.VariablePower
