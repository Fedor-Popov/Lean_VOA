import VOA.Huang.DLNSchur4Relations

/-! # Negative-pair symbols and the square root of minus one

The rank-one Weyl relations imply `c(u,-u) = 1` directly. Together with
square-class invariance this kills all symbols when `-1` is a square unit.
-/

namespace VOA.Huang.DLNSchur

section Normalized

variable {n : ℕ} {E : Type*} [Group E]
variable (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n)
variable (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod n))
variable (hs : Function.Surjective π)
variable (X Y : Multiplicative (ZMod n) →* E)
variable (hX : ∀ t, π (X t) = upperRoot t.toAdd)
variable (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
variable (hn : RootNormalization h2 π X Y)

include h3 hs hX hY hn

/-- Conjugation of Weyl words, including the parameter inversion. -/
theorem weylWord_conj_weylWord (u v : (ZMod n)ˣ) :
    weylWord X Y u * weylWord X Y v * (weylWord X Y u)⁻¹ =
      weylWord X Y (u ^ 2 * v⁻¹) := by
  have hx := weylWord_upper_conj h2 h3 π hs X Y hX hY hn u (v : ZMod n)
  have hy := weylWord_lower_conj h2 h3 π hs X Y hX hY hn u
    (-(↑v⁻¹ : ZMod n))
  calc
    _ = (weylWord X Y u * X (Multiplicative.ofAdd (v : ZMod n)) *
          (weylWord X Y u)⁻¹) *
        (weylWord X Y u * Y (Multiplicative.ofAdd (-(↑v⁻¹ : ZMod n))) *
          (weylWord X Y u)⁻¹) *
        (weylWord X Y u * X (Multiplicative.ofAdd (v : ZMod n)) *
          (weylWord X Y u)⁻¹) := by unfold weylWord; group
    _ = _ := by
      rw [hx, hy, weylWord_eq_lower_upper_lower h2 h3 π hs X Y hX hY hn]
      simp [mul_comm]

/-- The negative-pair relation requires no bilinearity assumption. -/
theorem torusDefect_neg_self (u : (ZMod n)ˣ) :
    torusDefect X Y u (-u) = 1 := by
  have hw := weylWord_conj_weylWord h2 h3 π hs X Y hX hY hn u 1
  simp only [inv_one, mul_one] at hw
  have he : u * -u = -(u ^ 2) := by simp [pow_two]
  have ht : torusWord X Y u * torusWord X Y (-u) = torusWord X Y (u * -u) := by
    rw [he, torusWord, torusWord, torusWord, weylWord_neg, weylWord_neg, ← hw]
    group
  rw [torusDefect, ht, mul_inv_cancel]

/-- A square root of minus one kills every diagonal defect. -/
theorem torusDefect_eq_one_of_neg_one_square [IsCyclic (ZMod n)ˣ]
    (hc : π.ker ≤ Subgroup.center E)
    (a : (ZMod n)ˣ) (ha : a ^ 2 = -1) (u v : (ZMod n)ˣ)
    (w : (ZMod n)ˣ) (hw : ∀ t : (ZMod n)ˣ, t ∈ Submonoid.powers w) :
    torusDefect X Y u v = 1 := by
  have he : torusDefect X Y w (-w) = torusDefect X Y w w := by
    have h := torusDefect_mul_squares h2 h3 π hs X Y hX hY hn hc 1 a w w
    simpa [ha] using h
  have hz : torusDefect X Y w w = 1 :=
    he.symm.trans (torusDefect_neg_self h2 h3 π hs X Y hX hY hn w)
  rcases torusDefect_eq_one_or_generator h2 h3 π hs X Y hX hY hn hc w hw u v with h | h
  · exact h
  · exact h.trans hz

end Normalized

/-- In a finite cyclic group of order divisible by four, every involution is a square. -/
theorem exists_square_of_sq_eq_one_of_four_dvd_card {G : Type*} [Group G]
    [Finite G] [IsCyclic G] (h4 : 4 ∣ Nat.card G) (z : G) (hz : z ^ 2 = 1) :
    ∃ a : G, a ^ 2 = z := by
  obtain ⟨w, hw⟩ := IsCyclic.exists_monoid_generator (α := G)
  obtain ⟨i, hi⟩ := hw z
  dsimp only at hi
  have hd : 4 ∣ i * 2 := h4.trans (by
    rw [← orderOf_eq_card_of_forall_mem_powers hw]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hi, hz])
  have he : 2 ∣ i := by omega
  obtain ⟨j, rfl⟩ := he
  exact ⟨w ^ j, by rw [← pow_mul, mul_comm j 2, hi]⟩

/-- A square root of minus one exists at every prime power with `p = 1 mod 4`. -/
theorem exists_unit_sq_eq_neg_one_primePower {p k : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hk : 0 < k) :
    ∃ a : (ZMod (p ^ k))ˣ, a ^ 2 = -1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  apply exists_square_of_sq_eq_one_of_four_dvd_card
  · rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]
    exact dvd_mul_of_dvd_right (by omega : 4 ∣ p - 1) _
  · simp

/-- Unconditional vanishing of all torus defects for `p = 1 mod 4`. -/
theorem torusDefect_eq_one_primePower_mod_four_one {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp4 : p % 4 = 1) (hk : 0 < k)
    {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (hn : RootNormalization (primePower_coprime_two_three hp hp5).1 π X Y)
    (u v : (ZMod (p ^ k))ˣ) : torusDefect X Y u v = 1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  obtain ⟨a, ha⟩ := exists_unit_sq_eq_neg_one_primePower hp hp4 hk
  obtain ⟨w, hw⟩ := IsCyclic.exists_monoid_generator (α := (ZMod (p ^ k))ˣ)
  exact torusDefect_eq_one_of_neg_one_square
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hc a ha u v w hw

/-- The requested generator relation is proved for the `p = 1 mod 4` subfamily. -/
theorem torusGeneratorRelations_primePower_mod_four_one {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp4 : p % 4 = 1) (hk : 0 < k) :
    TorusGeneratorRelations (p ^ k) (primePower_coprime_two_three hp hp5).1 := by
  intro E _ π hs hc X Y hX hY _ hn w _
  exact torusDefect_eq_one_primePower_mod_four_one hp hp5 hp4 hk π hs hc X Y hX hY hn w w

end VOA.Huang.DLNSchur
