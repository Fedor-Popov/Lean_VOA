import VOA.DeligneAudit.D4FusionToroidalPresentedTwoLayerQuadraticGarland

/-! Every toroidal letter of u-degree at least two kills the cyclic generator. -/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.UnivG VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.D4FusionContact

noncomputable section

private theorem two_positive_high_v (c : Fin 28)
    (hc : D4sector.raising c ∨ D4sector.cartan c)
    (i s : ℕ) (hi : 2 ≤ i) (hs : s ≤ 1) :
    (ρPTE 2).op c i s (pTE 2) = 0 := by
  have ht : [(c, 2 * i + s)] ∈ (ravFam D4sector 2 0).tails := by
    rcases hc with hc | hc
    · exact Or.inl ⟨c, 2 * i + s, hc, rfl⟩
    · exact Or.inr (Or.inl ⟨c, 2 * i + s, hc, by omega, rfl⟩)
  interval_cases s
  · simpa [symbolLetters, wordOpT] using two_syntax_tail [(c, 2 * i)] ht
  · have hd : (2 * i + 1) / 2 = i := by omega
    simpa [symbolLetters, wordOpT, hd] using
      two_syntax_tail [(c, 2 * i + 1)] ht

private theorem two_negative_next (k : Fin 12) (i s : ℕ) (hs : s ≤ 1)
    (hx : (ρPTE 2).op (negativeIndex k) i s (pTE 2) = 0) :
    (ρPTE 2).op (negativeIndex k) (i + 1) s (pTE 2) = 0 := by
  have hh := two_generator_cartan_one (negativeCartan k)
    (negativeCartan_lt_four k) 0 (by omega)
  have hcomm := (ρPTE 2).comm (negativeCartan k) (negativeIndex k)
    1 i 0 s (pTE 2)
  rw [if_pos (by omega : 0 + s < 2)] at hcomm
  have hsum : (∑ c : Fin 28,
      D4sector.f (negativeCartan k) (negativeIndex k) c •
        (ρPTE 2).op c (i + 1) s (pTE 2)) = 0 := by
    simpa [hh, hx, Nat.add_comm] using hcomm.symm
  have htable : (∑ c : Fin 28,
      D4sector.f (negativeCartan k) (negativeIndex k) c •
        (ρPTE 2).op c (i + 1) s (pTE 2)) =
      (negativeWeight k : ℂ) •
        (ρPTE 2).op (negativeIndex k) (i + 1) s (pTE 2) := by
    change (∑ c : Fin 28, contactF (negativeCartan k) (negativeIndex k) c •
      (ρPTE 2).op c (i + 1) s (pTE 2)) = _
    simp only [negative_cartan_table, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [htable] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left (negativeWeight_ne_zero k)

private theorem two_negative_high_v (k : Fin 12) (i s : ℕ)
    (hi : 2 ≤ i) (hs : s ≤ 1) :
    (ρPTE 2).op (negativeIndex k) i s (pTE 2) = 0 := by
  have hbase : (ρPTE 2).op (negativeIndex k) 2 s (pTE 2) = 0 := by
    by_cases hk : k = 11
    · subst k
      interval_cases s
      · simpa [negativeIndex] using two_theta_two_zero
      · simpa [negativeIndex] using two_theta_two_one_zero
    · have hne : negativeIndex k ≠ D4sector.c₀ := by
        intro he
        have hclosed : ∀ j : Fin 12,
            negativeIndex j = D4sector.c₀ → j = 11 := by decide +kernel
        exact hk (hclosed k he)
      have h1 := two_generator_one_other_all (negativeIndex k) hne s
      exact two_negative_next k 1 s hs h1
  induction i, hi using Nat.le_induction with
  | base => exact hbase
  | succ i hi ih => exact two_negative_next k i s hs ih

theorem two_high_v (c : Fin 28) (i s : ℕ) (hi : 2 ≤ i) :
    (ρPTE 2).op c i s (pTE 2) = 0 := by
  by_cases hs : s ≤ 1
  · by_cases hc : c.val < 4
    · exact two_positive_high_v c (Or.inr (show D4sector.cartan c from hc)) i s hi hs
    by_cases hr : c.val < 16
    · exact two_positive_high_v c
        (Or.inl (show D4sector.raising c from ⟨by omega, hr⟩)) i s hi hs
    · obtain ⟨k, rfl⟩ := negativeIndex_covers c (by omega)
      exact two_negative_high_v k i s hi hs
  · have hs' : 2 ≤ s := by omega
    rw [(ρPTE 2).high_zero c i s hs']
    rfl

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.two_high_v
