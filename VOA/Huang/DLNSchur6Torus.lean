import VOA.Huang.DLNSchur6Symbols

/-! # Torus-generator vanishing in the complementary congruence class -/

namespace VOA.Huang.DLNSchur

/-- Reduction detects units at a positive prime power. -/
theorem isUnit_iff_reduction_ne_zero {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (x : ZMod (p ^ k)) :
    IsUnit x ↔ ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hk]
  have hr : ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p) x = (x.val : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    exact map_natCast _ _
  rw [hr, ne_eq, ZMod.natCast_eq_zero_iff]

/-- Two nonsquares with sum one exist in the prime field when minus one is
a nonsquare. Both are negatives of nonzero squares. -/
theorem exists_nonsquares_add_one_prime {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) :
    ∃ u v : ZMod p, u + v = 1 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      (¬ ∃ a, a ^ 2 = u) ∧ (¬ ∃ a, a ^ 2 = v) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : ¬ ∃ a : ZMod p, a ^ 2 = -1 := by
    rintro ⟨a, ha⟩
    exact (ZMod.exists_sq_eq_neg_one_iff.mp
      ((isSquare_iff_exists_sq _).mpr ⟨a, ha.symm⟩)) hp4
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have ha : a ≠ 0 := by
    intro h; apply hn; exact ⟨b, by simpa [h] using hab⟩
  have hb : b ≠ 0 := by
    intro h; apply hn; exact ⟨a, by simpa [h] using hab⟩
  have hns : ∀ c : ZMod p, c ≠ 0 → ¬ ∃ d, d ^ 2 = -(c ^ 2) := by
    intro c hc
    rintro ⟨d, hd⟩
    apply hn
    refine ⟨d / c, ?_⟩
    rw [div_pow, hd, neg_div, div_self (pow_ne_zero _ hc)]
  refine ⟨-(a ^ 2), -(b ^ 2), ?_, neg_ne_zero.mpr (pow_ne_zero _ ha),
    neg_ne_zero.mpr (pow_ne_zero _ hb), hns a ha, hns b hb⟩
  linear_combination -hab

/-- The nonsquare additive pair lifts to every positive prime power.
Nonsquareness is detected after reduction; no root-lifting assumption is used. -/
theorem exists_nonsquare_units_add_one_primePower {p k : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 3) (hk : 0 < k) :
    ∃ u v : (ZMod (p ^ k))ˣ, (u : ZMod (p ^ k)) + (v : ZMod (p ^ k)) = 1 ∧
      (¬ ∃ a, a ^ 2 = u) ∧ (¬ ∃ a, a ^ 2 = v) := by
  obtain ⟨a, b, hab, ha, hb, hna, hnb⟩ := exists_nonsquares_add_one_prime hp hp4
  let r := ZMod.castHom (dvd_pow_self p hk.ne') (ZMod p)
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective (dvd_pow_self p hk.ne') a
  change r x = a at hx
  have hy : r (1 - x) = b := by
    rw [map_sub, map_one, hx]
    linear_combination -hab
  have hux : IsUnit x := (isUnit_iff_reduction_ne_zero hp hk x).mpr (by rwa [hx])
  have huy : IsUnit (1 - x) :=
    (isUnit_iff_reduction_ne_zero hp hk (1 - x)).mpr (by rwa [hy])
  refine ⟨hux.unit, huy.unit, ?_, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]; ring
  · rintro ⟨z, hz⟩
    apply hna
    refine ⟨r (z : ZMod (p ^ k)), ?_⟩
    have he := congrArg (fun w : (ZMod (p ^ k))ˣ => r (w : ZMod (p ^ k))) hz
    simpa only [Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec, hx] using he
  · rintro ⟨z, hz⟩
    apply hnb
    refine ⟨r (z : ZMod (p ^ k)), ?_⟩
    have he := congrArg (fun w : (ZMod (p ^ k))ˣ => r (w : ZMod (p ^ k))) hz
    simpa only [Units.val_pow_eq_pow_val, map_pow, IsUnit.unit_spec, hy] using he

/-- Unconditional generator vanishing for the remaining congruence class. -/
theorem torusGeneratorRelations_primePower_mod_four_three {p k : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) (hk : 0 < k) :
    TorusGeneratorRelations (p ^ k) (primePower_coprime_two_three hp hp5).1 := by
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  obtain ⟨u, v, huv, hu, hv⟩ := exists_nonsquare_units_add_one_primePower hp hp4 hk
  intro E _ π hs hc X Y hX hY _ hn w hw
  have he := torusDefect_eq_generator_of_nonsquares
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hc w hw u v hu hv
  exact he.symm.trans (torusDefect_add_eq_one
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hc u v huv)

theorem largePrimeTorusGeneratorRelationsModFourThree :
    LargePrimeTorusGeneratorRelationsModFourThree := by
  intro p k hp hp5 hp4 hk
  exact torusGeneratorRelations_primePower_mod_four_three hp hp5 hp4 hk

theorem largePrimeTorusGeneratorRelations : LargePrimeTorusGeneratorRelations :=
  largePrimeTorusGeneratorRelations_iff_mod_four_three.mpr
    largePrimeTorusGeneratorRelationsModFourThree

/-- All torus defects vanish at every positive prime power away from two and three. -/
theorem torusDefect_eq_one_primePower {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k)
    {E : Type} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod (p ^ k)))
    (hs : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E)
    (X Y : Multiplicative (ZMod (p ^ k)) →* E)
    (hX : ∀ t, π (X t) = upperRoot t.toAdd)
    (hY : ∀ t, π (Y t) = lowerRoot t.toAdd)
    (hgen : X.range ⊔ Y.range = commutator E)
    (hn : RootNormalization (primePower_coprime_two_three hp hp5).1 π X Y)
    (u v : (ZMod (p ^ k))ˣ) : torusDefect X Y u v = 1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp (by omega) k
  obtain ⟨w, hw⟩ := IsCyclic.exists_monoid_generator (α := (ZMod (p ^ k))ˣ)
  have hz := largePrimeTorusGeneratorRelations p k hp hp5 hk E π hs hc X Y hX hY hgen hn w hw
  rcases torusDefect_eq_one_or_generator
    (primePower_coprime_two_three hp hp5).1 (primePower_coprime_two_three hp hp5).2
    π hs X Y hX hY hn hc w hw u v with h | h
  · exact h
  · exact h.trans hz

end VOA.Huang.DLNSchur
