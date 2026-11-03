import VOA.DeligneAudit.SL4TMixedFlagMap

/-! # Transport of smaller flags through mixed-site state quotients -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

theorem mixedTruncationIdeal_characteristic (q : MixedParams) :
    mixedCharacteristic q ∈ mixedTruncationIdeal q :=
  (show Ideal.span {mixedCharacteristic q} ≤ _ from le_sup_left)
    (Ideal.subset_span rfl)

theorem mixedTruncationIdeal_power (q : MixedParams) :
    (X : (MixedRing q)[X]) ^ (q.A + q.B).toNat ∈ mixedTruncationIdeal q :=
  (show Ideal.span {(X : (MixedRing q)[X]) ^ (q.A + q.B).toNat} ≤ _ from le_sup_right)
    (Ideal.subset_span rfl)

/-- Each valid b-state transports its smaller flag with its zero-root shift. -/
theorem mixedBState_flag (q : MixedParams) (hq : MixedValid q) (hB : 1 ≤ q.B)
    (i : Fin 4) (hs : MixedValid (mixedBNext q (mixedBOrder i))) {ns : List ℕ}
    (h : SpanningChain (mixedTruncationIdeal (mixedBNext q (mixedBOrder i))) ⊥ ⊤ ns) :
    SpanningChain (mixedTruncationIdeal q) (mixedBChain q i.val)
      (mixedBChain q (i.val + 1))
      (ns.map (fun n => n + mixedBZeroRoots (mixedBOrder i))) := by
  let s := mixedBOrder i
  let ψ := mixedBStateSurjection q hq hB s hs
  have hψ := mixedBStateSurjection_surjective q hq hB s hs
  have hk := mixedBThom_stateIdeal q hq hB i
  have hp := mixedBStateSurjection_characteristic q hq hB s hs
  have hm : ((mixedBNext q s).A + (mixedBNext q s).B).toNat =
      (q.A + q.B - 1).toNat := by rw [mixedBNext_sites]
  have hpos : 1 ≤ q.A + q.B := by have := hq.1; omega
  have hexp : ((mixedBNext q s).A + (mixedBNext q s).B).toNat + 1 =
      (q.A + q.B).toNat := by rw [hm]; omega
  rw [mixedBChain_step]
  change SpanningChain _ _ _ (ns.map (fun n => n + mixedBZeroRoots s))
  by_cases hz : mixedBZeroRoots s = 0
  · have ht : Polynomial.C (mixedBThom q s) *
        X ^ ((mixedBNext q s).A + (mixedBNext q s).B).toNat ∈
        (mixedBChain q i.val).map Polynomial.C ⊔ mixedTruncationIdeal q := by
      rw [hm]
      fin_cases i <;> simp [s, mixedBOrder, mixedBZeroRoots] at hz
      · exact (show mixedTruncationIdeal q ≤ _ from le_sup_right)
          (mixedBThom_first_truncation q hq hB)
      · simpa only [sup_comm] using mixedBThom_second_truncation q hq hB
    simp only [hz, pow_zero, one_mul] at hp
    simp only [hz, Nat.add_zero, List.map_id']
    exact
      SpanningChain.of_state_without_root (mixedBStateIdeal q s) ψ hψ
        (mixedBThom q s) (mixedBChain q i.val) (mixedTruncationIdeal q)
        (mixedCharacteristic (mixedBNext q s)) (mixedCharacteristic q)
        ((mixedBNext q s).A + (mixedBNext q s).B).toNat hk hp
        (mixedTruncationIdeal_characteristic q) ht h
  · have hz' : mixedBZeroRoots s = 1 := by
      have hb : ∀ z, mixedBZeroRoots z = 0 ∨ mixedBZeroRoots z = 1 := by
        intro z
        cases z <;> simp [mixedBZeroRoots]
      exact (hb s).resolve_left hz
    simp only [hz', pow_one] at hp
    rw [hz']
    exact SpanningChain.of_state_with_root (mixedBStateIdeal q s) ψ hψ
      (mixedBThom q s) (mixedBChain q i.val) (mixedTruncationIdeal q)
      (mixedCharacteristic (mixedBNext q s)) (mixedCharacteristic q)
      ((mixedBNext q s).A + (mixedBNext q s).B).toNat hk hp
      (mixedTruncationIdeal_characteristic q)
      (by rw [hexp]; exact mixedTruncationIdeal_power q) h

/-- The polynomial lift for the double-root a-state divides each characteristic factor once. -/
theorem mixedAState_doubleRoot_lift (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0)
    (hs : MixedValid (mixedANext q (.chosen, .complement))) :
    ((mixedFirstPolynomial q).divX * (mixedSecondPolynomial q).divX).map
        (Ideal.Quotient.mkₐ ℂ (mixedAStateIdeal q (.chosen, .complement))).toRingHom =
      (mixedCharacteristic (mixedANext q (.chosen, .complement))).map
        (mixedAStateSurjection q hq hA hB (.chosen, .complement) hs).toRingHom := by
  let s : MixedAState := (.chosen, .complement)
  let ρ := Ideal.Quotient.mkₐ ℂ (mixedAStateIdeal q s)
  let ψ := mixedAStateSurjection q hq hA hB s hs
  have hfirst : (mixedFirstPolynomial q).map ρ.toRingHom =
      X * (mixedFirstPolynomial (mixedANext q s)).map ψ.toRingHom := by
    simp only [mixedFirstPolynomial, descendingPoly_map, map_mul, map_pow, map_neg,
      map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    simp only [ψ, mixedAStateSurjection_evaluation]
    simpa only [s, Prod.fst, if_true, pow_one] using
      mixedAState_first_characteristic q hq s hs
  have hsecond : (mixedSecondPolynomial q).map ρ.toRingHom =
      X * (mixedSecondPolynomial (mixedANext q s)).map ψ.toRingHom := by
    simp only [mixedSecondPolynomial, descendingPoly_map, map_mul, map_pow, map_neg,
      map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    simp only [ψ, mixedAStateSurjection_evaluation]
    simpa only [s, Prod.snd, if_true, pow_one] using
      mixedAState_second_characteristic q hq s hs
  rw [Polynomial.map_mul, mixedCharacteristic_factors, Polynomial.map_mul]
  exact congrArg₂ (· * ·) (polynomial_map_divX_of_zero_root ρ _ _ hfirst)
    (polynomial_map_divX_of_zero_root ρ _ _ hsecond)

/-- A state with any removed roots increases its cell level by one. -/
def mixedALevelShift (s : MixedAState) : ℕ := min 1 (mixedAZeroRoots s)

/-- Removing an a-site decreases the total number of sites by one. -/
theorem mixedANext_sites (q : MixedParams) (s : MixedAState) :
    (mixedANext q s).A + (mixedANext q s).B = q.A + q.B - 1 := by
  simp [mixedANext]
  ring

/-- Each valid a-state transports its smaller flag, including the double-root state. -/
theorem mixedAState_flag (q : MixedParams) (hq : MixedValid q) (hA : 1 ≤ q.A)
    (hB : q.B = 0) (i : Fin 9) (hs : MixedValid (mixedANext q (mixedAOrder i)))
    {ns : List ℕ}
    (h : SpanningChain (mixedTruncationIdeal (mixedANext q (mixedAOrder i))) ⊥ ⊤ ns) :
    SpanningChain (mixedTruncationIdeal q) (mixedAChain q i.val)
      (mixedAChain q (i.val + 1))
      (ns.map (fun n => n + mixedALevelShift (mixedAOrder i))) := by
  let s := mixedAOrder i
  let ψ := mixedAStateSurjection q hq hA hB s hs
  have hψ := mixedAStateSurjection_surjective q hq hA hB s hs
  have hk := mixedAThom_stateIdeal q hq hA hB i
  have hp := mixedAStateSurjection_characteristic q hq hA hB s hs
  have hm : ((mixedANext q s).A + (mixedANext q s).B).toNat = (q.A - 1).toNat := by
    rw [mixedANext_sites, hB, add_zero]
  have hexp : ((mixedANext q s).A + (mixedANext q s).B).toNat + 1 =
      (q.A + q.B).toNat := by rw [hm, hB, add_zero]; omega
  rw [mixedAChain_step]
  change SpanningChain _ _ _ (ns.map (fun n => n + mixedALevelShift s))
  by_cases hi : i.val < 4
  · have hz : mixedAZeroRoots s = 0 := by
      fin_cases i <;> simp_all [s, mixedAOrder, mixedAZeroRoots]
    have ht := mixedAThom_noRoot_truncation q hA hB ⟨i.val, hi⟩
    have ht' : Polynomial.C (mixedAThom q s) *
        X ^ ((mixedANext q s).A + (mixedANext q s).B).toNat ∈
        (mixedAChain q i.val).map Polynomial.C ⊔ mixedTruncationIdeal q := by
      rw [hm]
      exact (show mixedTruncationIdeal q ≤ _ from le_sup_right) ht
    simp only [hz, pow_zero, one_mul] at hp
    have hz' : mixedALevelShift s = 0 := by simp [mixedALevelShift, hz]
    simp only [hz', Nat.add_zero, List.map_id']
    exact
      SpanningChain.of_state_without_root (mixedAStateIdeal q s) ψ hψ
        (mixedAThom q s) (mixedAChain q i.val) (mixedTruncationIdeal q)
        (mixedCharacteristic (mixedANext q s)) (mixedCharacteristic q)
        ((mixedANext q s).A + (mixedANext q s).B).toNat hk hp
        (mixedTruncationIdeal_characteristic q) ht' h
  · by_cases hi' : i.val = 6
    · have he : i = (6 : Fin 9) := Fin.ext hi'
      subst i
      have hz' : mixedALevelShift s = 1 := by rfl
      rw [hz']
      apply SpanningChain.of_surjective_state (mixedAStateIdeal q s) ψ hψ
        (mixedAThom q s) (mixedAChain q 6) (mixedTruncationIdeal q)
        (mixedCharacteristic (mixedANext q s))
        ((mixedFirstPolynomial q).divX * (mixedSecondPolynomial q).divX)
        ((mixedANext q s).A + (mixedANext q s).B).toNat 1 hk
        (mixedAState_doubleRoot_lift q hq hA hB hs) _ _ h
      · simpa only [pow_one, mul_assoc, sup_comm] using
          mixedAThom_doubleRoot_truncation q hq hA hB
      · rw [hexp]
        exact (show mixedTruncationIdeal q ≤ _ from le_sup_right)
          ((mixedTruncationIdeal q).mul_mem_left _ (mixedTruncationIdeal_power q))
    · have hz : mixedAZeroRoots s = 1 := by
        fin_cases i <;> simp_all [s, mixedAOrder, mixedAZeroRoots]
      have hz' : mixedALevelShift s = 1 := by simp [mixedALevelShift, hz]
      simp only [hz, pow_one] at hp
      rw [hz']
      exact SpanningChain.of_state_with_root (mixedAStateIdeal q s) ψ hψ
        (mixedAThom q s) (mixedAChain q i.val) (mixedTruncationIdeal q)
        (mixedCharacteristic (mixedANext q s)) (mixedCharacteristic q)
        ((mixedANext q s).A + (mixedANext q s).B).toNat hk hp
        (mixedTruncationIdeal_characteristic q)
        (by rw [hexp]; exact mixedTruncationIdeal_power q) h

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedTruncationIdeal_characteristic
#print axioms VOA.DeligneAudit.SL4T.mixedTruncationIdeal_power
#print axioms VOA.DeligneAudit.SL4T.mixedBState_flag
#print axioms VOA.DeligneAudit.SL4T.mixedAState_doubleRoot_lift
#print axioms VOA.DeligneAudit.SL4T.mixedANext_sites
#print axioms VOA.DeligneAudit.SL4T.mixedAState_flag
