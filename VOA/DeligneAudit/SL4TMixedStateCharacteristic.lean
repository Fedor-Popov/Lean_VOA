import VOA.DeligneAudit.SL4TMixedStateQuotient

/-! # Characteristic-polynomial transport for mixed b-site quotients -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The characteristic polynomial of the union of the first and complementary alphabets. -/
def mixedCharacteristic (q : MixedParams) : (MixedRing q)[X] :=
  descendingPoly (fun i => (-1) ^ i * mixedEvaluation q (mixedE 3 i)) q.e1.toNat *
    descendingPoly (fun i => (-1) ^ i * mixedEvaluation q (mixedG2prime i))
      (mixedQ q - q.e2).toNat

/-- Removing a zero root multiplies the reduced characteristic polynomial by `X`. -/
theorem descendingPoly_remove_zero_root {R : Type*} [CommRing R]
    (f : ℕ → R) (d e : ℕ) (hde : d = e + 1) (hf : f d = 0) :
    descendingPoly f d = X * descendingPoly f e := by
  subst d
  rw [descendingPoly_step, hf, map_zero, add_zero]

/-- The characteristic polynomial is evaluated by the same coefficient functions. -/
theorem mixedCharacteristic_state_evaluation (q : MixedParams) (K : Ideal (MixedRing q)) :
    (mixedCharacteristic q).map (Ideal.Quotient.mkₐ ℂ K).toRingHom =
      descendingPoly (fun i => (-1) ^ i * mixedStateEvaluation q K (mixedE 3 i))
        q.e1.toNat *
      descendingPoly (fun i => (-1) ^ i * mixedStateEvaluation q K (mixedG2prime i))
        (mixedQ q - q.e2).toNat := by
  simp only [mixedCharacteristic, Polynomial.map_mul, descendingPoly_map, map_mul,
    map_pow, map_neg, map_one]
  rfl

/-- The reduced b-state polynomial uses exactly the same images of every coefficient. -/
theorem mixedBStateSurjection_characteristic_evaluation (q : MixedParams)
    (hq : MixedValid q) (hB : 1 ≤ q.B) (s : MixedBState)
    (hs : MixedValid (mixedBNext q s)) :
    (mixedCharacteristic (mixedBNext q s)).map
        (mixedBStateSurjection q hq hB s hs).toRingHom =
      descendingPoly (fun i => (-1) ^ i *
        mixedStateEvaluation q (mixedBStateIdeal q s) (mixedE 3 i))
        (mixedBNext q s).e1.toNat *
      descendingPoly (fun i => (-1) ^ i *
        mixedStateEvaluation q (mixedBStateIdeal q s) (mixedG2prime i))
        (mixedQ (mixedBNext q s) - (mixedBNext q s).e2).toNat := by
  simp only [mixedCharacteristic, Polynomial.map_mul, descendingPoly_map, map_mul,
    map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    mixedBStateSurjection_evaluation]

/-- Compatibility with the number of zero roots in all four b-site states. -/
theorem mixedBStateSurjection_characteristic (q : MixedParams) (hq : MixedValid q)
    (hB : 1 ≤ q.B) (s : MixedBState) (hs : MixedValid (mixedBNext q s)) :
    (mixedCharacteristic q).map
        (Ideal.Quotient.mkₐ ℂ (mixedBStateIdeal q s)).toRingHom =
      X ^ mixedBZeroRoots s * (mixedCharacteristic (mixedBNext q s)).map
        (mixedBStateSurjection q hq hB s hs).toRingHom := by
  rw [mixedCharacteristic_state_evaluation,
    mixedBStateSurjection_characteristic_evaluation]
  have hb := mixedBStateEvaluation_boundary q s
  have hv := hq
  have hn := hs
  simp only [MixedValid, mixedP, mixedQ] at hv
  cases s with
  | s1 => simp [mixedBNext, mixedBZeroRoots, mixedQ]
  | d1 =>
      simp only [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      have he : q.e1.toNat = (q.e1 - 1).toNat + 1 := by omega
      have hz := hb.2
      change mixedStateEvaluation q (mixedBStateIdeal q .d1) (mixedE 3 q.e1.toNat) = 0
        at hz
      simp only [mixedBNext, mixedBZeroRoots, pow_one, mixedQ]
      rw [descendingPoly_remove_zero_root _ _ _ he (by rw [hz, mul_zero])]
      exact mul_assoc _ _ _
  | s2 =>
      have he : mixedQ q - q.e2 = mixedQ (mixedBNext q .s2) -
          (mixedBNext q .s2).e2 := by simp [mixedQ, mixedBNext]; ring
      simp only [mixedBNext, mixedBZeroRoots, pow_zero, one_mul] at he ⊢
      rw [he]
  | d2 =>
      simp only [MixedValid, mixedBNext, mixedP, mixedQ] at hn
      have he : (mixedQ q - q.e2).toNat =
          (mixedQ (mixedBNext q .d2) - (mixedBNext q .d2).e2).toNat + 1 := by
        simp only [mixedQ, mixedBNext] at *
        omega
      have hz := hb.2
      change mixedStateEvaluation q (mixedBStateIdeal q .d2)
        (mixedG2prime (mixedQ q - q.e2).toNat) = 0 at hz
      simp only [mixedBZeroRoots, pow_one]
      rw [descendingPoly_remove_zero_root _ _ _ he (by rw [hz, mul_zero])]
      simp only [mixedBNext]
      ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.descendingPoly_remove_zero_root
#print axioms VOA.DeligneAudit.SL4T.mixedCharacteristic_state_evaluation
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_characteristic_evaluation
#print axioms VOA.DeligneAudit.SL4T.mixedBStateSurjection_characteristic
