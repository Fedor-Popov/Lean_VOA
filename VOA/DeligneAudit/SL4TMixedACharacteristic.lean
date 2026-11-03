import VOA.DeligneAudit.SL4TMixedASite
import VOA.DeligneAudit.SL4TMixedStateCharacteristic

/-! # Characteristic-polynomial transport at the nine a-site states -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

open Polynomial

/-- The first factor loses a zero root precisely in the chosen first-node state. -/
theorem mixedAState_first_characteristic (q : MixedParams) (hq : MixedValid q)
    (s : MixedAState) (hs : MixedValid (mixedANext q s)) :
    descendingPoly (fun i => (-1) ^ i *
        mixedStateEvaluation q (mixedAStateIdeal q s) (mixedE 3 i)) q.e1.toNat =
      X ^ (if s.1 = .chosen then 1 else 0) *
        descendingPoly (fun i => (-1) ^ i *
          mixedStateEvaluation q (mixedAStateIdeal q s) (mixedE 3 i))
          (mixedANext q s).e1.toNat := by
  by_cases hl : s.1 = .chosen
  · have he : q.e1.toNat = (mixedANext q s).e1.toNat + 1 := by
      simp only [MixedValid, mixedANext, hl, if_true] at hs ⊢
      omega
    rw [if_pos hl, pow_one]
    apply descendingPoly_remove_zero_root _ _ _ he
    have hb := (mixedAStateEvaluation_boundary q s).1
    simp only [mixedAPair, hl] at hb
    rw [hb, mul_zero]
  · simp [mixedANext, hl]

/-- The complementary second factor loses a zero root only in the complement state. -/
theorem mixedAState_second_characteristic (q : MixedParams) (hq : MixedValid q)
    (s : MixedAState) (hs : MixedValid (mixedANext q s)) :
    descendingPoly (fun i => (-1) ^ i *
        mixedStateEvaluation q (mixedAStateIdeal q s) (mixedG2prime i))
        (mixedQ q - q.e2).toNat =
      X ^ (if s.2 = .complement then 1 else 0) *
        descendingPoly (fun i => (-1) ^ i *
          mixedStateEvaluation q (mixedAStateIdeal q s) (mixedG2prime i))
          (mixedQ (mixedANext q s) - (mixedANext q s).e2).toNat := by
  have hv := hq
  simp only [MixedValid, mixedQ] at hv
  rcases s with ⟨l, r⟩
  cases r with
  | original =>
      have he : mixedQ q - q.e2 = mixedQ (mixedANext q (l, .original)) -
          (mixedANext q (l, .original)).e2 := by simp [mixedQ, mixedANext]; ring
      simp only [Prod.snd, reduceCtorEq, if_false, pow_zero, one_mul]
      rw [he]
  | chosen =>
      have he : mixedQ q - q.e2 = mixedQ (mixedANext q (l, .chosen)) -
          (mixedANext q (l, .chosen)).e2 := by simp [mixedQ, mixedANext]; ring
      simp only [Prod.snd, reduceCtorEq, if_false, pow_zero, one_mul]
      rw [he]
  | complement =>
      have he : (mixedQ q - q.e2).toNat =
          (mixedQ (mixedANext q (l, .complement)) -
            (mixedANext q (l, .complement)).e2).toNat + 1 := by
        simp [MixedValid, mixedQ, mixedANext] at hs ⊢
        omega
      simp only [Prod.snd, if_true, pow_one]
      apply descendingPoly_remove_zero_root _ _ _ he
      have hb := (mixedAStateEvaluation_boundary q (l, .complement)).2
      change mixedStateEvaluation q _ (mixedG2prime (mixedQ q - q.e2).toNat) = 0 at hb
      rw [hb, mul_zero]

/-- Compatibility of every a-state surjection with its characteristic polynomial. -/
theorem mixedAStateSurjection_characteristic (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (s : MixedAState)
    (hs : MixedValid (mixedANext q s)) :
    (mixedCharacteristic q).map
        (Ideal.Quotient.mkₐ ℂ (mixedAStateIdeal q s)).toRingHom =
      X ^ mixedAZeroRoots s * (mixedCharacteristic (mixedANext q s)).map
        (mixedAStateSurjection q hq hA hB s hs).toRingHom := by
  rw [mixedCharacteristic_state_evaluation]
  simp only [mixedCharacteristic, Polynomial.map_mul, descendingPoly_map, map_mul,
    map_pow, map_neg, map_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    mixedAStateSurjection_evaluation]
  rw [mixedAState_first_characteristic q hq s hs,
    mixedAState_second_characteristic q hq s hs]
  simp only [mixedAZeroRoots, pow_add]
  ring

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedAState_first_characteristic
#print axioms VOA.DeligneAudit.SL4T.mixedAState_second_characteristic
#print axioms VOA.DeligneAudit.SL4T.mixedAStateSurjection_characteristic
