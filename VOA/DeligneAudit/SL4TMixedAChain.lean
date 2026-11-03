import VOA.DeligneAudit.SL4TMixedIdealChain
import VOA.DeligneAudit.SL4TMixedASite

/-! # The nine-step a-site Thom chain and its state-ideal conditions -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

/-- The order of the nine a-site choices, with the double-root state in seventh place. -/
def mixedAOrder (i : Fin 9) : MixedAState :=
  ![(.complement, .chosen), (.complement, .original), (.outside, .chosen),
    (.outside, .original), (.complement, .complement), (.outside, .complement),
    (.chosen, .complement), (.chosen, .chosen), (.chosen, .original)] i

/-- The nine a-site Thom elements. -/
def mixedAThom (q : MixedParams) (s : MixedAState) : MixedRing q :=
  let a := mixedEvaluation q (mixedE 3 q.e1.toNat)
  let b := mixedEvaluation q (mixedG2prime (mixedQ q - q.e2).toNat)
  let h := mixedEvaluation q (mixedH 0 (q.A - q.d1).toNat)
  let z := mixedEvaluation q (mixedE 2 q.d3.toNat)
  let b' := mixedEvaluation q (mixedE 4 q.e2.toNat)
  match s with
  | (.complement, .chosen) => a * h * b * z
  | (.complement, .original) => a * h * b
  | (.outside, .chosen) => a * b * z
  | (.outside, .original) => a * b
  | (.complement, .complement) => a * h
  | (.outside, .complement) => a
  | (.chosen, .complement) => b' * z
  | (.chosen, .chosen) => z
  | (.chosen, .original) => 1

/-- The a-site ideals are the prefixes of the ordered Thom generators. -/
def mixedAChain (q : MixedParams) (k : ℕ) : Ideal (MixedRing q) :=
  principalIdealPrefix (fun i => mixedAThom q (mixedAOrder i)) k

theorem mixedAChain_mono (q : MixedParams) : Monotone (mixedAChain q) :=
  principalIdealPrefix_mono _

theorem mixedAChain_zero (q : MixedParams) : mixedAChain q 0 = ⊥ :=
  principalIdealPrefix_zero _

theorem mixedAChain_step (q : MixedParams) (i : Fin 9) :
    mixedAChain q (i.val + 1) =
      mixedAChain q i.val ⊔ Ideal.span {mixedAThom q (mixedAOrder i)} :=
  principalIdealPrefix_step _ i

theorem mixedAChain_top (q : MixedParams) : mixedAChain q 9 = ⊤ :=
  principalIdealPrefix_top_of_unit _ 8 rfl

/-- Each a-state boundary ideal is killed modulo the preceding ideal. -/
theorem mixedAThom_stateIdeal (q : MixedParams) (hq : MixedValid q)
    (hA : 1 ≤ q.A) (hB : q.B = 0) (i : Fin 9) :
    ∀ x ∈ mixedAStateIdeal q (mixedAOrder i),
      mixedAThom q (mixedAOrder i) * x ∈ mixedAChain q i.val := by
  let a := mixedEvaluation q (mixedE 3 q.e1.toNat)
  let a' := mixedEvaluation q (mixedG1prime (mixedP q - q.e1).toNat)
  let b := mixedEvaluation q (mixedG2prime (mixedQ q - q.e2).toNat)
  let b' := mixedEvaluation q (mixedE 4 q.e2.toNat)
  let h := mixedEvaluation q (mixedH 0 (q.A - q.d1).toNat)
  let z := mixedEvaluation q (mixedE 2 q.d3.toNat)
  have hfirst : a * a' * h = 0 := by
    dsimp [a, a', h]
    rw [mixedFirst_top_without_b_sites q hq hB]
    exact mixedBase_corner_product q hq 0 hA
  have hsecond : b * b' * z = 0 := by
    have ht := mixedSecond_top_without_b_sites q hq hB
    have hc := mixedBase_corner_product q hq 2 hA
    change z * mixedEvaluation q (mixedH 2 (q.A - q.d3).toNat) = 0 at hc
    change b' * b = (-1) ^ (q.A - q.d3).toNat *
      mixedEvaluation q (mixedH 2 (q.A - q.d3).toNat) at ht
    linear_combination z * ht + (-1) ^ (q.A - q.d3).toNat * hc
  have hmem (k : ℕ) (j : Fin 9) (hj : j.val < k) :
      mixedAThom q (mixedAOrder j) ∈ mixedAChain q k :=
    mem_principalIdealPrefix _ k j hj
  fin_cases i
  · apply mul_pair_ideal_mem
    · rw [mixedAChain_zero]
      change a * h * b * z * a' = 0
      linear_combination b * z * hfirst
    · rw [mixedAChain_zero]
      change a * h * b * z * b' = 0
      linear_combination a * h * hsecond
  · apply mul_pair_ideal_mem
    · change a * h * b * a' ∈ mixedAChain q 1
      have hz : a * h * b * a' = 0 := by linear_combination b * hfirst
      rw [hz]
      exact Ideal.zero_mem _
    · exact hmem 1 0 (by decide)
  · apply mul_pair_ideal_mem
    · change a * b * z * h ∈ mixedAChain q 2
      have hm := hmem 2 0 (by decide)
      change a * h * b * z ∈ mixedAChain q 2 at hm
      convert hm using 1 <;> ring
    · change a * b * z * b' ∈ mixedAChain q 2
      have hz : a * b * z * b' = 0 := by linear_combination a * hsecond
      rw [hz]
      exact Ideal.zero_mem _
  · apply mul_pair_ideal_mem
    · change a * b * h ∈ mixedAChain q 3
      have hm := hmem 3 1 (by decide)
      change a * h * b ∈ mixedAChain q 3 at hm
      convert hm using 1 <;> ring
    · exact hmem 3 2 (by decide)
  · apply mul_pair_ideal_mem
    · change a * h * a' ∈ mixedAChain q 4
      have hz : a * h * a' = 0 := by linear_combination hfirst
      rw [hz]
      exact Ideal.zero_mem _
    · exact hmem 4 1 (by decide)
  · apply mul_pair_ideal_mem
    · exact hmem 5 4 (by decide)
    · exact hmem 5 3 (by decide)
  · apply mul_pair_ideal_mem
    · change b' * z * a ∈ mixedAChain q 6
      have hm := (mixedAChain q 6).mul_mem_right (b' * z) (hmem 6 5 (by decide))
      change a * (b' * z) ∈ mixedAChain q 6 at hm
      convert hm using 1 <;> ring
    · change b' * z * b ∈ mixedAChain q 6
      have hz : b' * z * b = 0 := by linear_combination hsecond
      rw [hz]
      exact Ideal.zero_mem _
  · apply mul_pair_ideal_mem
    · change z * a ∈ mixedAChain q 7
      exact (mixedAChain q 7).mul_mem_left z (hmem 7 5 (by decide))
    · change z * b' ∈ mixedAChain q 7
      have hm := hmem 7 6 (by decide)
      change b' * z ∈ mixedAChain q 7 at hm
      simpa only [mul_comm] using hm
  · apply mul_pair_ideal_mem
    · change 1 * a ∈ mixedAChain q 8
      rw [one_mul]
      exact hmem 8 5 (by decide)
    · change 1 * z ∈ mixedAChain q 8
      rw [one_mul]
      exact hmem 8 7 (by decide)

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.mixedAChain_mono
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_zero
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_step
#print axioms VOA.DeligneAudit.SL4T.mixedAChain_top
#print axioms VOA.DeligneAudit.SL4T.mixedAThom_stateIdeal
