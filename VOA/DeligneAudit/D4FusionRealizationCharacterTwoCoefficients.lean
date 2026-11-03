import VOA.DeligneAudit.D4FusionRealizationCharacterTwoCore

namespace VOA.DeligneAudit.D4CharacterTwo
open VOA.DeligneAudit.DeligneCharacter
set_option maxRecDepth 100000

/-! Complete integer degree profile of the final finite algorithm state. -/
def profile (N : ℕ) : ℤ :=
  if N = 0 then 300 else if N = 1 then 378 else if N = 2 then 134
  else if N = 3 then 28 else if N = 4 then 1 else 0

set_option maxHeartbeats 2000000 in
-- Bounded exact coefficient of the 389-term literal.
theorem coefficient_0 :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (0 : ℤ))).map
      fun t => t.2).sum = 300 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact coefficient of the 389-term literal.
theorem coefficient_1 :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (1 : ℤ))).map
      fun t => t.2).sum = 378 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact coefficient of the 389-term literal.
theorem coefficient_2 :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (2 : ℤ))).map
      fun t => t.2).sum = 134 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact coefficient of the 389-term literal.
theorem coefficient_3 :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (3 : ℤ))).map
      fun t => t.2).sum = 28 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded exact coefficient of the 389-term literal.
theorem coefficient_4 :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (4 : ℤ))).map
      fun t => t.2).sum = 1 := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Bounded support certificate; the general tail proof below uses these bounds.
theorem support_two : ∀ t ∈ state10, -4 ≤ t.1.2 ∧ t.1.2 ≤ 0 := by
  decide +kernel

theorem state10_coefficient (N : ℕ) :
    ((state10.filter fun (t : Term) => decide (t.1.2 + 4 = (N : ℤ))).map
      fun t => t.2).sum = profile N := by
  unfold profile
  split_ifs with h0 h1 h2 h3 h4
  · subst N; exact coefficient_0
  · subst N; exact coefficient_1
  · subst N; exact coefficient_2
  · subst N; exact coefficient_3
  · subst N; exact coefficient_4
  · have hN : 4 < N := by omega
    have hf : state10.filter (fun (t : Term) => decide (t.1.2 + 4 = (N : ℤ))) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht
      simp only [decide_eq_true_eq]
      have hb := support_two t ht
      omega
    simp only [hf, List.map_nil, List.sum_nil]

end VOA.DeligneAudit.D4CharacterTwo
