/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterExceptionalData

/-! Opaque symbolic-function assembly; no closed character algorithm is reduced here. -/
namespace VOA.DeligneAudit.DeligneCharacter

theorem exceptional_dsum_0 (hilb : ℕ → ℕ → ℕ) :
    demazureSumCoeff hilb 0 = hilb 0 0 := by
  simp [demazureSumCoeff, A2.conv, A2.partitionsLe]

theorem exceptional_dsum_1 (hilb : ℕ → ℕ → ℕ) :
    demazureSumCoeff hilb 1 = hilb 0 1 + hilb 1 0 := by
  simp [demazureSumCoeff, A2.conv, A2.partitionsLe, Finset.sum_range_succ]

theorem exceptional_dsum_2 (hilb : ℕ → ℕ → ℕ) :
    demazureSumCoeff hilb 2 = hilb 0 2 + hilb 1 0 + hilb 1 1 + hilb 2 0 := by
  have hcard : {x ∈ Finset.range 2 | 1 - x = 0}.card = 1 := by
    decide +kernel
  simp [demazureSumCoeff, A2.conv, A2.partitionsLe, Finset.sum_range_succ,
    hcard, Nat.add_assoc]

theorem exceptional_map_three (f : ℕ → ℕ) (a b c : ℕ)
    (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) :
    (List.range 3).map f = [a, b, c] := by
  change [f 0, f 1, f 2] = [a, b, c]
  rw [h0, h1, h2]

theorem exceptional_check_three (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ N ∈ List.range 3, P N := by
  intro N hN
  have hlt : N < 3 := List.mem_range.mp hN
  interval_cases N <;> assumption

theorem exceptional_check_two (P : ℕ → Prop) (h0 : P 0) (h1 : P 1) :
    ∀ N ∈ List.range 2, P N := by
  intro N hN
  have hlt : N < 2 := List.mem_range.mp hN
  interval_cases N <;> assumption

end VOA.DeligneAudit.DeligneCharacter
