/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorD4Data

/-! Concatenation of small independently kernel-checked certificate ranges. -/
namespace VOA.DeligneAudit.DeligneDivisor.D4

open VOA.DeligneAudit.DeligneSector.D4 (br)

theorem check_range_append {f : ℕ → Bool} {start left right : ℕ}
    (hL : (List.range' start left).all f = true)
    (hR : (List.range' (start + left) right).all f = true) :
    (List.range' start (left + right)).all f = true := by
  rw [← List.range'_append_1, List.all_append, hL, hR]
  rfl

/-- Transport and concatenate before instantiating any closed checker. -/
theorem check_family_append (F : ℕ → ℕ → Bool) (f : ℕ → Bool)
    (hF : ∀ lo len, F lo (lo + len) = (List.range' lo len).all f)
    (lo left right : ℕ)
    (hL : F lo (lo + left) = true)
    (hR : F (lo + left) (lo + left + right) = true) :
    F lo (lo + (left + right)) = true := by
  rw [hF] at hL hR ⊢
  exact check_range_append hL hR

theorem nodeChecks_range (lo len : ℕ) :
    nodeChecks lo (lo + len) =
      (List.range' lo len).all (fun i => nodeCheck br 28 tab par i) := by
  simp only [nodeChecks, Nat.add_sub_cancel_left]

theorem antiChecks_range (lo len : ℕ) :
    antiChecks lo (lo + len) = (List.range' lo len).all
      (fun c => (List.range 28).all fun d => !decide (c < d) || antiCheck c d) := by
  simp only [antiChecks, Nat.add_sub_cancel_left]

theorem symChecks_range (lo len : ℕ) :
    symChecks lo (lo + len) = (List.range' lo len).all
      (fun c => (List.range 28).all fun d => !decide (c ≤ d) || symCheck c d) := by
  simp only [symChecks, Nat.add_sub_cancel_left]

theorem nodeChecks_append (lo left right : ℕ)
    (hL : nodeChecks lo (lo + left) = true)
    (hR : nodeChecks (lo + left) (lo + left + right) = true) :
    nodeChecks lo (lo + (left + right)) = true :=
  check_family_append _ _ nodeChecks_range lo left right hL hR

theorem antiChecks_append (lo left right : ℕ)
    (hL : antiChecks lo (lo + left) = true)
    (hR : antiChecks (lo + left) (lo + left + right) = true) :
    antiChecks lo (lo + (left + right)) = true :=
  check_family_append _ _ antiChecks_range lo left right hL hR

theorem symChecks_append (lo left right : ℕ)
    (hL : symChecks lo (lo + left) = true)
    (hR : symChecks (lo + left) (lo + left + right) = true) :
    symChecks lo (lo + (left + right)) = true :=
  check_family_append _ _ symChecks_range lo left right hL hR

/-- Keep checker endpoints literal at every concrete application. -/
theorem check_family_join (F : ℕ → ℕ → Bool) (f : ℕ → Bool)
    (hF : ∀ lo len, F lo (lo + len) = (List.range' lo len).all f)
    (lo mid hi : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hL : F lo mid = true) (hR : F mid hi = true) : F lo hi = true := by
  have ha : lo + (mid - lo) = mid := Nat.add_sub_of_le hlo
  have hb : mid + (hi - mid) = hi := Nat.add_sub_of_le hmid
  have ht : lo + ((mid - lo) + (hi - mid)) = hi := by omega
  have hL' : F lo (lo + (mid - lo)) = true := by rw [ha]; exact hL
  have hR' : F (lo + (mid - lo)) (lo + (mid - lo) + (hi - mid)) = true := by
    rw [ha, hb]
    exact hR
  have h := check_family_append F f hF lo (mid - lo) (hi - mid) hL' hR'
  simpa only [ht] using h

theorem nodeChecks_join (lo mid hi : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hL : nodeChecks lo mid = true) (hR : nodeChecks mid hi = true) :
    nodeChecks lo hi = true :=
  check_family_join _ _ nodeChecks_range lo mid hi hlo hmid hL hR

theorem antiChecks_join (lo mid hi : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hL : antiChecks lo mid = true) (hR : antiChecks mid hi = true) :
    antiChecks lo hi = true :=
  check_family_join _ _ antiChecks_range lo mid hi hlo hmid hL hR

theorem symChecks_join (lo mid hi : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hL : symChecks lo mid = true) (hR : symChecks mid hi = true) :
    symChecks lo hi = true :=
  check_family_join _ _ symChecks_range lo mid hi hlo hmid hL hR

/-- Counts, starts, and the total are separate parameters, not arithmetic
expressions inside a closed Boolean proposition. -/
theorem check_range_join {f : ℕ → Bool} (lo left mid right total : ℕ)
    (hm : lo + left = mid) (ht : left + right = total)
    (hL : (List.range' lo left).all f = true)
    (hR : (List.range' mid right).all f = true) :
    (List.range' lo total).all f = true := by
  rw [← ht]
  apply check_range_append hL
  rw [hm]
  exact hR

/-- The index is symbolic here, so no concrete certificate is evaluated. -/
theorem symChecks_row_of_range (c hi : ℕ) (hhi : hi = c + 1)
    (h : (List.range' 0 28).all (fun d => !decide (c ≤ d) || symCheck c d) = true) :
    symChecks c hi = true := by
  rw [hhi, symChecks_range]
  change ((List.range 28).all (fun d => !decide (c ≤ d) || symCheck c d) && true) = true
  rw [Bool.and_true, List.range_eq_range']
  exact h

theorem antiChecks_row_of_range (c hi : ℕ) (hhi : hi = c + 1)
    (h : (List.range' 0 28).all (fun d => !decide (c < d) || antiCheck c d) = true) :
    antiChecks c hi = true := by
  rw [hhi, antiChecks_range]
  change ((List.range 28).all (fun d => !decide (c < d) || antiCheck c d) && true) = true
  rw [Bool.and_true, List.range_eq_range']
  exact h

end VOA.DeligneAudit.DeligneDivisor.D4
