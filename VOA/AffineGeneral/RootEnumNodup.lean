/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.RootEnum

/-!
# Structural absence of duplicates in the root enumeration

Candidate integers form an injective affine image of a natural-number
range. Prefixing preserves injectivity, and branches with different tails
are disjoint. Filtering each branch therefore preserves absence of
duplicates without comparing the concrete enumerated vectors in pairs.
-/

namespace VOA.AffineGeneral.RootEnum

theorem cands_nodup (r : Row) (rest : List ℤ) : (cands r rest).Nodup := by
  unfold cands
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply List.Pairwise.imp _ List.nodup_range
  intro i j hne hij
  apply hne
  have hc : (i : ℤ) = (j : ℤ) := add_left_cancel hij
  exact_mod_cast hc

/-- Enumeration has no duplicates for any rows, independently of positivity
or admissibility. -/
theorem enum_nodup (N : ℚ) (rows : List Row) : (enum N rows).Nodup := by
  change List.Pairwise (· ≠ ·) (enum N rows)
  induction rows with
  | nil => simp [enum]
  | cons r rs ih =>
      rw [enum, List.pairwise_flatMap]
      constructor
      · intro rest _
        apply List.Pairwise.filter
        rw [List.pairwise_map]
        apply List.Pairwise.imp _ (cands_nodup r rest)
        intro x y hne hxy
        exact hne (List.cons.inj hxy).1
      · apply ih.imp
        intro rest₁ rest₂ hne s hs₁ t hs₂ hst
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hs₁).1
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hs₂).1
        exact hne (List.cons.inj hst).2

end VOA.AffineGeneral.RootEnum

#print axioms VOA.AffineGeneral.RootEnum.enum_nodup
