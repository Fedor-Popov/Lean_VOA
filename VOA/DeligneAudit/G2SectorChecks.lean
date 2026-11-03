/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2SectorChecksA

/-!
# G2 sector data: kernel checks (aggregate)
-/

namespace VOA.DeligneAudit.DeligneSector.G2

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem blk_sound {P : ℕ → Bool} {lo len : ℕ} (h : (List.range' lo len).all P = true) {k : ℕ}
    (h1 : lo ≤ k) (h2 : k < lo + len) : P k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩


/-- Index bounds: the `g2_bound` (the same Boolean). -/
theorem range_ok : rangeCheck 14 br = true := VOA.AffineGeneral.SCLie.g2_bound

theorem u3_ok : (List.range 14).all u3OK = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hk
  exact blk_sound u3_b0 (by omega) (by omega)




theorem stab_ok : stabChecks = true := by
  refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hi hk
  interval_cases i
  · exact blk_sound stab_b0_0 (by omega) (by omega)
  · exact blk_sound stab_b1_0 (by omega) (by omega)
  · exact blk_sound stab_b2_0 (by omega) (by omega)
  · exact blk_sound stab_b3_0 (by omega) (by omega)
  · exact blk_sound stab_b4_0 (by omega) (by omega)
  · exact blk_sound stab_b5_0 (by omega) (by omega)


theorem wt_ok : wtCheck = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hk
  exact blk_sound (P := fun a => (List.range 14).all fun b => (br a b).all fun p => (List.range 2).all fun i => wtZ p.1 i == wtZ a i + wtZ b i) wt_b0 (by omega) (by omega)







end VOA.DeligneAudit.DeligneSector.G2
