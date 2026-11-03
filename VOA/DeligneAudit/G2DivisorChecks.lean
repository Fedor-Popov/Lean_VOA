/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.G2DivisorChecksA
import VOA.DeligneAudit.G2DivisorChecksB
import VOA.DeligneAudit.G2DivisorChecksC
import VOA.DeligneAudit.G2DivisorChecksD
import VOA.DeligneAudit.G2DivisorChecksE
import VOA.DeligneAudit.G2DivisorChecksF
import VOA.DeligneAudit.G2DivisorChecksG
import VOA.DeligneAudit.G2DivisorChecksH

/-!
# G2 pair-comparison certificates: kernel checks (aggregate)
-/

namespace VOA.DeligneAudit.DeligneDivisor.G2

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.G2 (br relZ)

theorem g2_colChecks : colChecks = true := by
  refine List.all_eq_true.mpr fun x hx => ?_
  rw [List.mem_range] at hx
  interval_cases x
  · exact g2_col_0
  · exact g2_col_1
  · exact g2_col_2
  · exact g2_col_3
  · exact g2_col_4
  · exact g2_col_5
  · exact g2_col_6
  · exact g2_col_7
  · exact g2_col_8
  · exact g2_col_9
  · exact g2_col_10
  · exact g2_col_11
  · exact g2_col_12
  · exact g2_col_13

theorem nodeChecks_sound {lo hi : ℕ} (h : nodeChecks lo hi = true) {i : ℕ} (h1 : lo ≤ i)
    (h2 : i < hi) : nodeCheckC 14 colS tab par i = true := by
  simp only [nodeChecks, List.all_eq_true, List.mem_range'] at h
  exact h i ⟨i - lo, by omega, by omega⟩

theorem g2_node (i : ℕ) (h0 : 0 < i) (h1 : i < 196) : nodeCheckC 14 colS tab par i = true := by
  exact nodeChecks_sound g2_nodes_1 (by omega) (by omega)

theorem UChecks_sound {lo len : ℕ} (h : (List.range' lo len).all UCheck = true) {k : ℕ} (h1 : lo ≤ k)
    (h2 : k < lo + len) : UCheck k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩

theorem g2_UCheck (k : ℕ) (hk : k < 28) : UCheck k = true := by
  rcases Nat.lt_or_ge k 14 with h0 | h0
  · exact UChecks_sound g2_U_0 (by omega) h0
  exact UChecks_sound g2_U_14 (by omega) (by omega)

theorem antiChecks_sound {lo hi : ℕ} (h : antiChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 14) (hcd : c < d) : antiCheck c d = true := by
  simp only [antiChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem symChecks_sound {lo hi : ℕ} (h : symChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 14) (hcd : c ≤ d) : symCheck c d = true := by
  simp only [symChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem g2_antiCheck' (c d : ℕ) (_hc : c < 14) (hd : d < 14) (hcd : c < d) : antiCheck c d = true := by
  exact antiChecks_sound g2_anti_0 (by omega) (by omega) hd hcd

theorem g2_symCheck' (c d : ℕ) (_hc : c < 14) (hd : d < 14) (hcd : c ≤ d) : symCheck c d = true := by
  exact symChecks_sound g2_sym_0 (by omega) (by omega) hd hcd

end VOA.DeligneAudit.DeligneDivisor.G2
