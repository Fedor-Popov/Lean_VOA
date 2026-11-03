/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorMiscCheck00
import VOA.DeligneAudit.E6DivisorMiscCheck01
import VOA.DeligneAudit.E6DivisorMiscCheck02
import VOA.DeligneAudit.E6DivisorMiscCheck03
import VOA.DeligneAudit.E6DivisorMiscCheck04
import VOA.DeligneAudit.E6DivisorMiscCheck05
import VOA.DeligneAudit.E6DivisorMiscCheck06
import VOA.DeligneAudit.E6DivisorMiscCheck07
import VOA.DeligneAudit.E6DivisorMiscCheck08
import VOA.DeligneAudit.E6DivisorMiscCheck09
import VOA.DeligneAudit.E6DivisorMiscCheck10
import VOA.DeligneAudit.E6DivisorMiscCheck11
import VOA.DeligneAudit.E6DivisorChecksA
import VOA.DeligneAudit.E6DivisorChecksA2

/-!
# E₆ pair-comparison certificates: kernel checks (A3, columns, misc, complement tables)

The 6083 tree nodes (13 blocks), the column tables, the depth bound, the root, the relation ranges, the completeness of `psiT`, and the 651 complement tables (7 blocks).  Each theorem is a small `decide +kernel` check (kept small to bound kernel memory).
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

























theorem nodeChecks_sound {lo hi : ℕ} (h : nodeChecks lo hi = true) {i : ℕ} (h1 : lo ≤ i)
    (h2 : i < hi) : nodeCheckC 78 colE6 tab par i = true := by
  simp only [nodeChecks, List.all_eq_true, List.mem_range'] at h
  exact h i ⟨i - lo, by omega, by omega⟩

theorem e6_node (i : ℕ) (h0 : 0 < i) (h1 : i < 6084) : nodeCheckC 78 colE6 tab par i = true := by
  rcases Nat.lt_or_ge i 470 with h0 | h0
  · exact nodeChecks_sound e6_nodes_1 (by omega) h0
  rcases Nat.lt_or_ge i 939 with h1 | h1
  · exact nodeChecks_sound e6_nodes_470 (by omega) h1
  rcases Nat.lt_or_ge i 1408 with h2 | h2
  · exact nodeChecks_sound e6_nodes_939 (by omega) h2
  rcases Nat.lt_or_ge i 1877 with h3 | h3
  · exact nodeChecks_sound e6_nodes_1408 (by omega) h3
  rcases Nat.lt_or_ge i 2346 with h4 | h4
  · exact nodeChecks_sound e6_nodes_1877 (by omega) h4
  rcases Nat.lt_or_ge i 2815 with h5 | h5
  · exact nodeChecks_sound e6_nodes_2346 (by omega) h5
  rcases Nat.lt_or_ge i 3284 with h6 | h6
  · exact nodeChecks_sound e6_nodes_2815 (by omega) h6
  rcases Nat.lt_or_ge i 3753 with h7 | h7
  · exact nodeChecks_sound e6_nodes_3284 (by omega) h7
  rcases Nat.lt_or_ge i 4222 with h8 | h8
  · exact nodeChecks_sound e6_nodes_3753 (by omega) h8
  rcases Nat.lt_or_ge i 4691 with h9 | h9
  · exact nodeChecks_sound e6_nodes_4222 (by omega) h9
  rcases Nat.lt_or_ge i 5160 with h10 | h10
  · exact nodeChecks_sound e6_nodes_4691 (by omega) h10
  rcases Nat.lt_or_ge i 5629 with h11 | h11
  · exact nodeChecks_sound e6_nodes_5160 (by omega) h11
  exact nodeChecks_sound e6_nodes_5629 (by omega) (by omega)

theorem UChecks_sound {lo : ℕ} (h : (List.range' lo 93).all UCheck = true) {k : ℕ} (h1 : lo ≤ k)
    (h2 : k < lo + 93) : UCheck k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩

theorem e6_UCheck (k : ℕ) (hk : k < 651) : UCheck k = true := by
  rcases Nat.lt_or_ge k 93 with h0 | h0
  · exact UChecks_sound e6_U_0 (by omega) h0
  rcases Nat.lt_or_ge k 186 with h1 | h1
  · exact UChecks_sound e6_U_93 (by omega) h1
  rcases Nat.lt_or_ge k 279 with h2 | h2
  · exact UChecks_sound e6_U_186 (by omega) h2
  rcases Nat.lt_or_ge k 372 with h3 | h3
  · exact UChecks_sound e6_U_279 (by omega) h3
  rcases Nat.lt_or_ge k 465 with h4 | h4
  · exact UChecks_sound e6_U_372 (by omega) h4
  rcases Nat.lt_or_ge k 558 with h5 | h5
  · exact UChecks_sound e6_U_465 (by omega) h5
  exact UChecks_sound e6_U_558 (by omega) (by omega)

end VOA.DeligneAudit.DeligneDivisor.E6
