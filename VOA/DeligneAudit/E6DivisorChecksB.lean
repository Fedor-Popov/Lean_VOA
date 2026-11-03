/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorData

/-!
# E₆ pair-comparison certificates: kernel checks (B)

The antisymmetric certificates, by blocks of rows.  Each theorem is a small `decide +kernel` check (kept small to bound kernel memory).
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

theorem e6_anti_0 : antiChecks 0 1 = true := by decide +kernel

theorem e6_anti_1 : antiChecks 1 2 = true := by decide +kernel

theorem e6_anti_2 : antiChecks 2 3 = true := by decide +kernel

theorem e6_anti_3 : antiChecks 3 4 = true := by decide +kernel

theorem e6_anti_4 : antiChecks 4 6 = true := by decide +kernel

theorem e6_anti_6 : antiChecks 6 8 = true := by decide +kernel

theorem e6_anti_8 : antiChecks 8 10 = true := by decide +kernel

theorem e6_anti_10 : antiChecks 10 13 = true := by decide +kernel

theorem e6_anti_13 : antiChecks 13 16 = true := by decide +kernel

theorem e6_anti_16 : antiChecks 16 20 = true := by decide +kernel

theorem e6_anti_20 : antiChecks 20 25 = true := by decide +kernel

theorem e6_anti_25 : antiChecks 25 31 = true := by decide +kernel

theorem e6_anti_31 : antiChecks 31 38 = true := by decide +kernel

theorem e6_anti_38 : antiChecks 38 47 = true := by decide +kernel

theorem e6_anti_47 : antiChecks 47 58 = true := by decide +kernel

theorem e6_anti_58 : antiChecks 58 78 = true := by decide +kernel

theorem antiChecks_sound {lo hi : ℕ} (h : antiChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 78) (hcd : c < d) : antiCheck c d = true := by
  simp only [antiChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem e6_antiCheck' (c d : ℕ) (hc : c < 78) (hd : d < 78) (hcd : c < d) : antiCheck c d = true := by
  rcases Nat.lt_or_ge c 1 with h0 | h0
  · exact antiChecks_sound e6_anti_0 (by omega) h0 hd hcd
  rcases Nat.lt_or_ge c 2 with h1 | h1
  · exact antiChecks_sound e6_anti_1 (by omega) h1 hd hcd
  rcases Nat.lt_or_ge c 3 with h2 | h2
  · exact antiChecks_sound e6_anti_2 (by omega) h2 hd hcd
  rcases Nat.lt_or_ge c 4 with h3 | h3
  · exact antiChecks_sound e6_anti_3 (by omega) h3 hd hcd
  rcases Nat.lt_or_ge c 6 with h4 | h4
  · exact antiChecks_sound e6_anti_4 (by omega) h4 hd hcd
  rcases Nat.lt_or_ge c 8 with h5 | h5
  · exact antiChecks_sound e6_anti_6 (by omega) h5 hd hcd
  rcases Nat.lt_or_ge c 10 with h6 | h6
  · exact antiChecks_sound e6_anti_8 (by omega) h6 hd hcd
  rcases Nat.lt_or_ge c 13 with h7 | h7
  · exact antiChecks_sound e6_anti_10 (by omega) h7 hd hcd
  rcases Nat.lt_or_ge c 16 with h8 | h8
  · exact antiChecks_sound e6_anti_13 (by omega) h8 hd hcd
  rcases Nat.lt_or_ge c 20 with h9 | h9
  · exact antiChecks_sound e6_anti_16 (by omega) h9 hd hcd
  rcases Nat.lt_or_ge c 25 with h10 | h10
  · exact antiChecks_sound e6_anti_20 (by omega) h10 hd hcd
  rcases Nat.lt_or_ge c 31 with h11 | h11
  · exact antiChecks_sound e6_anti_25 (by omega) h11 hd hcd
  rcases Nat.lt_or_ge c 38 with h12 | h12
  · exact antiChecks_sound e6_anti_31 (by omega) h12 hd hcd
  rcases Nat.lt_or_ge c 47 with h13 | h13
  · exact antiChecks_sound e6_anti_38 (by omega) h13 hd hcd
  rcases Nat.lt_or_ge c 58 with h14 | h14
  · exact antiChecks_sound e6_anti_47 (by omega) h14 hd hcd
  exact antiChecks_sound e6_anti_58 (by omega) (by omega) hd hcd

end VOA.DeligneAudit.DeligneDivisor.E6
