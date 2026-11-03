/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6DivisorSymCheck00
import VOA.DeligneAudit.E6DivisorSymCheck01
import VOA.DeligneAudit.E6DivisorSymCheck02
import VOA.DeligneAudit.E6DivisorSymCheck03
import VOA.DeligneAudit.E6DivisorSymCheck04
import VOA.DeligneAudit.E6DivisorSymCheck05
import VOA.DeligneAudit.E6DivisorSymCheck06
import VOA.DeligneAudit.E6DivisorSymCheck07
import VOA.DeligneAudit.E6DivisorSymCheck08
import VOA.DeligneAudit.E6DivisorSymCheck09
import VOA.DeligneAudit.E6DivisorSymCheck10
import VOA.DeligneAudit.E6DivisorSymCheck11
import VOA.DeligneAudit.E6DivisorSymCheck12
import VOA.DeligneAudit.E6DivisorSymCheck13
import VOA.DeligneAudit.E6DivisorSymCheck14
import VOA.DeligneAudit.E6DivisorSymCheck15
import VOA.DeligneAudit.E6DivisorData

/-!
# E₆ pair-comparison certificates: kernel checks (C)

The symmetric certificates, by blocks of rows.  Each theorem is a small `decide +kernel` check (kept small to bound kernel memory).
-/

namespace VOA.DeligneAudit.DeligneDivisor.E6

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor

































theorem symChecks_sound {lo hi : ℕ} (h : symChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 78) (hcd : c ≤ d) : symCheck c d = true := by
  simp only [symChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem e6_symCheck' (c d : ℕ) (hc : c < 78) (hd : d < 78) (hcd : c ≤ d) : symCheck c d = true := by
  rcases Nat.lt_or_ge c 1 with h0 | h0
  · exact symChecks_sound e6_sym_0 (by omega) h0 hd hcd
  rcases Nat.lt_or_ge c 2 with h1 | h1
  · exact symChecks_sound e6_sym_1 (by omega) h1 hd hcd
  rcases Nat.lt_or_ge c 3 with h2 | h2
  · exact symChecks_sound e6_sym_2 (by omega) h2 hd hcd
  rcases Nat.lt_or_ge c 4 with h3 | h3
  · exact symChecks_sound e6_sym_3 (by omega) h3 hd hcd
  rcases Nat.lt_or_ge c 6 with h4 | h4
  · exact symChecks_sound e6_sym_4 (by omega) h4 hd hcd
  rcases Nat.lt_or_ge c 8 with h5 | h5
  · exact symChecks_sound e6_sym_6 (by omega) h5 hd hcd
  rcases Nat.lt_or_ge c 10 with h6 | h6
  · exact symChecks_sound e6_sym_8 (by omega) h6 hd hcd
  rcases Nat.lt_or_ge c 13 with h7 | h7
  · exact symChecks_sound e6_sym_10 (by omega) h7 hd hcd
  rcases Nat.lt_or_ge c 16 with h8 | h8
  · exact symChecks_sound e6_sym_13 (by omega) h8 hd hcd
  rcases Nat.lt_or_ge c 20 with h9 | h9
  · exact symChecks_sound e6_sym_16 (by omega) h9 hd hcd
  rcases Nat.lt_or_ge c 25 with h10 | h10
  · exact symChecks_sound e6_sym_20 (by omega) h10 hd hcd
  rcases Nat.lt_or_ge c 31 with h11 | h11
  · exact symChecks_sound e6_sym_25 (by omega) h11 hd hcd
  rcases Nat.lt_or_ge c 38 with h12 | h12
  · exact symChecks_sound e6_sym_31 (by omega) h12 hd hcd
  rcases Nat.lt_or_ge c 47 with h13 | h13
  · exact symChecks_sound e6_sym_38 (by omega) h13 hd hcd
  rcases Nat.lt_or_ge c 58 with h14 | h14
  · exact symChecks_sound e6_sym_47 (by omega) h14 hd hcd
  exact symChecks_sound e6_sym_58 (by omega) (by omega) hd hcd

end VOA.DeligneAudit.DeligneDivisor.E6
