/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4DivisorChecksA
import VOA.DeligneAudit.F4DivisorChecksB
import VOA.DeligneAudit.F4DivisorChecksC
import VOA.DeligneAudit.F4DivisorChecksD
import VOA.DeligneAudit.F4DivisorChecksE
import VOA.DeligneAudit.F4DivisorChecksF
import VOA.DeligneAudit.F4DivisorChecksG
import VOA.DeligneAudit.F4DivisorChecksH
import VOA.DeligneAudit.F4DivisorChecksI
import VOA.DeligneAudit.F4DivisorChecksJ
import VOA.DeligneAudit.F4DivisorChecksK
import VOA.DeligneAudit.F4DivisorChecksL
import VOA.DeligneAudit.F4DivisorChecksM
import VOA.DeligneAudit.F4DivisorChecksN
import VOA.DeligneAudit.F4DivisorChecksO
import VOA.DeligneAudit.F4DivisorChecksP
import VOA.DeligneAudit.F4DivisorChecksQ
import VOA.DeligneAudit.F4DivisorChecksR
import VOA.DeligneAudit.F4DivisorChecksS
import VOA.DeligneAudit.F4DivisorChecksT
import VOA.DeligneAudit.F4DivisorChecksU
import VOA.DeligneAudit.F4DivisorChecksV
import VOA.DeligneAudit.F4DivisorChecksW
import VOA.DeligneAudit.F4DivisorChecksX
import VOA.DeligneAudit.F4DivisorChecksY
import VOA.DeligneAudit.F4DivisorChecksZ
import VOA.DeligneAudit.F4DivisorChecksAA
import VOA.DeligneAudit.F4DivisorChecksAB
import VOA.DeligneAudit.F4DivisorChecksAC
import VOA.DeligneAudit.F4DivisorChecksAD
import VOA.DeligneAudit.F4DivisorChecksAE
import VOA.DeligneAudit.F4DivisorChecksAF
import VOA.DeligneAudit.F4DivisorChecksAG
import VOA.DeligneAudit.F4DivisorChecksAH
import VOA.DeligneAudit.F4DivisorChecksAI
import VOA.DeligneAudit.F4DivisorChecksAJ
import VOA.DeligneAudit.F4DivisorChecksAK
import VOA.DeligneAudit.F4DivisorChecksAL
import VOA.DeligneAudit.F4DivisorChecksAM
import VOA.DeligneAudit.F4DivisorChecksAN
import VOA.DeligneAudit.F4DivisorChecksAO
import VOA.DeligneAudit.F4DivisorChecksAP
import VOA.DeligneAudit.F4DivisorChecksAQ
import VOA.DeligneAudit.F4DivisorChecksAR
import VOA.DeligneAudit.F4DivisorChecksAS
import VOA.DeligneAudit.F4DivisorChecksAT
import VOA.DeligneAudit.F4DivisorChecksAU
import VOA.DeligneAudit.F4DivisorChecksAV
import VOA.DeligneAudit.F4DivisorChecksAW
import VOA.DeligneAudit.F4DivisorChecksAX
import VOA.DeligneAudit.F4DivisorChecksAY
import VOA.DeligneAudit.F4DivisorChecksAZ
import VOA.DeligneAudit.F4DivisorChecksBA
import VOA.DeligneAudit.F4DivisorChecksBB
import VOA.DeligneAudit.F4DivisorChecksBC
import VOA.DeligneAudit.F4DivisorChecksBD
import VOA.DeligneAudit.F4DivisorChecksBE
import VOA.DeligneAudit.F4DivisorChecksBF
import VOA.DeligneAudit.F4DivisorChecksBG
import VOA.DeligneAudit.F4DivisorChecksBH
import VOA.DeligneAudit.F4DivisorChecksBI
import VOA.DeligneAudit.F4DivisorChecksBJ
import VOA.DeligneAudit.F4DivisorChecksBK
import VOA.DeligneAudit.F4DivisorChecksBL
import VOA.DeligneAudit.F4DivisorChecksBM
import VOA.DeligneAudit.F4DivisorChecksBN
import VOA.DeligneAudit.F4DivisorChecksBO
import VOA.DeligneAudit.F4DivisorChecksBP
import VOA.DeligneAudit.F4DivisorChecksBQ
import VOA.DeligneAudit.F4DivisorChecksBR
import VOA.DeligneAudit.F4DivisorChecksBS
import VOA.DeligneAudit.F4DivisorChecksBT
import VOA.DeligneAudit.F4DivisorChecksBU
import VOA.DeligneAudit.F4DivisorChecksBV
import VOA.DeligneAudit.F4DivisorChecksBW
import VOA.DeligneAudit.F4DivisorChecksBX
import VOA.DeligneAudit.F4DivisorChecksBY
import VOA.DeligneAudit.F4DivisorChecksBZ
import VOA.DeligneAudit.F4DivisorChecksCA

/-!
# F4 pair-comparison certificates: kernel checks (aggregate)
-/

namespace VOA.DeligneAudit.DeligneDivisor.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneDivisor
open VOA.DeligneAudit.DeligneSector.F4 (br relZ)

theorem f4_colChecks : colChecks = true := by
  refine List.all_eq_true.mpr fun x hx => ?_
  rw [List.mem_range] at hx
  interval_cases x
  · exact f4_col_0
  · exact f4_col_1
  · exact f4_col_2
  · exact f4_col_3
  · exact f4_col_4
  · exact f4_col_5
  · exact f4_col_6
  · exact f4_col_7
  · exact f4_col_8
  · exact f4_col_9
  · exact f4_col_10
  · exact f4_col_11
  · exact f4_col_12
  · exact f4_col_13
  · exact f4_col_14
  · exact f4_col_15
  · exact f4_col_16
  · exact f4_col_17
  · exact f4_col_18
  · exact f4_col_19
  · exact f4_col_20
  · exact f4_col_21
  · exact f4_col_22
  · exact f4_col_23
  · exact f4_col_24
  · exact f4_col_25
  · exact f4_col_26
  · exact f4_col_27
  · exact f4_col_28
  · exact f4_col_29
  · exact f4_col_30
  · exact f4_col_31
  · exact f4_col_32
  · exact f4_col_33
  · exact f4_col_34
  · exact f4_col_35
  · exact f4_col_36
  · exact f4_col_37
  · exact f4_col_38
  · exact f4_col_39
  · exact f4_col_40
  · exact f4_col_41
  · exact f4_col_42
  · exact f4_col_43
  · exact f4_col_44
  · exact f4_col_45
  · exact f4_col_46
  · exact f4_col_47
  · exact f4_col_48
  · exact f4_col_49
  · exact f4_col_50
  · exact f4_col_51

theorem nodeChecks_sound {lo hi : ℕ} (h : nodeChecks lo hi = true) {i : ℕ} (h1 : lo ≤ i)
    (h2 : i < hi) : nodeCheckC 52 colS tab par i = true := by
  simp only [nodeChecks, List.all_eq_true, List.mem_range'] at h
  exact h i ⟨i - lo, by omega, by omega⟩

theorem f4_node (i : ℕ) (h0 : 0 < i) (h1 : i < 2704) : nodeCheckC 52 colS tab par i = true := by
  rcases Nat.lt_or_ge i 150 with h0 | h0
  · exact nodeChecks_sound f4_nodes_1 (by omega) h0
  rcases Nat.lt_or_ge i 300 with h1 | h1
  · exact nodeChecks_sound f4_nodes_150 (by omega) h1
  rcases Nat.lt_or_ge i 450 with h2 | h2
  · exact nodeChecks_sound f4_nodes_300 (by omega) h2
  rcases Nat.lt_or_ge i 600 with h3 | h3
  · exact nodeChecks_sound f4_nodes_450 (by omega) h3
  rcases Nat.lt_or_ge i 750 with h4 | h4
  · exact nodeChecks_sound f4_nodes_600 (by omega) h4
  rcases Nat.lt_or_ge i 900 with h5 | h5
  · exact nodeChecks_sound f4_nodes_750 (by omega) h5
  rcases Nat.lt_or_ge i 1050 with h6 | h6
  · exact nodeChecks_sound f4_nodes_900 (by omega) h6
  rcases Nat.lt_or_ge i 1200 with h7 | h7
  · exact nodeChecks_sound f4_nodes_1050 (by omega) h7
  rcases Nat.lt_or_ge i 1350 with h8 | h8
  · exact nodeChecks_sound f4_nodes_1200 (by omega) h8
  rcases Nat.lt_or_ge i 1500 with h9 | h9
  · exact nodeChecks_sound f4_nodes_1350 (by omega) h9
  rcases Nat.lt_or_ge i 1650 with h10 | h10
  · exact nodeChecks_sound f4_nodes_1500 (by omega) h10
  rcases Nat.lt_or_ge i 1800 with h11 | h11
  · exact nodeChecks_sound f4_nodes_1650 (by omega) h11
  rcases Nat.lt_or_ge i 1950 with h12 | h12
  · exact nodeChecks_sound f4_nodes_1800 (by omega) h12
  rcases Nat.lt_or_ge i 2100 with h13 | h13
  · exact nodeChecks_sound f4_nodes_1950 (by omega) h13
  rcases Nat.lt_or_ge i 2250 with h14 | h14
  · exact nodeChecks_sound f4_nodes_2100 (by omega) h14
  rcases Nat.lt_or_ge i 2400 with h15 | h15
  · exact nodeChecks_sound f4_nodes_2250 (by omega) h15
  rcases Nat.lt_or_ge i 2550 with h16 | h16
  · exact nodeChecks_sound f4_nodes_2400 (by omega) h16
  rcases Nat.lt_or_ge i 2700 with h17 | h17
  · exact nodeChecks_sound f4_nodes_2550 (by omega) h17
  exact nodeChecks_sound f4_nodes_2700 (by omega) (by omega)

theorem UChecks_sound {lo len : ℕ} (h : (List.range' lo len).all UCheck = true) {k : ℕ} (h1 : lo ≤ k)
    (h2 : k < lo + len) : UCheck k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩

theorem f4_UCheck (k : ℕ) (hk : k < 325) : UCheck k = true := by
  rcases Nat.lt_or_ge k 52 with h0 | h0
  · exact UChecks_sound f4_U_0 (by omega) h0
  rcases Nat.lt_or_ge k 104 with h1 | h1
  · exact UChecks_sound f4_U_52 (by omega) h1
  rcases Nat.lt_or_ge k 156 with h2 | h2
  · exact UChecks_sound f4_U_104 (by omega) h2
  rcases Nat.lt_or_ge k 208 with h3 | h3
  · exact UChecks_sound f4_U_156 (by omega) h3
  rcases Nat.lt_or_ge k 260 with h4 | h4
  · exact UChecks_sound f4_U_208 (by omega) h4
  rcases Nat.lt_or_ge k 312 with h5 | h5
  · exact UChecks_sound f4_U_260 (by omega) h5
  exact UChecks_sound f4_U_312 (by omega) (by omega)

theorem antiChecks_sound {lo hi : ℕ} (h : antiChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 52) (hcd : c < d) : antiCheck c d = true := by
  simp only [antiChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem symChecks_sound {lo hi : ℕ} (h : symChecks lo hi = true) {c d : ℕ} (h1 : lo ≤ c)
    (h2 : c < hi) (hd : d < 52) (hcd : c ≤ d) : symCheck c d = true := by
  simp only [symChecks, List.all_eq_true, List.mem_range', List.mem_range, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  rcases h c ⟨c - lo, by omega, by omega⟩ d hd with h | h
  · exact absurd hcd h
  · exact h

theorem dsound {P : ℕ → Bool} {lo len : ℕ} (h : (List.range' lo len).all P = true) {k : ℕ}
    (h1 : lo ≤ k) (h2 : k < lo + len) : P k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩

theorem f4_antiCheck' (c d : ℕ) (hc : c < 52) (hd : d < 52) (hcd : c < d) : antiCheck c d = true := by
  interval_cases c
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_0_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_0_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_1_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_1_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_2_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_2_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_3_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_3_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_4_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_4_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_5_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_5_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_6_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_6_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_7_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_7_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_8_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_8_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_9_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_9_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_10_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_10_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_11_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_11_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_12_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_12_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_13_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_13_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_14_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_14_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_15_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_15_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_16_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_16_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_17_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_17_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_18_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_18_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_19_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_19_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_20_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_20_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_21_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_21_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_22_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_22_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_23_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_23_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_anti_24_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_anti_24_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_25_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_26_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_27_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_28_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_29_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_30_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_31_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_32_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_33_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_34_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_35_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_36_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_37_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_38_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_39_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_40_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_41_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_42_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_43_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_44_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_45_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_46_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_47_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_48_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_49_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_anti_50_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · omega

theorem f4_symCheck' (c d : ℕ) (hc : c < 52) (hd : d < 52) (hcd : c ≤ d) : symCheck c d = true := by
  interval_cases c
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_0_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_0_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_1_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_1_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_2_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_2_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_3_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_3_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_4_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_4_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_5_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_5_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_6_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_6_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_7_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_7_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_8_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_8_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_9_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_9_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_10_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_10_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_11_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_11_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_12_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_12_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_13_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_13_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_14_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_14_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_15_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_15_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_16_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_16_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_17_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_17_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_18_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_18_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_19_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_19_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_20_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_20_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_21_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_21_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_22_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_22_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_23_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_23_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_24_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_24_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · rcases Nat.lt_or_ge d 26 with g0 | g0
    · exact (by have h_ := dsound (k := d) f4_sym_25_0 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
    exact (by have h_ := dsound (k := d) f4_sym_25_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_26_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_27_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_28_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_29_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_30_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_31_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_32_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_33_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_34_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_35_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_36_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_37_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_38_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_39_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_40_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_41_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_42_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_43_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_44_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_45_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_46_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_47_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_48_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_49_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_50_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))
  · exact (by have h_ := dsound (k := d) f4_sym_51_26 (by omega) (by omega); simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h_; exact h_.resolve_left (by omega))

end VOA.DeligneAudit.DeligneDivisor.F4
