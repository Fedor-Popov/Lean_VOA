/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorChecksA
import VOA.DeligneAudit.F4SectorChecksB
import VOA.DeligneAudit.F4SectorChecksC
import VOA.DeligneAudit.F4SectorChecksD
import VOA.DeligneAudit.F4SectorChecksE
import VOA.DeligneAudit.F4SectorChecksF
import VOA.DeligneAudit.F4SectorChecksG
import VOA.DeligneAudit.F4SectorChecksH
import VOA.DeligneAudit.F4SectorChecksI
import VOA.DeligneAudit.F4SectorChecksJ
import VOA.DeligneAudit.F4SectorChecksK
import VOA.DeligneAudit.F4SectorChecksL
import VOA.DeligneAudit.F4SectorChecksM
import VOA.DeligneAudit.F4SectorChecksN
import VOA.DeligneAudit.F4SectorChecksO
import VOA.DeligneAudit.F4SectorChecksP
import VOA.DeligneAudit.F4SectorChecksQ
import VOA.DeligneAudit.F4SectorChecksR
import VOA.DeligneAudit.F4SectorChecksS
import VOA.DeligneAudit.F4SectorChecksT
import VOA.DeligneAudit.F4SectorChecksU
import VOA.DeligneAudit.F4SectorChecksV
import VOA.DeligneAudit.F4SectorChecksW
import VOA.DeligneAudit.F4SectorChecksX
import VOA.DeligneAudit.F4SectorChecksY
import VOA.DeligneAudit.F4SectorChecksZ
import VOA.DeligneAudit.F4SectorChecksAA
import VOA.DeligneAudit.F4SectorChecksAB
import VOA.DeligneAudit.F4SectorChecksAC
import VOA.DeligneAudit.F4SectorChecksAD
import VOA.DeligneAudit.F4SectorChecksAE
import VOA.DeligneAudit.F4SectorChecksAF
import VOA.DeligneAudit.F4SectorChecksAG
import VOA.DeligneAudit.F4SectorChecksAH
import VOA.DeligneAudit.F4SectorChecksAI
import VOA.DeligneAudit.F4SectorChecksAJ
import VOA.DeligneAudit.F4SectorChecksAK
import VOA.DeligneAudit.F4SectorChecksAL

/-!
# F4 sector data: kernel checks (aggregate)
-/

namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

theorem blk_sound {P : ℕ → Bool} {lo len : ℕ} (h : (List.range' lo len).all P = true) {k : ℕ}
    (h1 : lo ≤ k) (h2 : k < lo + len) : P k = true := by
  simp only [List.all_eq_true, List.mem_range'] at h
  exact h k ⟨k - lo, by omega, by omega⟩


/-- Index bounds: the `f4_bound` (the same Boolean). -/
theorem range_ok : rangeCheck 52 br = true := VOA.AffineGeneral.SCLie.f4_bound

theorem u3_ok : (List.range 52).all u3OK = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hk
  rcases Nat.lt_or_ge k 1 with h0 | h0
  · exact blk_sound u3_b0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 2 with h1 | h1
  · exact blk_sound u3_b1 (by omega) (by omega)
  rcases Nat.lt_or_ge k 3 with h2 | h2
  · exact blk_sound u3_b2 (by omega) (by omega)
  rcases Nat.lt_or_ge k 4 with h3 | h3
  · exact blk_sound u3_b3 (by omega) (by omega)
  rcases Nat.lt_or_ge k 5 with h4 | h4
  · exact blk_sound u3_b4 (by omega) (by omega)
  rcases Nat.lt_or_ge k 6 with h5 | h5
  · exact blk_sound u3_b5 (by omega) (by omega)
  rcases Nat.lt_or_ge k 7 with h6 | h6
  · exact blk_sound u3_b6 (by omega) (by omega)
  rcases Nat.lt_or_ge k 8 with h7 | h7
  · exact blk_sound u3_b7 (by omega) (by omega)
  rcases Nat.lt_or_ge k 9 with h8 | h8
  · exact blk_sound u3_b8 (by omega) (by omega)
  rcases Nat.lt_or_ge k 10 with h9 | h9
  · exact blk_sound u3_b9 (by omega) (by omega)
  rcases Nat.lt_or_ge k 11 with h10 | h10
  · exact blk_sound u3_b10 (by omega) (by omega)
  rcases Nat.lt_or_ge k 12 with h11 | h11
  · exact blk_sound u3_b11 (by omega) (by omega)
  rcases Nat.lt_or_ge k 13 with h12 | h12
  · exact blk_sound u3_b12 (by omega) (by omega)
  rcases Nat.lt_or_ge k 14 with h13 | h13
  · exact blk_sound u3_b13 (by omega) (by omega)
  rcases Nat.lt_or_ge k 15 with h14 | h14
  · exact blk_sound u3_b14 (by omega) (by omega)
  rcases Nat.lt_or_ge k 16 with h15 | h15
  · exact blk_sound u3_b15 (by omega) (by omega)
  rcases Nat.lt_or_ge k 17 with h16 | h16
  · exact blk_sound u3_b16 (by omega) (by omega)
  rcases Nat.lt_or_ge k 18 with h17 | h17
  · exact blk_sound u3_b17 (by omega) (by omega)
  rcases Nat.lt_or_ge k 19 with h18 | h18
  · exact blk_sound u3_b18 (by omega) (by omega)
  rcases Nat.lt_or_ge k 20 with h19 | h19
  · exact blk_sound u3_b19 (by omega) (by omega)
  rcases Nat.lt_or_ge k 21 with h20 | h20
  · exact blk_sound u3_b20 (by omega) (by omega)
  rcases Nat.lt_or_ge k 22 with h21 | h21
  · exact blk_sound u3_b21 (by omega) (by omega)
  rcases Nat.lt_or_ge k 23 with h22 | h22
  · exact blk_sound u3_b22 (by omega) (by omega)
  rcases Nat.lt_or_ge k 24 with h23 | h23
  · exact blk_sound u3_b23 (by omega) (by omega)
  rcases Nat.lt_or_ge k 25 with h24 | h24
  · exact blk_sound u3_b24 (by omega) (by omega)
  rcases Nat.lt_or_ge k 26 with h25 | h25
  · exact blk_sound u3_b25 (by omega) (by omega)
  rcases Nat.lt_or_ge k 27 with h26 | h26
  · exact blk_sound u3_b26 (by omega) (by omega)
  rcases Nat.lt_or_ge k 28 with h27 | h27
  · exact blk_sound u3_b27 (by omega) (by omega)
  rcases Nat.lt_or_ge k 29 with h28 | h28
  · exact blk_sound u3_b28 (by omega) (by omega)
  rcases Nat.lt_or_ge k 30 with h29 | h29
  · exact blk_sound u3_b29 (by omega) (by omega)
  rcases Nat.lt_or_ge k 31 with h30 | h30
  · exact blk_sound u3_b30 (by omega) (by omega)
  rcases Nat.lt_or_ge k 32 with h31 | h31
  · exact blk_sound u3_b31 (by omega) (by omega)
  rcases Nat.lt_or_ge k 33 with h32 | h32
  · exact blk_sound u3_b32 (by omega) (by omega)
  rcases Nat.lt_or_ge k 34 with h33 | h33
  · exact blk_sound u3_b33 (by omega) (by omega)
  rcases Nat.lt_or_ge k 35 with h34 | h34
  · exact blk_sound u3_b34 (by omega) (by omega)
  rcases Nat.lt_or_ge k 36 with h35 | h35
  · exact blk_sound u3_b35 (by omega) (by omega)
  rcases Nat.lt_or_ge k 37 with h36 | h36
  · exact blk_sound u3_b36 (by omega) (by omega)
  rcases Nat.lt_or_ge k 38 with h37 | h37
  · exact blk_sound u3_b37 (by omega) (by omega)
  rcases Nat.lt_or_ge k 39 with h38 | h38
  · exact blk_sound u3_b38 (by omega) (by omega)
  rcases Nat.lt_or_ge k 40 with h39 | h39
  · exact blk_sound u3_b39 (by omega) (by omega)
  rcases Nat.lt_or_ge k 41 with h40 | h40
  · exact blk_sound u3_b40 (by omega) (by omega)
  rcases Nat.lt_or_ge k 42 with h41 | h41
  · exact blk_sound u3_b41 (by omega) (by omega)
  rcases Nat.lt_or_ge k 43 with h42 | h42
  · exact blk_sound u3_b42 (by omega) (by omega)
  rcases Nat.lt_or_ge k 44 with h43 | h43
  · exact blk_sound u3_b43 (by omega) (by omega)
  rcases Nat.lt_or_ge k 45 with h44 | h44
  · exact blk_sound u3_b44 (by omega) (by omega)
  rcases Nat.lt_or_ge k 46 with h45 | h45
  · exact blk_sound u3_b45 (by omega) (by omega)
  rcases Nat.lt_or_ge k 47 with h46 | h46
  · exact blk_sound u3_b46 (by omega) (by omega)
  rcases Nat.lt_or_ge k 48 with h47 | h47
  · exact blk_sound u3_b47 (by omega) (by omega)
  rcases Nat.lt_or_ge k 49 with h48 | h48
  · exact blk_sound u3_b48 (by omega) (by omega)
  rcases Nat.lt_or_ge k 50 with h49 | h49
  · exact blk_sound u3_b49 (by omega) (by omega)
  rcases Nat.lt_or_ge k 51 with h50 | h50
  · exact blk_sound u3_b50 (by omega) (by omega)
  exact blk_sound u3_b51 (by omega) (by omega)




theorem stab_ok : stabChecks = true := by
  refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hi hk
  interval_cases i
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b0_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b0_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b0_164 (by omega) (by omega)
    exact blk_sound stab_b0_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b1_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b1_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b1_164 (by omega) (by omega)
    exact blk_sound stab_b1_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b2_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b2_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b2_164 (by omega) (by omega)
    exact blk_sound stab_b2_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b3_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b3_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b3_164 (by omega) (by omega)
    exact blk_sound stab_b3_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b4_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b4_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b4_164 (by omega) (by omega)
    exact blk_sound stab_b4_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b5_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b5_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b5_164 (by omega) (by omega)
    exact blk_sound stab_b5_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b6_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b6_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b6_164 (by omega) (by omega)
    exact blk_sound stab_b6_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b7_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b7_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b7_164 (by omega) (by omega)
    exact blk_sound stab_b7_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b8_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b8_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b8_164 (by omega) (by omega)
    exact blk_sound stab_b8_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b9_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b9_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b9_164 (by omega) (by omega)
    exact blk_sound stab_b9_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b10_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b10_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b10_164 (by omega) (by omega)
    exact blk_sound stab_b10_246 (by omega) (by omega)
  · rcases Nat.lt_or_ge k 82 with h0 | h0
    · exact blk_sound stab_b11_0 (by omega) (by omega)
    rcases Nat.lt_or_ge k 164 with h1 | h1
    · exact blk_sound stab_b11_82 (by omega) (by omega)
    rcases Nat.lt_or_ge k 246 with h2 | h2
    · exact blk_sound stab_b11_164 (by omega) (by omega)
    exact blk_sound stab_b11_246 (by omega) (by omega)


theorem wt_ok : wtCheck = true := by
  refine List.all_eq_true.mpr fun k hk => ?_
  rw [List.mem_range] at hk
  rcases Nat.lt_or_ge k 13 with h0 | h0
  · exact blk_sound
      (P := fun a => (List.range 52).all fun b => (br a b).all fun p =>
        (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i)
      wt_b0 (by omega) (by omega)
  rcases Nat.lt_or_ge k 26 with h1 | h1
  · exact blk_sound
      (P := fun a => (List.range 52).all fun b => (br a b).all fun p =>
        (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i)
      wt_b13 (by omega) (by omega)
  rcases Nat.lt_or_ge k 39 with h2 | h2
  · exact blk_sound
      (P := fun a => (List.range 52).all fun b => (br a b).all fun p =>
        (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i)
      wt_b26 (by omega) (by omega)
  exact blk_sound
      (P := fun a => (List.range 52).all fun b => (br a b).all fun p =>
        (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i)
      wt_b39 (by omega) (by omega)







end VOA.DeligneAudit.DeligneSector.F4

#print axioms VOA.DeligneAudit.DeligneSector.F4.u3_ok
#print axioms VOA.DeligneAudit.DeligneSector.F4.stab_ok
#print axioms VOA.DeligneAudit.DeligneSector.F4.wt_ok
#print axioms VOA.DeligneAudit.DeligneSector.F4.raising_ok
#print axioms VOA.DeligneAudit.DeligneSector.F4.cycNodes_ok
#print axioms VOA.DeligneAudit.DeligneSector.F4.cyc_ok
