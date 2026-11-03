/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseH

/-! # Structural split for the H-left Zhu-circle branch -/

namespace VOA.LatGen.WpTwoZhuSparseCompute

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute

theorem l3hSparseQ_eq_expected :
    virActSparseQ 3 hThreeSparseQ = l3hExpectedQ := by
  norm_num (config := { maxSteps := 1000000 })
    [virActSparseQ, hThreeSparseQ, sThreeSparseQ, virVacuumSparseQ,
    l3hExpectedQ,
    virShiftRawQ, mulSparseQ, vacuumSparseQ, bindQ, sumQ, addQ, scaleQ,
    normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord,
    List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, Function.comp_apply]

def hEntryModeSparseQ (i : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (-4725 / 2048)
    (scaleQ (Nat.choose 3 i)
      (voaModeActSparseQ hThreeSparseQ ((i : ℤ) - 2) 6
        (virActSparseQ 3 hThreeSparseQ)))

def hLeftPartSparseQ : ℕ → SparseRational.Poly ℕ
  | 0 => [([0, 0, 0], 1 / 6)]
  | 1 => [([0, 1], 1 / 2)]
  | 2 => [([2], 1 / 3)]
  | _ => []

def hEntryModePartSparseQ (i j : ℕ) : SparseRational.Poly ℕ :=
  scaleQ (-4725 / 2048)
    (scaleQ (Nat.choose 3 i)
      (voaModeActSparseQ (hLeftPartSparseQ j) ((i : ℤ) - 2) 6
        l3hExpectedQ))

theorem hEntryMode_split (i : ℕ) (hi : Nat.choose 3 i ≠ 0) :
    hEntryModeSparseQ i = sumQ [hEntryModePartSparseQ i 0,
      hEntryModePartSparseQ i 1, hEntryModePartSparseQ i 2] := by
  unfold hEntryModeSparseQ
  rw [l3hSparseQ_eq_expected]
  have hH : hThreeSparseQ =
      [([0, 0, 0], 1 / 6), ([0, 1], 1 / 2), ([2], 1 / 3)] := by
    norm_num [hThreeSparseQ, sThreeSparseQ, normalizeQ, insertQ,
      sortWord, insertVar, insertSorted, compareWord]
  rw [hH]
  unfold voaModeActSparseQ zhuStateActSparseQ bindQ
  simp only [List.map_cons, List.map_nil]
  rw [scaleQ_sumQ (Nat.choose 3 i) (by exact_mod_cast hi),
    scaleQ_sumQ (-4725 / 2048) (by norm_num)]
  simp only [List.map_cons, List.map_nil]
  simp only [hEntryModePartSparseQ, hLeftPartSparseQ,
    voaModeActSparseQ, zhuStateActSparseQ, bindQ, List.map_cons,
    List.map_nil, sumQ, addQ_nil_right]

end VOA.LatGen.WpTwoZhuSparseCompute
