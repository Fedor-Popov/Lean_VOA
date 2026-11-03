/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7SectorChecksDefs
import VOA.DeligneAudit.E7SectorBasicCheck0
import VOA.DeligneAudit.E7SectorBasicCheck1
import VOA.DeligneAudit.E7SectorRaisingCheck7
import VOA.DeligneAudit.E7SectorRaisingCheck10
import VOA.DeligneAudit.E7SectorRaisingCheck13
import VOA.DeligneAudit.E7SectorRaisingCheck16
import VOA.DeligneAudit.E7SectorRaisingCheck19
import VOA.DeligneAudit.E7SectorRaisingCheck22
import VOA.DeligneAudit.E7SectorRaisingCheck25
import VOA.DeligneAudit.E7SectorRaisingCheck28
import VOA.DeligneAudit.E7SectorRaisingCheck31
import VOA.DeligneAudit.E7SectorRaisingCheck34
import VOA.DeligneAudit.E7SectorRaisingCheck37
import VOA.DeligneAudit.E7SectorRaisingCheck40
import VOA.DeligneAudit.E7SectorRaisingCheck43
import VOA.DeligneAudit.E7SectorRaisingCheck46
import VOA.DeligneAudit.E7SectorRaisingCheck49
import VOA.DeligneAudit.E7SectorRaisingCheck52
import VOA.DeligneAudit.E7SectorRaisingCheck55
import VOA.DeligneAudit.E7SectorRaisingCheck58
import VOA.DeligneAudit.E7SectorRaisingCheck61
import VOA.DeligneAudit.E7SectorRaisingCheck64
import VOA.DeligneAudit.E7SectorRaisingCheck67
import VOA.DeligneAudit.E7SectorCartanCheck0
import VOA.DeligneAudit.E7SectorCartanCheck1
import VOA.DeligneAudit.E7SectorCartanCheck2
import VOA.DeligneAudit.E7SectorCartanCheck3
import VOA.DeligneAudit.E7SectorCartanCheck4
import VOA.DeligneAudit.E7SectorCartanCheck5
import VOA.DeligneAudit.E7SectorCartanCheck6

/-! The original E7 sector results, assembled from small opaque checks. -/
namespace VOA.DeligneAudit.DeligneCarrier.E7

open VOA.AffineGeneral.SCLie

set_option linter.style.longLine false

private theorem sectorBasicRange_join {P : ℕ → Bool} {start left right : ℕ}
    (hL : (List.range' start left).all P = true)
    (hR : (List.range' (start + left) right).all P = true) :
    (List.range' start (left + right)).all P = true := by
  rw [← List.range'_append_1,List.all_append,hL,hR]
  rfl

private theorem raising_join_7_13 :
    (List.range' 7 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 7) (left := 3) (right := 3)
    raising_ok_7_10 raising_ok_10_13

private theorem raising_join_16_22 :
    (List.range' 16 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 16) (left := 3) (right := 3)
    raising_ok_16_19 raising_ok_19_22

private theorem raising_join_13_22 :
    (List.range' 13 9).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 13) (left := 3) (right := 6)
    raising_ok_13_16 raising_join_16_22

private theorem raising_join_7_22 :
    (List.range' 7 15).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 7) (left := 6) (right := 9)
    raising_join_7_13 raising_join_13_22

private theorem raising_join_22_28 :
    (List.range' 22 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 22) (left := 3) (right := 3)
    raising_ok_22_25 raising_ok_25_28

private theorem raising_join_31_37 :
    (List.range' 31 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 31) (left := 3) (right := 3)
    raising_ok_31_34 raising_ok_34_37

private theorem raising_join_28_37 :
    (List.range' 28 9).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 28) (left := 3) (right := 6)
    raising_ok_28_31 raising_join_31_37

private theorem raising_join_22_37 :
    (List.range' 22 15).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 22) (left := 6) (right := 9)
    raising_join_22_28 raising_join_28_37

private theorem raising_join_7_37 :
    (List.range' 7 30).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 7) (left := 15) (right := 15)
    raising_join_7_22 raising_join_22_37

private theorem raising_join_37_43 :
    (List.range' 37 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 37) (left := 3) (right := 3)
    raising_ok_37_40 raising_ok_40_43

private theorem raising_join_46_52 :
    (List.range' 46 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 46) (left := 3) (right := 3)
    raising_ok_46_49 raising_ok_49_52

private theorem raising_join_43_52 :
    (List.range' 43 9).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 43) (left := 3) (right := 6)
    raising_ok_43_46 raising_join_46_52

private theorem raising_join_37_52 :
    (List.range' 37 15).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 37) (left := 6) (right := 9)
    raising_join_37_43 raising_join_43_52

private theorem raising_join_55_61 :
    (List.range' 55 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 55) (left := 3) (right := 3)
    raising_ok_55_58 raising_ok_58_61

private theorem raising_join_52_61 :
    (List.range' 52 9).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 52) (left := 3) (right := 6)
    raising_ok_52_55 raising_join_55_61

private theorem raising_join_64_70 :
    (List.range' 64 6).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 64) (left := 3) (right := 3)
    raising_ok_64_67 raising_ok_67_70

private theorem raising_join_61_70 :
    (List.range' 61 9).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 61) (left := 3) (right := 6)
    raising_ok_61_64 raising_join_64_70

private theorem raising_join_52_70 :
    (List.range' 52 18).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 52) (left := 9) (right := 9)
    raising_join_52_61 raising_join_61_70

private theorem raising_join_37_70 :
    (List.range' 37 33).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 37) (left := 15) (right := 18)
    raising_join_37_52 raising_join_52_70

private theorem raising_join_7_70 :
    (List.range' 7 63).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true :=
  sectorBasicRange_join (P := fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0)
    (start := 7) (left := 30) (right := 33)
    raising_join_7_37 raising_join_37_70

theorem raising_ok : (List.range' 7 63).all (fun e => (List.range 133).all fun y => coef (entry e7T e y) 132 == 0) = true := by
  exact raising_join_7_70

theorem cartan_ok : (List.range 7).all (fun h => (List.range 133).all fun y =>
    coef (entry e7T h y) 132 == if y = 132 then -((thetaH ⟨h % 133, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ℤ) else 0) = true := by
  rw [List.range_eq_range']
  exact (sectorBasicRange_join (sectorBasicRange_join cartan_ok_0_1 (sectorBasicRange_join cartan_ok_1_2 cartan_ok_2_3)) (sectorBasicRange_join (sectorBasicRange_join cartan_ok_3_4 cartan_ok_4_5) (sectorBasicRange_join cartan_ok_5_6 cartan_ok_6_7)))

#print axioms wtLink
#print axioms e7_wt_pos
#print axioms raising_ok
#print axioms cartan_ok

end VOA.DeligneAudit.DeligneCarrier.E7
