/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E6SectorCyclicBase
import VOA.DeligneAudit.E6SectorCycChkA
import VOA.DeligneAudit.E6SectorCycChkB
import VOA.DeligneAudit.E6SectorCycChkC
import VOA.DeligneAudit.E6SectorCycChkD
import VOA.DeligneAudit.E6SectorCycChkE
import VOA.DeligneAudit.E6SectorCycChkF

set_option linter.style.longLine false

/-!
# E₆ sector data: coadjoint cyclicity, part A
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem cyc0 : (Pi.single (0 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (4 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-5 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (4 : ℤ)), ([6, 74, 59], (-2 : ℤ))] (by decide) (3 : ℤ) (by norm_num) cycChk0

theorem cyc1 : (Pi.single (1 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (1 : ℤ)), ([10, 77, 46], (-2 : ℤ)), ([9, 75, 56], (-2 : ℤ)), ([8, 76, 51], (-3 : ℤ)), ([7, 75, 55], (2 : ℤ)), ([6, 74, 59], (-1 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk1

theorem cyc2 : (Pi.single (2 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (5 : ℤ)), ([10, 77, 46], (-6 : ℤ)), ([9, 75, 56], (-10 : ℤ)), ([8, 76, 51], (-12 : ℤ)), ([7, 75, 55], (8 : ℤ)), ([6, 74, 59], (-4 : ℤ))] (by decide) (3 : ℤ) (by norm_num) cycChk2

theorem cyc3 : (Pi.single (3 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (2 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-4 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (4 : ℤ)), ([6, 74, 59], (-2 : ℤ))] (by decide) (1 : ℤ) (by norm_num) cycChk3

theorem cyc4 : (Pi.single (4 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (4 : ℤ)), ([10, 77, 46], (-6 : ℤ)), ([9, 75, 56], (-8 : ℤ)), ([8, 76, 51], (-12 : ℤ)), ([7, 75, 55], (10 : ℤ)), ([6, 74, 59], (-5 : ℤ))] (by decide) (3 : ℤ) (by norm_num) cycChk4

theorem cyc5 : (Pi.single (5 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_combo [([11, 73, 62], (2 : ℤ)), ([10, 77, 46], (-3 : ℤ)), ([9, 75, 56], (-4 : ℤ)), ([8, 76, 51], (-6 : ℤ)), ([7, 75, 55], (5 : ℤ)), ([6, 74, 59], (-4 : ℤ))] (by decide) (3 : ℤ) (by norm_num) cycChk5

theorem cyc6 : (Pi.single (6 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [74, 59] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk6

theorem cyc7 : (Pi.single (7 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75, 55] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk7

theorem cyc8 : (Pi.single (8 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 51] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk8

theorem cyc9 : (Pi.single (9 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75, 56] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk9

theorem cyc10 : (Pi.single (10 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk10

theorem cyc11 : (Pi.single (11 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [73, 62] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk11

theorem cyc12 : (Pi.single (12 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75, 59] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk12

theorem cyc13 : (Pi.single (13 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 55] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk13

theorem cyc14 : (Pi.single (14 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 56] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk14

theorem cyc15 : (Pi.single (15 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 51] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk15

theorem cyc16 : (Pi.single (16 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75, 62] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk16

theorem cyc17 : (Pi.single (17 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 59] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk17

theorem cyc18 : (Pi.single (18 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 60] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk18

theorem cyc19 : (Pi.single (19 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 55] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk19

theorem cyc20 : (Pi.single (20 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 56] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk20

theorem cyc21 : (Pi.single (21 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 62] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk21

theorem cyc22 : (Pi.single (22 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 63] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk22

theorem cyc23 : (Pi.single (23 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 59] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk23

theorem cyc24 : (Pi.single (24 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 60] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk24

theorem cyc25 : (Pi.single (25 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 66] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk25

end

end VOA.DeligneAudit.DeligneCarrier.E6
