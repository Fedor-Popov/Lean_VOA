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
# E₆ sector data: coadjoint cyclicity, part C
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem cyc52 : (Pi.single (52 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [70, 51] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk52

theorem cyc53 : (Pi.single (53 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [72, 46] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk53

theorem cyc54 : (Pi.single (54 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [71, 46] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk54

theorem cyc55 : (Pi.single (55 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [74] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk55

theorem cyc56 : (Pi.single (56 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [73] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk56

theorem cyc57 : (Pi.single (57 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [70, 46] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk57

theorem cyc58 : (Pi.single (58 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [69, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk58

theorem cyc59 : (Pi.single (59 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [72] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk59

theorem cyc60 : (Pi.single (60 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [71] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk60

theorem cyc61 : (Pi.single (61 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [67, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk61

theorem cyc62 : (Pi.single (62 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [70] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk62

theorem cyc63 : (Pi.single (63 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [69] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk63

theorem cyc64 : (Pi.single (64 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [68] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk64

theorem cyc65 : (Pi.single (65 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [64, 46] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk65

theorem cyc66 : (Pi.single (66 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [67] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk66

theorem cyc67 : (Pi.single (67 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [66] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk67

theorem cyc68 : (Pi.single (68 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [64] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk68

theorem cyc69 : (Pi.single (69 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [63] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk69

theorem cyc70 : (Pi.single (70 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [62] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk70

theorem cyc71 : (Pi.single (71 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [60] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk71

theorem cyc72 : (Pi.single (72 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [59] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk72

theorem cyc73 : (Pi.single (73 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [56] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk73

theorem cyc74 : (Pi.single (74 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [55] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk74

theorem cyc75 : (Pi.single (75 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [51] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk75

theorem cyc76 : (Pi.single (76 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [46] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk76

theorem cyc77 : (Pi.single (77 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk77

end

end VOA.DeligneAudit.DeligneCarrier.E6
