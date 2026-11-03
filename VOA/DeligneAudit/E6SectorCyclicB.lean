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
# E₆ sector data: coadjoint cyclicity, part B
-/

set_option maxRecDepth 100000

namespace VOA.DeligneAudit.DeligneCarrier.E6

open MvPolynomial VOA.QuadraticJetCoefficientPairing VOA.DeligneAudit.E6Sparse VOA.DeligneAudit.E6SectorSparse
open VOA.AffineGeneral.SCLie VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector

noncomputable section

theorem cyc26 : (Pi.single (26 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 62] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk26

theorem cyc27 : (Pi.single (27 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 63] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk27

theorem cyc28 : (Pi.single (28 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 64] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk28

theorem cyc29 : (Pi.single (29 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76, 68] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk29

theorem cyc30 : (Pi.single (30 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 66] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk30

theorem cyc31 : (Pi.single (31 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 67] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk31

theorem cyc32 : (Pi.single (32 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 68] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk32

theorem cyc33 : (Pi.single (33 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 69] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk33

theorem cyc34 : (Pi.single (34 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 70] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk34

theorem cyc35 : (Pi.single (35 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 71] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk35

theorem cyc36 : (Pi.single (36 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 72] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk36

theorem cyc37 : (Pi.single (37 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 73] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk37

theorem cyc38 : (Pi.single (38 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 74] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk38

theorem cyc39 : (Pi.single (39 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 75] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk39

theorem cyc40 : (Pi.single (40 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 76] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk40

theorem cyc41 : (Pi.single (41 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [77, 77] ⟨by decide, by decide⟩ (2 : ℤ) (by norm_num) cycChk41

theorem cyc42 : (Pi.single (42 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [72, 55] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk42

theorem cyc43 : (Pi.single (43 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [74, 51] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk43

theorem cyc44 : (Pi.single (44 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk44

theorem cyc45 : (Pi.single (45 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [73, 51] ⟨by decide, by decide⟩ (1 : ℤ) (by norm_num) cycChk45

theorem cyc46 : (Pi.single (46 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [76] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk46

theorem cyc47 : (Pi.single (47 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [70, 56] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk47

theorem cyc48 : (Pi.single (48 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [72, 51] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk48

theorem cyc49 : (Pi.single (49 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [74, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk49

theorem cyc50 : (Pi.single (50 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [73, 46] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk50

theorem cyc51 : (Pi.single (51 : Fin 78) 1 : Fin 78 → ℂ) ∈ slotWords fE6 77 3 :=
  mem_of_word [75] ⟨by decide, by decide⟩ (-1 : ℤ) (by norm_num) cycChk51

end

end VOA.DeligneAudit.DeligneCarrier.E6
