/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoWordChecks
import VOA.DeligneAudit.D4FusionRealizationTwoMatrixRange
import VOA.DeligneAudit.DeligneSectorD4Table

/-! The independently checked light matrix payload is exactly the actual
D4 bracket table. No numerical input hypothesis is introduced. -/
namespace VOA.DeligneAudit.D4Two.Certificate

theorem rawBracketTable_eq : rawBracketTable = DeligneSector.D4.brT := rfl

theorem rawBracket_eq (c i : ℕ) : rawBracket c i = DeligneSector.D4.br c i := by
  unfold rawBracket DeligneSector.D4.br
  rw [rawBracketTable_eq]

theorem rawColumn_range (c j : ℕ) (hc : c < 28) (hj : j < 29) :
    rangeCheck 29 (rawColumn c j) = true := by
  have h := column_range_checks
  simp only [columnRangeChecks, List.all_eq_true, List.mem_range] at h
  exact h c hc j hj

/-- Every integer column, including the extra trivial coordinate, is the
actual coadjoint zero-mode matrix. -/
theorem rawColumn_coeff (c i j : ℕ) (hc : c < 28) (hi : i < 29) (hj : j < 29) :
    coeff (rawColumn c j) i =
      if i < 28 ∧ j < 28 then -DeligneSector.Sparse.fZ DeligneSector.D4.br c i j else 0 := by
  have h := List.all_eq_true.mp column_checks_all c
    (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hc⟩)
  simp only [columnCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hh := h i hi j hj
  rw [rawBracket_eq] at hh
  exact hh

theorem rawColumn_complex (c i j : Fin 28) :
    (coeff (rawColumn c j) i : ℂ) =
      -DeligneSector.Sparse.fC 28 DeligneSector.D4.br c i j := by
  rw [rawColumn_coeff c i j c.isLt (by omega) (by omega), if_pos ⟨i.isLt, j.isLt⟩]
  simp only [Int.cast_neg, DeligneSector.Sparse.fC]

end VOA.DeligneAudit.D4Two.Certificate

#print axioms VOA.DeligneAudit.D4Two.Certificate.rawColumn_complex
