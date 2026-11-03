import VOA.DeligneAudit.D4FusionContactQuadraticSourceCheck0
import VOA.DeligneAudit.D4FusionContactQuadraticSourceCheck1
import VOA.DeligneAudit.D4FusionContactQuadraticSourceCheck2
import Mathlib.Tactic.FinCases

namespace VOA.DeligneAudit.D4FusionContact.Quadratic.Source

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

private theorem levi_root_0 : ∀ a : Fin 8, ∀ c : Fin 28,
    fZ br (leviIndex 0) (radIndex a.castSucc) c =
      if c = radIndex (target 0 a).castSucc then sign 0 a else 0 := by
  decide +kernel

private theorem levi_root_1 : ∀ a : Fin 8, ∀ c : Fin 28,
    fZ br (leviIndex 1) (radIndex a.castSucc) c =
      if c = radIndex (target 1 a).castSucc then sign 1 a else 0 := by
  decide +kernel

private theorem levi_root_2 : ∀ a : Fin 8, ∀ c : Fin 28,
    fZ br (leviIndex 2) (radIndex a.castSucc) c =
      if c = radIndex (target 2 a).castSucc then sign 2 a else 0 := by
  decide +kernel

theorem levi_rootZ (i : Fin 3) (a : Fin 8) (c : Fin 28) :
    fZ br (leviIndex i) (radIndex a.castSucc) c =
      if c = radIndex (target i a).castSucc then sign i a else 0 := by
  fin_cases i
  · exact levi_root_0 a c
  · exact levi_root_1 a c
  · exact levi_root_2 a c

theorem levi_root (i : Fin 3) (a : Fin 8) (c : Fin 28) :
    contactF (leviIndex i) (radIndex a.castSucc) c =
      if c = radIndex (target i a).castSucc then (sign i a : ℂ) else 0 := by
  change (fZ br (leviIndex i) (radIndex a.castSucc) c : ℂ) = _
  rw [levi_rootZ]
  split_ifs <;> simp

theorem column_indices : ∀ a b : Fin 8,
    (first (column a b) = a ∧ second (column a b) = b) ∨
    (first (column a b) = b ∧ second (column a b) = a) := by
  decide +kernel

theorem previous_lt : ∀ r : Fin 27, r ≠ 0 → previous r < r := by
  decide +kernel

theorem raw_zero : ∀ k : Fin 36, raw 0 k = if k = 0 then 1 else 0 := by
  decide +kernel

theorem recurrence (r : Fin 27) (hr : r ≠ 0) (k : Fin 36) :
    raw r k = derive (direction r) (raw (previous r)) k := by
  fin_cases r
  · exact (hr rfl).elim
  · exact recurrence_01 k
  · exact recurrence_02 k
  · exact recurrence_03 k
  · exact recurrence_04 k
  · exact recurrence_05 k
  · exact recurrence_06 k
  · exact recurrence_07 k
  · exact recurrence_08 k
  · exact recurrence_09 k
  · exact recurrence_10 k
  · exact recurrence_11 k
  · exact recurrence_12 k
  · exact recurrence_13 k
  · exact recurrence_14 k
  · exact recurrence_15 k
  · exact recurrence_16 k
  · exact recurrence_17 k
  · exact recurrence_18 k
  · exact recurrence_19 k
  · exact recurrence_20 k
  · exact recurrence_21 k
  · exact recurrence_22 k
  · exact recurrence_23 k
  · exact recurrence_24 k
  · exact recurrence_25 k
  · exact recurrence_26 k

end VOA.DeligneAudit.D4FusionContact.Quadratic.Source

#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.levi_root
#print axioms VOA.DeligneAudit.D4FusionContact.Quadratic.Source.recurrence
