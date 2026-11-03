/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.F4SectorChecksData

/-! Symbolic assembly of small F4 certificate leaves. -/
namespace VOA.DeligneAudit.DeligneSector.F4

open VOA.DeligneAudit.DeligneSector.Sparse VOA.DeligneAudit.DeligneSector.Generate
open VOA.DeligneAudit.DeligneDivisor

/-- All arithmetic is supplied separately from the closed checker proposition. -/
theorem f4_range_join {P : ℕ → Bool} (lo left mid right total : ℕ)
    (hm : lo + left = mid) (ht : left + right = total)
    (hL : (List.range' lo left).all P = true)
    (hR : (List.range' mid right).all P = true) :
    (List.range' lo total).all P = true := by
  rw [← ht, ← List.range'_append_1, List.all_append, hm, hL, hR]
  rfl

/-- Change a range length by transport of the whole proposition. -/
theorem f4_range_length {P : ℕ → Bool} (start old new : ℕ) (h : old = new)
    (hc : (List.range' start new).all P = true) :
    (List.range' start old).all P = true :=
  (congrArg (fun len => (List.range' start len).all P = true) h).mpr hc

/-- Recover a list-wide check from its independently checked indices. -/
theorem f4_all_of_getD {α : Type*} (xs : List α) (fallback : α) (P : α → Bool)
    (h : (List.range' 0 xs.length).all (fun i => P (xs.getD i fallback)) = true) :
    xs.all P = true := by
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hh := List.all_eq_true.mp h i (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  simpa only [List.getD_eq_getElem _ _ hi] using hh

/-- The non-recursive row of a generation-tree certificate. -/
def f4_generation_row (n : ℕ) (br : ℕ → ℕ → SV)
    (t : ℕ × ℕ × ℕ × ℤ) (seen : List ℕ) : Bool :=
  decide (t.2.1 ∈ seen) && decide (t.2.2.1 ∈ seen) && decide (t.1 < n) &&
    decide (t.2.1 < n) && decide (t.2.2.1 < n) && decide (t.2.2.2 ≠ 0) &&
    decide (br t.2.1 t.2.2.1 = [(t.1, t.2.2.2)])

def f4_generation_at (n : ℕ) (br : ℕ → ℕ → SV)
    (gen : List (ℕ × ℕ × ℕ × ℤ)) (seen : List ℕ) (i : ℕ) : Bool :=
  f4_generation_row n br (gen.getD i (0, 0, 0, 0))
    (((gen.take i).map (·.1)).reverse ++ seen)

/-- The generation recursion is reconstructed before closing any concrete input. -/
theorem f4_genCheck_of_rows (n : ℕ) (br : ℕ → ℕ → SV)
    (gen : List (ℕ × ℕ × ℕ × ℤ)) (seen : List ℕ)
    (h : ∀ i, i < gen.length → f4_generation_at n br gen seen i = true) :
    genCheck n br gen seen = true := by
  induction gen generalizing seen with
  | nil => rfl
  | cons t gen ih =>
      have h0 : f4_generation_row n br t seen = true := by
        simpa [f4_generation_at] using h 0 (by simp)
      have ht : ∀ i, i < gen.length →
          f4_generation_at n br gen (t.1 :: seen) i = true := by
        intro i hi
        have hh := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa [f4_generation_at, List.take_succ_cons, List.reverse_cons,
          List.append_assoc] using hh
      change (f4_generation_row n br t seen && genCheck n br gen (t.1 :: seen)) = true
      rw [h0, ih _ ht]
      rfl

/-- The single cyclic-vector check, separate from the whole family. -/
def f4_cyclic_row (c : ℕ) : Bool :=
  (cyc c).1 != 0 &&
    (cyc c).2.all (fun p => decide (p.1 < vecR.length) && decide ((cpar p.1).2.2 ≤ 22)) &&
    zeroCheck (((cyc c).2.flatMap fun p => smulSV p.2 (vecs p.1)) ++
      smulSV (-1) (smulSV (cyc c).1 [(c, 1)]))

/-- One bracket-weight row of the original finite check. -/
def f4_weight_row (a : ℕ) : Bool :=
  (List.range 52).all fun b => (br a b).all fun p =>
    (List.range 4).all fun i => wtZ p.1 i == wtZ a i + wtZ b i

def f4_rel_range_row (k : ℕ) : Bool :=
  (relZ k).all fun t => decide (t.1 < 52) && decide (t.2.1 < 52)

def f4_diag_row (k : ℕ) : Bool :=
  (relZ k).all fun t => !(t.1 = 45 ∧ t.2.1 = 45)

def f4_node_row (i : ℕ) : Bool := cycNodeCheck rows vecs cpar 52 i

theorem f4_relRange_of_rows
    (h : (List.range' 0 325).all f4_rel_range_row = true) : relRange = true := by
  change (List.range 325).all f4_rel_range_row = true
  rw [List.range_eq_range']
  exact h

theorem f4_cycNodes_of_rows (count : ℕ) (hlen : vecR.length - 1 = count)
    (h : (List.range' 1 count).all f4_node_row = true) : cycNodes = true := by
  change (List.range' 1 (vecR.length - 1)).all f4_node_row = true
  exact f4_range_length 1 _ _ hlen h

theorem f4_cycCheck_of_rows
    (h : (List.range' 0 52).all f4_cyclic_row = true) : cycCheck = true := by
  change (List.range 52).all f4_cyclic_row = true
  rw [List.range_eq_range']
  exact h

theorem f4_raising_from_rows
    (h : ∀ e ∈ posL, ∀ y : Fin 52, fZ br e y 45 = 0) :
    ∀ e y : Fin 52, e.val ∈ posL → fZ br e y 45 = 0 := by
  intro e y he
  exact h e.val he y

end VOA.DeligneAudit.DeligneSector.F4
