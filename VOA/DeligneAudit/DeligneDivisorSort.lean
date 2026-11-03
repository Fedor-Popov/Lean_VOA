/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorSparse
import VOA.DeligneAudit.E6Sparse

/-!
# Sort-based zero checks for sparse tables

A sparse table `L : QV` vanishes (all ordered coefficients `qget L a b`, `a, b < 256`) if, after keying each
entry by `256 a + b` and sorting with the structural merge sort (`E6Sparse.msort`), every run of equal keys
has total coefficient zero (`E6Sparse.gz`).  Cost `O(L log L)` instead of the quadratic `ozeroCheck`.

* `qget_eq_zero_of_qzeroSort`, `castQZ_eq_of_sort` (ordered coefficients);
* `qpoly_eq_zero_of_qzeroSortSym` (symmetric coefficients, for quadratic polynomials).
-/

namespace VOA.DeligneAudit.DeligneDivisor

open VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.E6Sparse (KTerm msort msort_perm gz)

noncomputable section

/-- Total coefficient of key `k`. -/
def kget (l : List KTerm) (k : ℕ) : ℤ := (l.map fun t => if t.2 = k then t.1 else 0).sum

theorem kget_cons (t : KTerm) (l : List KTerm) (k : ℕ) :
    kget (t :: l) k = (if t.2 = k then t.1 else 0) + kget l k := by
  simp [kget]

theorem kget_perm {l₁ l₂ : List KTerm} (h : l₁.Perm l₂) (k : ℕ) : kget l₁ k = kget l₂ k :=
  (h.map _).sum_eq

theorem gz_kget (k : ℕ) (s : ℤ) (l : List KTerm) (h : gz k s l = true) (k' : ℕ) :
    (if k = k' then s else 0) + kget l k' = 0 := by
  induction l generalizing k s with
  | nil =>
    simp only [gz, beq_iff_eq] at h
    simp [h, kget]
  | cons t rest ih =>
    simp only [gz] at h
    split_ifs at h with hk
    · have := ih k (s + t.1) h
      have hk' := Nat.eq_of_beq_eq_true hk
      rw [kget_cons, hk']
      split_ifs at this ⊢ <;> linarith
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      have := ih t.2 t.1 h.2
      rw [kget_cons, h.1]
      simpa using this

/-- Keys `256 a + b`. -/
def keyQ (L : QV) : List KTerm := L.map fun t => (t.2.2, t.1 * 256 + t.2.1)

/-- All indices are `< 256`. -/
def small256 (L : QV) : Bool := L.all fun t => decide (t.1 < 256) && decide (t.2.1 < 256)

/-- Sort-based zero check. -/
def qzeroSort (L : QV) : Bool :=
  small256 L &&
    match msort 40 (keyQ L) with
    | [] => true
    | t :: rest => gz t.2 t.1 rest

theorem kget_eq_zero_of_sorted {l : List KTerm}
    (h : (match l with | [] => true | t :: rest => gz t.2 t.1 rest) = true) (k : ℕ) :
    kget l k = 0 := by
  match l, h with
  | [], _ => rfl
  | t :: rest, h =>
    rw [kget_cons]
    have := gz_kget t.2 t.1 rest h k
    simpa [eq_comm] using this

theorem qget_eq_kget (L : QV) (hL : small256 L = true) {a b : ℕ} (ha : a < 256) (hb : b < 256) :
    qget L a b = kget (keyQ L) (a * 256 + b) := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    simp only [small256, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hL
    rw [keyQ, List.map_cons, kget_cons, ← keyQ, qget_cons, ih hL.2]
    congr 1
    have e : (t.1 * 256 + t.2.1 = a * 256 + b) ↔ (t.1 = a ∧ t.2.1 = b) := by
      constructor
      · intro h; omega
      · rintro ⟨rfl, rfl⟩; rfl
    by_cases h : t.1 = a ∧ t.2.1 = b
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (e.mp h'))]

theorem qget_eq_zero_of_qzeroSort {L : QV} (h : qzeroSort L = true) {a b : ℕ} (ha : a < 256)
    (hb : b < 256) : qget L a b = 0 := by
  unfold qzeroSort at h
  rw [Bool.and_eq_true] at h
  rw [qget_eq_kget L h.1 ha hb, ← kget_perm (msort_perm 40 (keyQ L))]
  exact kget_eq_zero_of_sorted h.2 _

theorem castQZ_eq_of_sort {S : DeligneSectorData} (hn : S.n ≤ 256) {L M : QV}
    (h : qzeroSort (L ++ smulQ (-1) M) = true) : castQZ (S := S) L = castQZ M := by
  funext c d
  have := qget_eq_zero_of_qzeroSort h (lt_of_lt_of_le c.2 hn) (lt_of_lt_of_le d.2 hn)
  rw [qget_append, qget_smulQ] at this
  simp only [castQZ]; linarith

/-- Symmetric zero check: orient, then sort. -/
def qzeroSortSym (L : QV) : Bool := qzeroSort (orient L)

theorem qpoly_eq_zero_of_qzeroSortSym {n : ℕ} (hn : n ≤ 256) {L : QV}
    (h : qzeroSortSym L = true) : qpoly n L = 0 := by
  rw [← qpoly_orient, qpoly_eq_sum_qget]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [qget_eq_zero_of_qzeroSort h (lt_of_lt_of_le a.2 hn) (lt_of_lt_of_le b.2 hn)]
  simp

end

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.castQZ_eq_of_sort
#print axioms VOA.DeligneAudit.DeligneDivisor.qpoly_eq_zero_of_qzeroSortSym
end AxiomAudit
