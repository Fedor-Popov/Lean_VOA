/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.Lex
import Mathlib.Tactic

/-! # Lexicographic partition comparisons for the Gordon filtration -/

namespace VOA.GordonPartitionOrder

/-- A larger multiplicity at the highest changed part forces an increase of the
usual lexicographic order on descending lists of parts. -/
theorem list_lex_of_count_witness (L M : List ℕ)
    (hL : L.Pairwise (· ≥ ·)) (hM : M.Pairwise (· ≥ ·))
    (h : ℕ) (hh : L.count h < M.count h)
    (hhigher : ∀ k, h < k → L.count k = M.count k) :
    List.Lex (· < ·) L M := by
  induction L generalizing M with
  | nil =>
    cases M with
    | nil => simp at hh
    | cons b M => exact List.Lex.nil
  | cons a L ih =>
    cases M with
    | nil => simp at hh
    | cons b M =>
      rcases lt_trichotomy a b with hab | hab | hab
      · exact List.Lex.rel hab
      · subst b
        apply List.Lex.cons
        apply ih M (List.pairwise_cons.mp hL).2 (List.pairwise_cons.mp hM).2
        · simp only [List.count_cons] at hh
          omega
        · intro k hk
          have := hhigher k hk
          simp only [List.count_cons] at this
          omega
      · have hzero : ∀ k, b < k → (b :: M).count k = 0 := by
          intro k hk
          apply List.count_eq_zero.mpr
          simp only [List.mem_cons, not_or]
          constructor
          · omega
          · intro hm
            have := (List.pairwise_cons.mp hM).1 k hm
            omega
        have hhb : h ≤ b := by
          by_contra hn
          have := hzero h (by omega)
          omega
        have := hhigher a (by omega)
        have hza := hzero a hab
        simp only [List.count_cons_self] at this
        omega

/-- The decreasing lexicographic order used in the paper, on actual natural-number partitions. -/
def LexGreater {n : ℕ} (mu lam : Nat.Partition n) : Prop :=
  List.Lex (· < ·) (lam.parts.sort (· ≥ ·)) (mu.parts.sort (· ≥ ·))

theorem lexGreater_of_count_witness {n : ℕ} (mu lam : Nat.Partition n) (h : ℕ)
    (hh : lam.parts.count h < mu.parts.count h)
    (hhigher : ∀ k, h < k → lam.parts.count k = mu.parts.count k) : LexGreater mu lam := by
  apply list_lex_of_count_witness _ _ (Multiset.pairwise_sort _ _) (Multiset.pairwise_sort _ _) h
  · simpa only [← Multiset.coe_count, Multiset.sort_eq] using hh
  · intro k hk
    simpa only [← Multiset.coe_count, Multiset.sort_eq] using hhigher k hk

/-- Replacing two parts by two parts with a strictly larger maximum increases
lexicographic order, even in the presence of any other unchanged parts. Zero new
parts are discarded, as required for the endpoint occupancies. -/
theorem lexGreater_replacing_pair {n a b h l : ℕ} (mu lam : Nat.Partition n)
    (rest : Multiset ℕ) (hab : b ≤ a) (hah : a < h) (hlh : l ≤ h)
    (hlam : lam.parts = rest + {a, b})
    (hmu : mu.parts = (rest + {h, l}).filter (· ≠ 0)) : LexGreater mu lam := by
  apply lexGreater_of_count_witness mu lam h
  · have hha : h ≠ a := by omega
    have hhb : h ≠ b := by omega
    have hh0 : h ≠ 0 := by omega
    simp [hlam, hmu, hha, hhb, hh0]
  · intro k hk
    have hka : k ≠ a := by omega
    have hkb : k ≠ b := by omega
    have hkh : k ≠ h := by omega
    have hkl : k ≠ l := by omega
    have hk0 : k ≠ 0 := by omega
    simp [hlam, hmu, hka, hkb, hkh, hkl, hk0]

/-- The repartitioned pair underlying either outside occupancy range is
lexicographically larger than the original partition. -/
theorem lexGreater_outside_occupancy {n a b v : ℕ} (mu lam : Nat.Partition n)
    (rest : Multiset ℕ) (hab : b ≤ a) (hv : v ≤ a + b)
    (hout : v < b ∨ a < v) (hlam : lam.parts = rest + {a, b})
    (hmu : mu.parts = (rest + {a + b - v, v}).filter (· ≠ 0)) : LexGreater mu lam := by
  by_cases hlarge : v ≤ a + b - v
  · apply lexGreater_replacing_pair mu lam rest hab (by omega) hlarge hlam hmu
  · apply lexGreater_replacing_pair (h := v) (l := a + b - v) mu lam rest hab
      (by omega) (by omega) hlam
    simpa only [Multiset.pair_comm] using hmu

end VOA.GordonPartitionOrder
