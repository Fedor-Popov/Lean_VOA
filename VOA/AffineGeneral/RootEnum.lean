/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-!
# Enumerating short vectors from an `LDLᵀ` decomposition (Fincke–Pohst)

If a positive-definite quadratic form is written as `Q(v) = ∑ₖ dₖ (vₖ + ∑_{i>k} Lₖᵢ vᵢ)²` with `dₖ > 0`,
every vector with `Q(v) ≤ N` has every tail sum `∑_{j≥k} (…)` at most `N`.  `enum N rows` builds all
integer suffixes with tail sum `≤ N`, choosing each coordinate from a window of `2R+2` integers around
`-∑ Lₖᵢ vᵢ` (`cands`), where `dₖ R² ≥ N`.  `mem_enum` is the completeness statement: every integer vector
with `tailSum rows v ≤ N` occurs in `enum N rows`.  The lists are computable, so a concrete count
(`decide`) visits only the pruned search tree.
-/

namespace VOA.AffineGeneral.RootEnum

/-- One row of an `LDLᵀ` decomposition: pivot `d`, coefficients `l` on the later coordinates, and a
radius `R` with `d R² ≥ N`. -/
structure Row where
  d : ℚ
  l : List ℚ
  R : ℕ

/-- `∑ aᵢ xᵢ`. -/
def dotQ : List ℚ → List ℤ → ℚ
  | a :: as, x :: xs => a * x + dotQ as xs
  | _, _ => 0

/-- The square term of a row on a suffix `x :: rest`. -/
def term (r : Row) : List ℤ → ℚ
  | [] => 0
  | x :: rest => r.d * ((x : ℚ) + dotQ r.l rest) ^ 2

/-- The tail sum `∑_{j ≥ k}` of the square terms. -/
def tailSum : List Row → List ℤ → ℚ
  | r :: rs, x :: xs => term r (x :: xs) + tailSum rs xs
  | _, _ => 0

/-- The candidate values of the first coordinate given the rest. -/
def cands (r : Row) (rest : List ℤ) : List ℤ :=
  (List.range (2 * r.R + 2)).map fun i : ℕ => ⌊-dotQ r.l rest⌋ - (r.R : ℤ) + (i : ℤ)

/-- All integer suffixes with tail sum `≤ N`. -/
def enum (N : ℚ) : List Row → List (List ℤ)
  | [] => [[]]
  | r :: rs => (enum N rs).flatMap fun rest =>
      ((cands r rest).map (· :: rest)).filter fun s => decide (tailSum (r :: rs) s ≤ N)

/-- The rows are admissible for the bound `N`. -/
def Admissible (N : ℚ) (rows : List Row) : Prop := ∀ r ∈ rows, 0 < r.d ∧ N ≤ r.d * (r.R : ℚ) ^ 2

theorem term_nonneg (r : Row) (hr : 0 < r.d) (s : List ℤ) : 0 ≤ term r s := by
  cases s with
  | nil => exact le_rfl
  | cons x rest => exact mul_nonneg hr.le (sq_nonneg _)

theorem tailSum_nonneg (rows : List Row) (h : ∀ r ∈ rows, 0 < r.d) (s : List ℤ) :
    0 ≤ tailSum rows s := by
  induction rows generalizing s with
  | nil => cases s <;> exact le_rfl
  | cons r rs ih =>
    cases s with
    | nil => exact le_rfl
    | cons x xs =>
      exact add_nonneg (term_nonneg r (h r List.mem_cons_self) _)
        (ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) xs)

theorem mem_cands (r : Row) (rest : List ℤ) (x : ℤ) (N : ℚ) (hr : 0 < r.d)
    (hR : N ≤ r.d * (r.R : ℚ) ^ 2) (hx : term r (x :: rest) ≤ N) : x ∈ cands r rest := by
  set c := dotQ r.l rest
  have hsq : ((x : ℚ) + c) ^ 2 ≤ (r.R : ℚ) ^ 2 := by
    have h1 : r.d * ((x : ℚ) + c) ^ 2 ≤ r.d * (r.R : ℚ) ^ 2 := le_trans hx hR
    exact le_of_mul_le_mul_left h1 hr
  have hR0 : (0 : ℚ) ≤ r.R := Nat.cast_nonneg _
  have habs : |(x : ℚ) + c| ≤ r.R := abs_le_of_sq_le_sq' hsq hR0 |> fun h => abs_le.mpr h
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  have hf1 : ((⌊-c⌋ : ℤ) : ℚ) ≤ -c := Int.floor_le _
  have hf2 : -c < ((⌊-c⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  have hlo' : ⌊-c⌋ - (r.R : ℤ) ≤ x := by
    have : ((⌊-c⌋ - (r.R : ℤ) : ℤ) : ℚ) ≤ x := by push_cast; linarith
    exact_mod_cast this
  have hhi' : x ≤ ⌊-c⌋ + r.R + 1 := by
    have : (x : ℚ) < ((⌊-c⌋ + (r.R : ℤ) + 1 : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this.le
  unfold cands
  rw [List.mem_map]
  refine ⟨(x - (⌊-c⌋ - r.R)).toNat, ?_, ?_⟩
  · rw [List.mem_range]
    omega
  · rw [Int.toNat_of_nonneg (by omega)]
    ring

/-- **Completeness of the enumeration.** -/
theorem mem_enum (N : ℚ) (rows : List Row) (hadm : Admissible N rows) (s : List ℤ)
    (hlen : s.length = rows.length) (hs : tailSum rows s ≤ N) : s ∈ enum N rows := by
  induction rows generalizing s with
  | nil =>
    rw [List.length_nil, List.length_eq_zero_iff] at hlen
    subst hlen
    exact List.mem_singleton_self _
  | cons r rs ih =>
    cases s with
    | nil => simp at hlen
    | cons x rest =>
      have hr := hadm r List.mem_cons_self
      have hadm' : Admissible N rs := fun r' hr' => hadm r' (List.mem_cons_of_mem _ hr')
      have hsum : tailSum (r :: rs) (x :: rest) = term r (x :: rest) + tailSum rs rest := rfl
      have ht := term_nonneg r hr.1 (x :: rest)
      have hts := tailSum_nonneg rs (fun r' hr' => (hadm' r' hr').1) rest
      have hrest : rest ∈ enum N rs :=
        ih hadm' rest (by simpa using hlen) (by linarith)
      have hx : x ∈ cands r rest := mem_cands r rest x N hr.1 hr.2 (by linarith)
      unfold enum
      rw [List.mem_flatMap]
      refine ⟨rest, hrest, ?_⟩
      rw [List.mem_filter, List.mem_map]
      exact ⟨⟨x, hx, rfl⟩, decide_eq_true hs⟩

/-- Every enumerated suffix has the expected length. -/
theorem length_of_mem_enum (N : ℚ) (rows : List Row) (s : List ℤ) (hs : s ∈ enum N rows) :
    s.length = rows.length := by
  induction rows generalizing s with
  | nil => simp [enum] at hs; simp [hs]
  | cons r rs ih =>
    simp only [enum, List.mem_flatMap, List.mem_filter, List.mem_map] at hs
    obtain ⟨rest, hrest, ⟨x, _, rfl⟩, _⟩ := hs
    simp [ih rest hrest]

end VOA.AffineGeneral.RootEnum
