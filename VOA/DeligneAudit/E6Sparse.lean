/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-!
# Sparse cubic identities by reflection

A tool for checking large polynomial identities `L · X_a · Q = Σ c · X_x · P_b` in
`MvPolynomial (Fin n) ℂ` (the U3 certificates of the Deligne carrier data) by kernel
reduction instead of `ring`.

* Data are flat lists of naturals, integers in sign-magnitude form (`decZ`); they elaborate
  quickly even for tens of thousands of entries.
* `cubicP l` is the polynomial `Σ c · X_a X_b X_c` of a list of cubic terms. `cubicZero l`
  encodes each term's sorted index triple as one natural (`keyed`), sorts by key (a structural
  merge sort `msort`, a permutation of its input for any fuel), and checks in one scan that
  each run of equal keys has total coefficient zero.
* **`cubicP_eq_zero_of_cubicZero`**: `cubicZero l = true → cubicP l = 0`. Soundness uses only
  that `msort` permutes and that equal keys give equal monomials, not that the sort is correct.
* **`mem_of_u3Check`**: a checked certificate puts `X_a · Q` in the ideal.
-/

namespace VOA.DeligneAudit.E6Sparse

open MvPolynomial

noncomputable section

/-! ## Decoding -/

/-- Sign-magnitude decoding: `2k ↦ k`, `2k+1 ↦ -k`. -/
def decZ (z : ℕ) : ℤ := if z % 2 = 0 then ((z / 2 : ℕ) : ℤ) else -((z / 2 : ℕ) : ℤ)

/-- Group a flat list into triples. -/
def triples : List ℕ → List (ℕ × ℕ × ℕ)
  | a :: b :: c :: r => (a, b, c) :: triples r
  | _ => []

/-- Quadratic terms `(i, j, c)` from flat data `i j z`. -/
def quadOf (l : List ℕ) : List (ℕ × ℕ × ℤ) := (triples l).map fun t => (t.1, t.2.1, decZ t.2.2)

/-- Certificate terms `(c, x, b)` from flat data `z x b`. -/
def certOf (l : List ℕ) : List (ℤ × ℕ × ℕ) := (triples l).map fun t => (decZ t.1, t.2.1, t.2.2)

/-! ## Polynomials of sparse lists -/

variable {n : ℕ}

/-- `X i`, or `0` out of range. -/
def Xn (n : ℕ) (i : ℕ) : MvPolynomial (Fin n) ℂ := if h : i < n then X ⟨i, h⟩ else 0

/-- A cubic term `(c, (a, b, d))`. -/
abbrev CTerm : Type := ℤ × ℕ × ℕ × ℕ

def monoP (n : ℕ) (k : ℕ × ℕ × ℕ) : MvPolynomial (Fin n) ℂ := Xn n k.1 * Xn n k.2.1 * Xn n k.2.2

def cubicP (n : ℕ) (l : List CTerm) : MvPolynomial (Fin n) ℂ :=
  (l.map fun t => (t.1 : MvPolynomial (Fin n) ℂ) * monoP n t.2).sum

def quadP (n : ℕ) (l : List (ℕ × ℕ × ℤ)) : MvPolynomial (Fin n) ℂ :=
  (l.map fun t => (t.2.2 : MvPolynomial (Fin n) ℂ) * (Xn n t.1 * Xn n t.2.1)).sum

theorem cubicP_append (l₁ l₂ : List CTerm) : cubicP n (l₁ ++ l₂) = cubicP n l₁ + cubicP n l₂ := by
  simp [cubicP]

theorem cubicP_cons (t : CTerm) (l : List CTerm) :
    cubicP n (t :: l) = (t.1 : MvPolynomial (Fin n) ℂ) * monoP n t.2 + cubicP n l := by
  simp [cubicP]

theorem cubicP_perm {l₁ l₂ : List CTerm} (h : l₁.Perm l₂) : cubicP n l₁ = cubicP n l₂ :=
  (h.map _).sum_eq

/-- `c · X_x · q` as cubic terms. -/
def mulX (c : ℤ) (x : ℕ) (q : List (ℕ × ℕ × ℤ)) : List CTerm :=
  q.map fun t => (c * t.2.2, x, t.1, t.2.1)

theorem cubicP_mulX (c : ℤ) (x : ℕ) (q : List (ℕ × ℕ × ℤ)) :
    cubicP n (mulX c x q) = (c : MvPolynomial (Fin n) ℂ) * Xn n x * quadP n q := by
  induction q with
  | nil => simp [mulX, cubicP, quadP]
  | cons t q ih =>
    simp only [mulX, List.map_cons] at ih ⊢
    rw [cubicP_cons, ih]
    simp only [quadP, List.map_cons, List.sum_cons, monoP]
    push_cast
    ring

theorem cubicP_flatMap {α : Type*} (l : List α) (f : α → List CTerm) :
    cubicP n (l.flatMap f) = (l.map fun a => cubicP n (f a)).sum := by
  induction l with
  | nil => simp [cubicP]
  | cons a l ih => simp [List.flatMap_cons, cubicP_append, ih]

/-- Negate all coefficients. -/
def negT (l : List CTerm) : List CTerm := l.map fun t => (-t.1, t.2)

theorem cubicP_negT (l : List CTerm) : cubicP n (negT l) = -cubicP n l := by
  induction l with
  | nil => simp [negT, cubicP]
  | cons t l ih =>
    simp only [negT, List.map_cons] at ih ⊢
    rw [cubicP_cons, cubicP_cons, ih]
    push_cast
    ring

/-! ## Canonical keys -/

/-- Sort a triple. -/
def sort3 (k : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let a := k.1; let b := k.2.1; let c := k.2.2
  if a ≤ b then
    if b ≤ c then (a, b, c) else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c) else if b ≤ c then (b, c, a) else (c, b, a)

theorem monoP_sort3 (k : ℕ × ℕ × ℕ) : monoP n (sort3 k) = monoP n k := by
  obtain ⟨a, b, c⟩ := k
  unfold sort3 monoP
  dsimp only
  split_ifs <;> ring

def canon (l : List CTerm) : List CTerm := l.map fun t => (t.1, sort3 t.2)

theorem cubicP_canon (l : List CTerm) : cubicP n (canon l) = cubicP n l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [canon, List.map_cons] at ih ⊢
    rw [cubicP_cons, cubicP_cons, ih, monoP_sort3]

/-! ## Single-number keys -/

/-- Encode a (sorted) triple of indices `< 128`. -/
def enc3 (k : ℕ × ℕ × ℕ) : ℕ := (k.1 * 128 + k.2.1) * 128 + k.2.2

def dec3 (m : ℕ) : ℕ × ℕ × ℕ := (m / 16384, m / 128 % 128, m % 128)

theorem dec3_enc3 (k : ℕ × ℕ × ℕ) (h1 : k.2.1 < 128) (h2 : k.2.2 < 128) : dec3 (enc3 k) = k := by
  obtain ⟨a, b, c⟩ := k
  simp only [dec3, enc3] at *
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

/-- Keyed term: coefficient and encoded monomial. -/
abbrev KTerm : Type := ℤ × ℕ

def kpoly (n : ℕ) (l : List KTerm) : MvPolynomial (Fin n) ℂ :=
  (l.map fun t => (t.1 : MvPolynomial (Fin n) ℂ) * monoP n (dec3 t.2)).sum

theorem kpoly_cons (t : KTerm) (l : List KTerm) :
    kpoly n (t :: l) = (t.1 : MvPolynomial (Fin n) ℂ) * monoP n (dec3 t.2) + kpoly n l := by
  simp [kpoly]

theorem kpoly_perm {l₁ l₂ : List KTerm} (h : l₁.Perm l₂) : kpoly n l₁ = kpoly n l₂ :=
  (h.map _).sum_eq

/-- Indices are `< 128`. -/
def small (l : List CTerm) : Bool := l.all fun t => t.2.1 < 128 && t.2.2.1 < 128 && t.2.2.2 < 128

def keyed (l : List CTerm) : List KTerm := l.map fun t => (t.1, enc3 (sort3 t.2))

theorem sort3_lt (k : ℕ × ℕ × ℕ) (h0 : k.1 < 128) (h1 : k.2.1 < 128) (h2 : k.2.2 < 128) :
    (sort3 k).2.1 < 128 ∧ (sort3 k).2.2 < 128 := by
  obtain ⟨a, b, c⟩ := k
  simp only [sort3] at *
  split_ifs <;> simp <;> omega

theorem kpoly_keyed (l : List CTerm) (h : small l = true) : kpoly n (keyed l) = cubicP n l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [small, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [keyed, List.map_cons] at ih ⊢
    rw [kpoly_cons, cubicP_cons, ih h.2]
    obtain ⟨h1, h2⟩ := sort3_lt t.2 h.1.1.1 h.1.1.2 h.1.2
    rw [dec3_enc3 _ h1 h2, monoP_sort3]

/-! ## A structural merge sort on keys -/

def merge : ℕ → List KTerm → List KTerm → List KTerm
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    if Nat.ble x.2 y.2 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys

theorem merge_perm (f : ℕ) (xs ys : List KTerm) : (merge f xs ys).Perm (xs ++ ys) := by
  induction f generalizing xs ys with
  | zero => simp [merge]
  | succ f ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split_ifs
        · exact (ih xs (y :: ys)).cons x
        · refine ((ih (x :: xs) ys).cons y).trans ?_
          exact List.perm_middle.symm

/-- Split into two halves (alternating), with accumulators. -/
def splitAux : List KTerm → List KTerm → List KTerm → List KTerm × List KTerm
  | x :: y :: r, a, b => splitAux r (x :: a) (y :: b)
  | [x], a, b => (x :: a, b)
  | [], a, b => (a, b)

theorem splitAux_perm : ∀ (l a b : List KTerm),
    ((splitAux l a b).1 ++ (splitAux l a b).2).Perm (l ++ (a ++ b))
  | x :: y :: r, a, b => by
    simp only [splitAux]
    refine (splitAux_perm r (x :: a) (y :: b)).trans ?_
    rw [List.perm_iff_count]
    intro z
    simp only [List.count_append, List.count_cons]
    omega
  | [x], a, b => by simp [splitAux]
  | [], a, b => by simp [splitAux]

def msort : ℕ → List KTerm → List KTerm
  | 0, l => l
  | f + 1, l =>
    match l with
    | [] => []
    | [x] => [x]
    | l =>
      match splitAux l [] [] with
      | (a, b) => merge l.length (msort f a) (msort f b)

theorem msort_perm : ∀ (f : ℕ) (l : List KTerm), (msort f l).Perm l
  | 0, l => by simp [msort]
  | f + 1, [] => by simp [msort]
  | f + 1, [x] => by simp [msort]
  | f + 1, x :: y :: r => by
    have hs := splitAux_perm (x :: y :: r) [] []
    simp only [List.append_nil] at hs
    simp only [msort]
    refine (merge_perm _ _ _).trans ?_
    exact ((msort_perm f _).append (msort_perm f _)).trans hs

/-! ## The group scan -/

/-- Each run of equal keys has total coefficient zero (`s` accumulates the current run). -/
def gz : ℕ → ℤ → List KTerm → Bool
  | _, s, [] => s == 0
  | k, s, t :: rest => if Nat.beq t.2 k then gz k (s + t.1) rest else (s == 0) && gz t.2 t.1 rest

theorem gz_sound (k : ℕ) (s : ℤ) (l : List KTerm) (h : gz k s l = true) :
    (s : MvPolynomial (Fin n) ℂ) * monoP n (dec3 k) + kpoly n l = 0 := by
  induction l generalizing k s with
  | nil =>
    simp only [gz, beq_iff_eq] at h
    simp [h, kpoly]
  | cons t rest ih =>
    simp only [gz] at h
    split_ifs at h with hk
    · have := ih k (s + t.1) h
      rw [kpoly_cons, Nat.eq_of_beq_eq_true hk]
      push_cast at this ⊢
      rw [← this]; ring
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      have := ih t.2 t.1 h.2
      rw [kpoly_cons, h.1]
      simpa using this

/-- **The Boolean check.** -/
def cubicZero (l : List CTerm) : Bool :=
  small l &&
    match msort 40 (keyed l) with
    | [] => true
    | t :: rest => gz t.2 t.1 rest

theorem cubicP_eq_zero_of_cubicZero (l : List CTerm) (h : cubicZero l = true) : cubicP n l = 0 := by
  unfold cubicZero at h
  rw [Bool.and_eq_true] at h
  rw [← kpoly_keyed l h.1, ← kpoly_perm (msort_perm 40 (keyed l))]
  have h2 := h.2
  split at h2
  · rename_i heq; rw [heq]; rfl
  · rename_i t rest heq
    rw [heq, kpoly_cons]
    exact gz_sound t.2 t.1 rest h2

/-! ## Ideal membership from a checked certificate -/

/-- Expansion of a certificate `Σ c · X_x · P_b`. -/
def certExp (relQ : ℕ → List (ℕ × ℕ × ℤ)) (cert : List (ℤ × ℕ × ℕ)) : List CTerm :=
  cert.flatMap fun t => mulX t.1 t.2.1 (relQ t.2.2)

/-- The full U3 check for one current. -/
def u3Check (relQ : ℕ → List (ℕ × ℕ × ℤ)) (q : List (ℕ × ℕ × ℤ)) (a : ℕ) (L : ℤ)
    (cert : List (ℤ × ℕ × ℕ)) : Bool :=
  cubicZero (mulX L a q ++ negT (certExp relQ cert))

/-- **A checked certificate puts `X_a · Q` in the ideal.** -/
theorem mem_of_u3Check (relQ : ℕ → List (ℕ × ℕ × ℤ)) (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : List (ℕ × ℕ × ℤ)) (a : ℕ) (L : ℤ) (hL : L ≠ 0) (cert : List (ℤ × ℕ × ℕ))
    (hrel : ∀ t ∈ cert, quadP n (relQ t.2.2) ∈ I) (h : u3Check relQ q a L cert = true) :
    Xn n a * quadP n q ∈ I := by
  have h0 := cubicP_eq_zero_of_cubicZero (n := n) _ h
  rw [cubicP_append, cubicP_negT, cubicP_mulX, certExp, cubicP_flatMap] at h0
  have hsum : (L : MvPolynomial (Fin n) ℂ) * Xn n a * quadP n q
      = (cert.map fun t => cubicP n (mulX t.1 t.2.1 (relQ t.2.2))).sum := by
    linear_combination h0
  have hmem : (L : MvPolynomial (Fin n) ℂ) * Xn n a * quadP n q ∈ I := by
    rw [hsum]
    refine list_sum_mem fun y hy => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    rw [cubicP_mulX]
    exact I.mul_mem_left _ (hrel t ht)
  have hC : (L : MvPolynomial (Fin n) ℂ) = C (L : ℂ) := by simp
  have h2 := I.mul_mem_left (C ((L : ℂ)⁻¹)) hmem
  rwa [hC, mul_assoc, ← mul_assoc (C _), ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hL),
    map_one, one_mul] at h2


/-! ## Quadratic identities -/

/-- A sparse quadratic identity, checked as the cubic identity `X₀ · q = 0`. -/
def quadZero (l : List (ℕ × ℕ × ℤ)) : Bool := cubicZero (l.map fun t => (t.2.2, 0, t.1, t.2.1))

theorem cubicP_quadEmbed (l : List (ℕ × ℕ × ℤ)) :
    cubicP n (l.map fun t => (t.2.2, 0, t.1, t.2.1)) = Xn n 0 * quadP n l := by
  induction l with
  | nil => simp [cubicP, quadP]
  | cons t l ih =>
    rw [List.map_cons, cubicP_cons, ih]
    simp only [quadP, List.map_cons, List.sum_cons, monoP]
    ring

theorem quadP_eq_zero_of_quadZero (hn : 0 < n) (l : List (ℕ × ℕ × ℤ)) (h : quadZero l = true) :
    quadP n l = 0 := by
  have h0 := cubicP_eq_zero_of_cubicZero (n := n) _ h
  rw [cubicP_quadEmbed] at h0
  have hX : Xn n 0 ≠ 0 := by rw [Xn, dif_pos hn]; exact X_ne_zero _
  exact (mul_eq_zero.mp h0).resolve_left hX

/-- Scale a sparse quadratic. -/
def scaleQ (c : ℤ) (l : List (ℕ × ℕ × ℤ)) : List (ℕ × ℕ × ℤ) := l.map fun t => (t.1, t.2.1, c * t.2.2)

theorem quadP_scaleQ (c : ℤ) (l : List (ℕ × ℕ × ℤ)) :
    quadP n (scaleQ c l) = (c : MvPolynomial (Fin n) ℂ) * quadP n l := by
  induction l with
  | nil => simp [scaleQ, quadP]
  | cons t l ih =>
    simp only [scaleQ, List.map_cons] at ih ⊢
    simp only [quadP, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    push_cast; ring

theorem quadP_append' (l₁ l₂ : List (ℕ × ℕ × ℤ)) : quadP n (l₁ ++ l₂) = quadP n l₁ + quadP n l₂ := by
  simp [quadP]

theorem quadP_flatMap' {α : Type*} (l : List α) (g : α → List (ℕ × ℕ × ℤ)) :
    quadP n (l.flatMap g) = (l.map fun a => quadP n (g a)).sum := by
  induction l with
  | nil => simp [quadP]
  | cons a l ih => simp [List.flatMap_cons, quadP_append', ih]

end

end VOA.DeligneAudit.E6Sparse
