/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.E7Sparse

/-!
# Sparse quadratic identities by reflection

The quadratic analogue of `E7Sparse.cubicZero`: `quadZero l = true → quadP n l = 0`, by sorting the
encoded sorted index pairs (`msort`, a permutation for any fuel) and checking that each run of equal
keys has total coefficient zero.  Indices must be `< 256`.
-/

namespace VOA.DeligneAudit.E7Sparse

open MvPolynomial

noncomputable section

variable {n : ℕ}

/-- `X_i X_j`. -/
def mono2 (n : ℕ) (k : ℕ × ℕ) : MvPolynomial (Fin n) ℂ := Xn n k.1 * Xn n k.2

theorem quadP_cons (t : ℕ × ℕ × ℤ) (l : List (ℕ × ℕ × ℤ)) :
    quadP n (t :: l) = (t.2.2 : MvPolynomial (Fin n) ℂ) * (Xn n t.1 * Xn n t.2.1) + quadP n l := by
  simp [quadP]

theorem quadP_append (l₁ l₂ : List (ℕ × ℕ × ℤ)) : quadP n (l₁ ++ l₂) = quadP n l₁ + quadP n l₂ := by
  simp [quadP]

/-- Sort a pair. -/
def sort2 (k : ℕ × ℕ) : ℕ × ℕ := if k.1 ≤ k.2 then k else (k.2, k.1)

theorem mono2_sort2 (k : ℕ × ℕ) : mono2 n (sort2 k) = mono2 n k := by
  unfold sort2 mono2
  split_ifs <;> simp [mul_comm]

def enc2 (k : ℕ × ℕ) : ℕ := k.1 * 256 + k.2

def dec2 (m : ℕ) : ℕ × ℕ := (m / 256, m % 256)

theorem dec2_enc2 (k : ℕ × ℕ) (h : k.2 < 256) : dec2 (enc2 k) = k := by
  obtain ⟨a, b⟩ := k
  simp only [dec2, enc2] at *
  refine Prod.ext ?_ ?_ <;> dsimp only <;> omega

def kpoly2 (n : ℕ) (l : List KTerm) : MvPolynomial (Fin n) ℂ :=
  (l.map fun t => (t.1 : MvPolynomial (Fin n) ℂ) * mono2 n (dec2 t.2)).sum

theorem kpoly2_cons (t : KTerm) (l : List KTerm) :
    kpoly2 n (t :: l) = (t.1 : MvPolynomial (Fin n) ℂ) * mono2 n (dec2 t.2) + kpoly2 n l := by
  simp [kpoly2]

theorem kpoly2_perm {l₁ l₂ : List KTerm} (h : l₁.Perm l₂) : kpoly2 n l₁ = kpoly2 n l₂ :=
  (h.map _).sum_eq

def small2 (l : List (ℕ × ℕ × ℤ)) : Bool := l.all fun t => t.1 < 256 && t.2.1 < 256

def keyed2 (l : List (ℕ × ℕ × ℤ)) : List KTerm := l.map fun t => (t.2.2, enc2 (sort2 (t.1, t.2.1)))

theorem kpoly2_keyed (l : List (ℕ × ℕ × ℤ)) (h : small2 l = true) :
    kpoly2 n (keyed2 l) = quadP n l := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [small2, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [keyed2, List.map_cons] at ih ⊢
    rw [kpoly2_cons, quadP_cons, ih h.2]
    have hs : (sort2 (t.1, t.2.1)).2 < 256 := by
      unfold sort2; split_ifs <;> simp <;> omega
    rw [dec2_enc2 _ hs, mono2_sort2]
    rfl

theorem gz2_sound (k : ℕ) (s : ℤ) (l : List KTerm) (h : gz k s l = true) :
    (s : MvPolynomial (Fin n) ℂ) * mono2 n (dec2 k) + kpoly2 n l = 0 := by
  induction l generalizing k s with
  | nil =>
    simp only [gz, beq_iff_eq] at h
    simp [h, kpoly2]
  | cons t rest ih =>
    simp only [gz] at h
    split_ifs at h with hk
    · have := ih k (s + t.1) h
      rw [kpoly2_cons, Nat.eq_of_beq_eq_true hk]
      push_cast at this ⊢
      rw [← this]; ring
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      have := ih t.2 t.1 h.2
      rw [kpoly2_cons, h.1]
      simpa using this

/-- **The Boolean check** for quadratic identities. -/
def quadZero (l : List (ℕ × ℕ × ℤ)) : Bool :=
  small2 l &&
    match msort 40 (keyed2 l) with
    | [] => true
    | t :: rest => gz t.2 t.1 rest

theorem quadP_eq_zero_of_quadZero (l : List (ℕ × ℕ × ℤ)) (h : quadZero l = true) :
    quadP n l = 0 := by
  unfold quadZero at h
  rw [Bool.and_eq_true] at h
  rw [← kpoly2_keyed l h.1, ← kpoly2_perm (msort_perm 40 (keyed2 l))]
  have h2 := h.2
  split at h2
  · rename_i heq; rw [heq]; rfl
  · rename_i t rest heq
    rw [heq, kpoly2_cons]
    exact gz2_sound t.2 t.1 rest h2

/-- Scale coefficients. -/
def scaleQ (c : ℤ) (l : List (ℕ × ℕ × ℤ)) : List (ℕ × ℕ × ℤ) := l.map fun t => (t.1, t.2.1, c * t.2.2)

theorem quadP_scaleQ (c : ℤ) (l : List (ℕ × ℕ × ℤ)) :
    quadP n (scaleQ c l) = (c : MvPolynomial (Fin n) ℂ) * quadP n l := by
  induction l with
  | nil => simp [scaleQ, quadP]
  | cons t l ih =>
    simp only [scaleQ, List.map_cons] at ih ⊢
    rw [quadP_cons, quadP_cons, ih]
    push_cast
    ring

end

end VOA.DeligneAudit.E7Sparse

section AxiomAudit
#print axioms VOA.DeligneAudit.E7Sparse.quadP_eq_zero_of_quadZero
end AxiomAudit
