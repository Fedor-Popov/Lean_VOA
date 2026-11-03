/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import Mathlib

/-!
# Certified executable sparse rational polynomials

The mathematical carrier is a monoid algebra indexed by multisets.  Mathlib's `Finsupp`
constructors deliberately use classical equality, so this executable equivalent uses sorted
monomial lists and sorted association lists with zero coefficients removed.
-/

namespace VOA.SparseRational

abbrev RawPoly (ι : Type*) := List (ℚ × List ι)
abbrev Monomial (ι : Type*) := List ι
abbrev Poly (ι : Type*) := List (Monomial ι × ℚ)

/-- Fully structural insertion into a sorted monomial. -/
def insertVar [LinearOrder ι] (i : ι) : List ι → List ι
  | [] => [i]
  | j :: js => if i ≤ j then i :: j :: js else j :: insertVar i js

/-- Fully structural insertion sort; unlike the library merge sort this reduces in kernel
certificate checks. -/
def sortWord [LinearOrder ι] : List ι → Monomial ι
  | [] => []
  | i :: is => insertVar i (sortWord is)

theorem insertVar_perm [LinearOrder ι] (i : ι) : ∀ w : List ι,
    (insertVar i w).Perm (i :: w)
  | [] => by simp [insertVar]
  | j :: js => by
      by_cases hij : i ≤ j
      · simp [insertVar, hij]
      · simpa [insertVar, hij] using
          ((insertVar_perm i js).cons j).trans (List.Perm.swap i j js)

theorem sortWord_perm [LinearOrder ι] : ∀ w : List ι, (sortWord w).Perm w
  | [] => by simp [sortWord]
  | i :: is => (insertVar_perm i (sortWord is)).trans ((sortWord_perm is).cons i)

/-- Structural lexicographic comparison used by the certificate evaluator. -/
def compareWord [LinearOrder ι] : List ι → List ι → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | i :: is, j :: js =>
      if i < j then .lt else if j < i then .gt else compareWord is js

theorem compareWord_eq_iff [LinearOrder ι] : ∀ w v : List ι,
    compareWord w v = .eq ↔ w = v
  | [], [] => by simp [compareWord]
  | [], _ :: _ => by simp [compareWord]
  | _ :: _, [] => by simp [compareWord]
  | i :: is, j :: js => by
      by_cases hij : i < j
      · constructor
        · intro h
          simp [compareWord, hij] at h
        · intro h
          cases h
          exact (lt_irrefl i hij).elim
      · by_cases hji : j < i
        · constructor
          · intro h
            simp [compareWord, hij, hji] at h
          · intro h
            cases h
            exact (lt_irrefl i hji).elim
        · have heq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
          subst j
          simp [compareWord, compareWord_eq_iff is js]

def insertSorted [LinearOrder ι] (w : Monomial ι) (q : ℚ) : Poly ι → Poly ι
  | [] => if q = 0 then [] else [(w, q)]
  | (v, c) :: P =>
      if q = 0 then (v, c) :: P
      else match compareWord w v with
        | .lt => (w, q) :: (v, c) :: P
        | .gt => (v, c) :: insertSorted w q P
        | .eq => if q + c = 0 then P else (v, q + c) :: P

def insertQ [LinearOrder ι] (q : ℚ) (w : List ι) (P : Poly ι) : Poly ι :=
  insertSorted (sortWord w) q P

def normalizeQ [LinearOrder ι] : RawPoly ι → Poly ι
  | [] => []
  | (q, w) :: P => insertQ q w (normalizeQ P)

def toRaw (P : Poly ι) : RawPoly ι :=
  P.map fun t => (t.2, t.1)

def addQ [LinearOrder ι] : Poly ι → Poly ι → Poly ι
  | [], Q => Q
  | P, [] => P
  | (w, c) :: P, (v, d) :: Q =>
      match compareWord w v with
      | .lt => (w, c) :: addQ P ((v, d) :: Q)
      | .gt => (v, d) :: addQ ((w, c) :: P) Q
      | .eq =>
          if c + d = 0 then addQ P Q else (w, c + d) :: addQ P Q
termination_by P Q => P.length + Q.length
decreasing_by all_goals simp_wf <;> omega

@[simp] theorem addQ_nil_left [LinearOrder ι] (P : Poly ι) : addQ [] P = P := by
  simp [addQ]

@[simp] theorem addQ_nil_right [LinearOrder ι] (P : Poly ι) : addQ P [] = P := by
  cases P <;> simp [addQ]

def scaleQ [LinearOrder ι] (q : ℚ) (P : Poly ι) : Poly ι :=
  if q = 0 then [] else P.map fun t => (t.1, q * t.2)

def sumQ [LinearOrder ι] : List (Poly ι) → Poly ι
  | [] => []
  | P :: Ps => addQ P (sumQ Ps)

/-- Scaling by a nonzero rational commutes with the structural merge.  This is an
executable equality, not merely equality after evaluation, and lets large certificates
be checked branchwise before their final collection. -/
theorem scaleQ_addQ [LinearOrder ι] (q : ℚ) (hq : q ≠ 0) : ∀ P Q : Poly ι,
    scaleQ q (addQ P Q) = addQ (scaleQ q P) (scaleQ q Q)
  | [], Q => by simp [scaleQ, hq]
  | P, [] => by simp [scaleQ, hq]
  | (w, c) :: P, (v, d) :: Q => by
      rw [addQ]
      generalize hcmp : compareWord w v = cmp
      cases cmp with
      | lt =>
          simp only [scaleQ, if_neg hq, List.map_cons]
          simp only [addQ, hcmp]
          congr 1
          simpa [scaleQ, hq] using scaleQ_addQ q hq P ((v, d) :: Q)
      | gt =>
          simp only [scaleQ, if_neg hq, List.map_cons]
          simp only [addQ, hcmp]
          congr 1
          simpa [scaleQ, hq] using scaleQ_addQ q hq ((w, c) :: P) Q
      | eq =>
          by_cases hcd : c + d = 0
          · have hqcd : q * c + q * d = 0 := by
              rw [← mul_add, hcd, mul_zero]
            rw [if_pos hcd]
            simp only [scaleQ, if_neg hq, List.map_cons]
            simp only [addQ, hcmp, if_pos hqcd]
            simpa [scaleQ, hq] using scaleQ_addQ q hq P Q
          · have hqcd : q * c + q * d ≠ 0 := by
              rw [← mul_add]
              exact mul_ne_zero hq hcd
            rw [if_neg hcd]
            simp only [scaleQ, if_neg hq, List.map_cons]
            simp only [addQ, hcmp, if_neg hqcd]
            rw [show List.map (fun t => (t.1, q * t.2)) (addQ P Q) =
                addQ (List.map (fun t => (t.1, q * t.2)) P)
                  (List.map (fun t => (t.1, q * t.2)) Q) by
              simpa [scaleQ, hq] using scaleQ_addQ q hq P Q]
            congr 2
            ring
termination_by P Q => P.length + Q.length
decreasing_by all_goals simp_wf <;> omega

theorem scaleQ_sumQ [LinearOrder ι] (q : ℚ) (hq : q ≠ 0) : ∀ Ps : List (Poly ι),
    scaleQ q (sumQ Ps) = sumQ (Ps.map (scaleQ q))
  | [] => by simp [sumQ, scaleQ, hq]
  | P :: Ps => by
      rw [sumQ, scaleQ_addQ q hq, scaleQ_sumQ q hq Ps]
      rfl

def bindQ [LinearOrder ι] [LinearOrder κ]
    (P : Poly ι) (f : Monomial ι → ℚ → Poly κ) : Poly κ :=
  sumQ (P.map fun t => f t.1 t.2)

noncomputable def evalWord {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : ι → A) (w : List ι) : A :=
  (w.map x).prod

noncomputable def evalSparse {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : ι → A) (P : Poly ι) : A :=
  (P.map fun t => algebraMap ℚ A t.2 * evalWord x t.1).sum

noncomputable def evalRaw {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : ι → A) (P : RawPoly ι) : A :=
  (P.map fun t => algebraMap ℚ A t.1 * evalWord x t.2).sum

theorem evalWord_perm {A : Type*} [CommRing A] [Algebra ℚ A]
    (x : ι → A) {w v : List ι} (h : w.Perm v) :
    evalWord x w = evalWord x v := by
  simpa [evalWord] using (h.map x).prod_eq

theorem evalWord_sortWord [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) (w : List ι) :
    evalWord x (sortWord w) = evalWord x w :=
  evalWord_perm x (sortWord_perm w)

theorem evalSparse_insertSorted [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A)
    (w : Monomial ι) (q : ℚ) : ∀ P : Poly ι,
    evalSparse x (insertSorted w q P) =
      algebraMap ℚ A q * evalWord x w + evalSparse x P
  | [] => by
      by_cases hq : q = 0 <;> simp [insertSorted, hq, evalSparse]
  | (v, c) :: P => by
      by_cases hq : q = 0
      · simp [insertSorted, hq, evalSparse]
      · generalize hcmp : compareWord w v = cmp
        cases cmp with
        | lt => simp [insertSorted, hq, hcmp, evalSparse]
        | gt =>
            rw [insertSorted, if_neg hq, hcmp]
            change algebraMap ℚ A c * evalWord x v +
                evalSparse x (insertSorted w q P) =
              algebraMap ℚ A q * evalWord x w +
                (algebraMap ℚ A c * evalWord x v + evalSparse x P)
            rw [evalSparse_insertSorted]
            ring
        | eq =>
            have hwvEq : w = v := (compareWord_eq_iff w v).mp hcmp
            subst v
            by_cases hqc : q + c = 0
            · rw [insertSorted, if_neg hq, hcmp, if_pos hqc]
              change evalSparse x P =
                algebraMap ℚ A q * evalWord x w +
                  (algebraMap ℚ A c * evalWord x w + evalSparse x P)
              rw [← add_assoc, ← add_mul, ← map_add, hqc, map_zero,
                zero_mul, zero_add]
            · rw [insertSorted, if_neg hq, hcmp, if_neg hqc]
              change algebraMap ℚ A (q + c) * evalWord x w + evalSparse x P =
                algebraMap ℚ A q * evalWord x w +
                  (algebraMap ℚ A c * evalWord x w + evalSparse x P)
              rw [map_add]
              ring

theorem evalSparse_insertQ [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A)
    (q : ℚ) (w : List ι) (P : Poly ι) :
    evalSparse x (insertQ q w P) =
      algebraMap ℚ A q * evalWord x w + evalSparse x P := by
  rw [insertQ, evalSparse_insertSorted, evalWord_sortWord]

theorem evalSparse_normalizeQ [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) :
    ∀ P : RawPoly ι, evalSparse x (normalizeQ P) = evalRaw x P
  | [] => by simp [normalizeQ, evalSparse, evalRaw]
  | (q, w) :: P => by
      rw [normalizeQ, evalSparse_insertQ, evalSparse_normalizeQ x P]
      simp [evalRaw]

theorem evalRaw_toRaw [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) (P : Poly ι) :
    evalRaw x (toRaw P) = evalSparse x P := by
  unfold evalRaw evalSparse toRaw
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rcases t with ⟨w, q⟩
  rfl

theorem evalRaw_append
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) (P Q : RawPoly ι) :
    evalRaw x (P ++ Q) = evalRaw x P + evalRaw x Q := by
  simp [evalRaw, List.map_append, List.sum_append]

theorem evalRaw_scale
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) (q : ℚ) :
    ∀ P : RawPoly ι,
      evalRaw x (P.map fun t => (q * t.1, t.2)) =
        algebraMap ℚ A q * evalRaw x P
  | [] => by simp [evalRaw]
  | (c, w) :: P => by
      change algebraMap ℚ A (q * c) * evalWord x w +
          evalRaw x (P.map fun t => (q * t.1, t.2)) =
        algebraMap ℚ A q *
          (algebraMap ℚ A c * evalWord x w + evalRaw x P)
      rw [evalRaw_scale x q P]
      rw [map_mul]
      ring

theorem evalSparse_addQ [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) :
    ∀ P Q : Poly ι,
      evalSparse x (addQ P Q) = evalSparse x P + evalSparse x Q
  | [], Q => by simp [addQ, evalSparse]
  | (w, c) :: P, [] => by simp [addQ, evalSparse]
  | (w, c) :: P, (v, d) :: Q => by
      rw [addQ]
      generalize hcmp : compareWord w v = cmp
      cases cmp with
      | lt =>
          change algebraMap ℚ A c * evalWord x w +
              evalSparse x (addQ P ((v, d) :: Q)) =
            (algebraMap ℚ A c * evalWord x w + evalSparse x P) +
              (algebraMap ℚ A d * evalWord x v + evalSparse x Q)
          rw [evalSparse_addQ x P ((v, d) :: Q)]
          change _ + (evalSparse x P +
            (algebraMap ℚ A d * evalWord x v + evalSparse x Q)) = _
          ring
      | gt =>
          change algebraMap ℚ A d * evalWord x v +
              evalSparse x (addQ ((w, c) :: P) Q) =
            (algebraMap ℚ A c * evalWord x w + evalSparse x P) +
              (algebraMap ℚ A d * evalWord x v + evalSparse x Q)
          rw [evalSparse_addQ x ((w, c) :: P) Q]
          change _ + (algebraMap ℚ A c * evalWord x w + evalSparse x P +
            evalSparse x Q) = _
          ring
      | eq =>
          have hwv : w = v := (compareWord_eq_iff w v).mp hcmp
          subst v
          by_cases hcd : c + d = 0
          · rw [if_pos hcd, evalSparse_addQ x P Q]
            change evalSparse x P + evalSparse x Q =
              (algebraMap ℚ A c * evalWord x w + evalSparse x P) +
                (algebraMap ℚ A d * evalWord x w + evalSparse x Q)
            have hm : algebraMap ℚ A c + algebraMap ℚ A d = 0 := by
              rw [← map_add, hcd, map_zero]
            symm
            calc
              (algebraMap ℚ A c * evalWord x w + evalSparse x P) +
                  (algebraMap ℚ A d * evalWord x w + evalSparse x Q) =
                (algebraMap ℚ A c + algebraMap ℚ A d) * evalWord x w +
                  (evalSparse x P + evalSparse x Q) := by ring
              _ = evalSparse x P + evalSparse x Q := by rw [hm, zero_mul, zero_add]
          · rw [if_neg hcd]
            change algebraMap ℚ A (c + d) * evalWord x w +
                evalSparse x (addQ P Q) =
              (algebraMap ℚ A c * evalWord x w + evalSparse x P) +
                (algebraMap ℚ A d * evalWord x w + evalSparse x Q)
            rw [evalSparse_addQ x P Q, map_add]
            ring
termination_by P Q => P.length + Q.length
decreasing_by all_goals simp_wf <;> omega

theorem evalSparse_scaleQ [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) (q : ℚ) (P : Poly ι) :
    evalSparse x (scaleQ q P) = algebraMap ℚ A q * evalSparse x P := by
  by_cases hq : q = 0
  · simp [scaleQ, hq, evalSparse]
  · rw [scaleQ, if_neg hq]
    induction P with
    | nil => simp [evalSparse]
    | cons t P ih =>
        rcases t with ⟨w, c⟩
        change algebraMap ℚ A (q * c) * evalWord x w +
            evalSparse x (P.map fun t => (t.1, q * t.2)) =
          algebraMap ℚ A q *
            (algebraMap ℚ A c * evalWord x w + evalSparse x P)
        rw [ih, map_mul]
        ring

theorem evalSparse_sumQ [LinearOrder ι]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : ι → A) :
    ∀ Ps : List (Poly ι),
      evalSparse x (sumQ Ps) = (Ps.map (evalSparse x)).sum
  | [] => by simp [sumQ, evalSparse]
  | P :: Ps => by
      rw [sumQ, evalSparse_addQ, evalSparse_sumQ x Ps]
      rfl

theorem evalSparse_bindQ [LinearOrder ι] [LinearOrder κ]
    {A : Type*} [CommRing A] [Algebra ℚ A] (x : κ → A)
    (P : Poly ι) (f : Monomial ι → ℚ → Poly κ) :
    evalSparse x (bindQ P f) =
      (P.map fun t => evalSparse x (f t.1 t.2)).sum := by
  rw [bindQ, evalSparse_sumQ]
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  rcases t with ⟨w, q⟩
  rfl

example : normalizeQ (ι := ℕ) [(1, [1, 0]), (-1, [0, 1])] = [] := by
  norm_num [normalizeQ, insertQ, sortWord, insertVar, insertSorted, compareWord]

end VOA.SparseRational
