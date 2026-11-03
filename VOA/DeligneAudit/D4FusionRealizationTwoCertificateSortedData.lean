/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCertificateData
import Mathlib.Data.List.Perm.Basic

/-! Sparse equality checking by sorting and a single grouped scan. -/
namespace VOA.DeligneAudit.D4Two.Certificate

def merge : ℕ → SV → SV → SV
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys =>
    if Nat.ble x.1 y.1 then x :: merge f xs (y :: ys) else y :: merge f (x :: xs) ys

theorem merge_perm (f : ℕ) (xs ys : SV) : (merge f xs ys).Perm (xs ++ ys) := by
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
def splitAux : SV → SV → SV → SV × SV
  | x :: y :: r, a, b => splitAux r (x :: a) (y :: b)
  | [x], a, b => (x :: a, b)
  | [], a, b => (a, b)

theorem splitAux_perm : ∀ (l a b : SV),
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

def msort : ℕ → SV → SV
  | 0, l => l
  | f + 1, l =>
    match l with
    | [] => []
    | [x] => [x]
    | l =>
      match splitAux l [] [] with
      | (a, b) => merge l.length (msort f a) (msort f b)

theorem msort_perm : ∀ (f : ℕ) (l : SV), (msort f l).Perm l
  | 0, l => by simp [msort]
  | f + 1, [] => by simp [msort]
  | f + 1, [x] => by simp [msort]
  | f + 1, x :: y :: r => by
    have hs := splitAux_perm (x :: y :: r) [] []
    simp only [List.append_nil] at hs
    simp only [msort]
    refine (merge_perm _ _ _).trans ?_
    exact ((msort_perm f _).append (msort_perm f _)).trans hs


def groupedZero : ℕ → ℤ → SV → Bool
  | _, a, [] => a == 0
  | i, a, p :: rest =>
      if p.1 = i then groupedZero i (a + p.2) rest
      else (a == 0) && groupedZero p.1 p.2 rest

def sortedZero (v : SV) : Bool :=
  match msort 40 v with
  | [] => true
  | p :: rest => groupedZero p.1 p.2 rest

end VOA.DeligneAudit.D4Two.Certificate
