/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuSparseLhs3

/-! # Staged sparse check of the W(2) fourth Zhu power: list infrastructure -/

namespace VOA.LatGen.WpTwoZhuSparseLhs

open VOA.SparseRational
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute

def sumQWithTail :
    List (VOA.SparseRational.Poly ℕ) →
      VOA.SparseRational.Poly ℕ → VOA.SparseRational.Poly ℕ
  | [], tail => tail
  | P :: Ps, tail => addQ P (sumQWithTail Ps tail)

theorem sumQ_eq_sumQWithTail_take_drop (n : ℕ) :
    ∀ Ps : List (VOA.SparseRational.Poly ℕ),
      sumQ Ps = sumQWithTail (Ps.take n) (sumQ (Ps.drop n)) := by
  induction n with
  | zero =>
      intro Ps
      simp only [List.take_zero, List.drop_zero, sumQWithTail]
  | succ n ih =>
      intro Ps
      cases Ps with
      | nil => rfl
      | cons P Ps =>
          simp only [List.take_succ_cons, List.drop_succ_cons, sumQ, sumQWithTail]
          exact congrArg (addQ P) (ih Ps)

def omega4Terms : List (VOA.SparseRational.Poly ℕ) :=
  ((zhuOmegaPartsSparseQ 3).flatMap zhuOmegaPartSparseQ).map Prod.snd

theorem aFieldActSparseQ_empty (i : ℕ) (s : ℤ) :
    aFieldActSparseQ i s [] = [] := by
  rfl

theorem sumQ_replicate_empty : ∀ n,
    sumQ (List.replicate n ([] : VOA.SparseRational.Poly ℕ)) = [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change addQ [] (sumQ (List.replicate n [])) = []
      simpa only [addQ_nil_left] using ih

theorem sumQ_map_empty {A : Type} (xs : List A) :
    sumQ (xs.map (fun _ => ([] : VOA.SparseRational.Poly ℕ))) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change addQ [] (sumQ (xs.map fun _ => [])) = []
      simpa only [addQ_nil_left] using ih

theorem aWordActSparseQ_empty : ∀ word s w,
    aWordActSparseQ word s w [] = [] := by
  intro word
  induction word with
  | nil =>
      intro s w
      simp [aWordActSparseQ]
  | cons i is ih =>
      intro s w
      simp only [aWordActSparseQ]
      rw [sumSparseIcc]
      simp_rw [aFieldActSparseQ_empty]
      simp_rw [ih]
      simp_rw [aFieldActSparseQ_empty]
      simp only [ite_self]
      exact sumQ_map_empty _

theorem zhuOmegaPartSparseQ_empty (w : ℕ) :
    zhuOmegaPartSparseQ (w, []) = [(w + 2, []), (w + 1, []), (w, [])] := by
  simp [zhuOmegaPartSparseQ, voaModeActSparseQ, zhuStateActSparseQ,
    bindQ, scaleQ, aWordActSparseQ_empty, sumQ_replicate_empty]

/-- Each Zhu-omega step has exactly three children, so dropping nine children at power three
is definitionally the same as dropping three parents at power two. -/
theorem zhuOmegaPartsSparseQ_three_drop_nine :
    (zhuOmegaPartsSparseQ 3).drop 9 =
      ((zhuOmegaPartsSparseQ 2).drop 3).flatMap zhuOmegaPartSparseQ := by
  rfl

/-- The corresponding fixed-length drop identity after one more omega step and projection. -/
theorem omega4Terms_drop_twentySeven :
    omega4Terms.drop 27 =
      (((zhuOmegaPartsSparseQ 3).drop 9).flatMap zhuOmegaPartSparseQ).map Prod.snd := by
  rfl

end VOA.LatGen.WpTwoZhuSparseLhs
