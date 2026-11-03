import VOA.Classification.COne.OrbC2hPieces
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2e OrbC2g LatMod

/-- Linearity with an independently proved output sum, allowing staged coefficients. -/
theorem mode_of_pieces_eval (u : LatModuleGen (latP 4)) (n : ℤ)
    (S T : SectorVector) (pieces : List (SectorVector × SectorVector))
    (hi : VectorCertificate (pieces.flatMap Prod.fst) S)
    (ho : evaluate (pieces.flatMap Prod.snd) = evaluate T)
    (h : ∀ p ∈ pieces, (V2m 4 four_ge_one).smul u n (evaluate p.1) = evaluate p.2) :
    (V2m 4 four_ge_one).smul u n (evaluate S) = evaluate T := by
  have aux (ps : List (SectorVector × SectorVector))
      (hp : ∀ p ∈ ps, (V2m 4 four_ge_one).smul u n (evaluate p.1) = evaluate p.2) :
      (V2m 4 four_ge_one).smul u n (evaluate (ps.flatMap Prod.fst)) =
        evaluate (ps.flatMap Prod.snd) := by
    induction ps with
    | nil => simp [evaluate, PreVertexAlgebra.smul_zero_right]
    | cons p ps ih =>
      simp only [List.flatMap_cons, evaluate_append, PreVertexAlgebra.smul_add_right]
      rw [hp p (by simp)]
      exact congrArg (evaluate p.2 + ·) (ih fun q hq => hp q (List.mem_cons_of_mem _ hq))
  rw [← vector_eq_of_certificate _ _ hi, aux pieces h, ho]

theorem evaluate_piece_outputs (ps : List (SectorVector × SectorVector)) :
    evaluate (ps.flatMap Prod.snd) = ((ps.map Prod.snd).map evaluate).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons, evaluate_append, List.map_cons, List.sum_cons, ih]
theorem evaluate_vector_list (ss : List SectorVector) :
    evaluate ss.flatten = (ss.map evaluate).sum := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [List.flatten_cons, evaluate_append, ih, List.map_cons, List.sum_cons]

def zipPairs : List SectorVector → List SectorVector
  | [] => []
  | [S] => [S]
  | S::T::ss => zipAdd S T :: zipPairs ss

def zipMany : ℕ → List SectorVector → SectorVector
  | 0, ss => ss.flatten
  | _+1, [] => []
  | _+1, [S] => S
  | n+1, S::T::ss => zipMany n (zipPairs (S::T::ss))

theorem evaluate_zipPairs (ss : List SectorVector) :
    ((zipPairs ss).map evaluate).sum = (ss.map evaluate).sum := by
  induction ss using zipPairs.induct with
  | case1 => rfl
  | case2 S => rfl
  | case3 S T ss ih =>
    simp only [zipPairs, List.map_cons, List.sum_cons, evaluate_zipAdd, ih]
    abel

theorem evaluate_zipMany (n : ℕ) (ss : List SectorVector) :
    evaluate (zipMany n ss) = (ss.map evaluate).sum := by
  induction n generalizing ss with
  | zero => exact evaluate_vector_list ss
  | succ n ih =>
    cases ss with
    | nil => simp [zipMany, evaluate]
    | cons S ss =>
      cases ss with
      | nil => simp [zipMany]
      | cons T ss => rw [zipMany, ih, evaluate_zipPairs]
end VOA.Classification.COne.OrbC2h
