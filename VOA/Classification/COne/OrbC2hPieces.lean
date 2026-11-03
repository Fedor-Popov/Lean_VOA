import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2e OrbC2g LatMod

/-- Linearity assembles independently certified complete mode images. -/
theorem mode_of_pieces (u : LatModuleGen (latP 4)) (n : ℤ)
    (S T : SectorVector) (pieces : List (SectorVector × SectorVector))
    (hi : VectorCertificate (pieces.flatMap Prod.fst) S)
    (ho : VectorCertificate (pieces.flatMap Prod.snd) T)
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
  rw [← vector_eq_of_certificate _ _ hi, ← vector_eq_of_certificate _ _ ho]
  exact aux pieces h

end VOA.Classification.COne.OrbC2h
