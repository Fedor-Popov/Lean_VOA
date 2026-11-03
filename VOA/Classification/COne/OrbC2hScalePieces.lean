import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

/-- A scalar coefficient may be restored after certifying a monomial mode action. -/
theorem mode_of_scaled (u : LatModuleGen (latP 4)) (n : ℤ) (q : ℚ)
    (S T U V : SectorVector)
    (hS : scaleVector q S = U) (hT : scaleVector q T = V)
    (h : (V2m 4 four_ge_one).smul u n (evaluate S) = evaluate T) :
    (V2m 4 four_ge_one).smul u n (evaluate U) = evaluate V := by
  rw [← hS, ← hT, evaluate_scaleVector, evaluate_scaleVector,
    PreVertexAlgebra.smul_smul_right, h]
end VOA.Classification.COne.OrbC2h
