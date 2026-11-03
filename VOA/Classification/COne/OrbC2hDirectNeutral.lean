import VOA.Classification.COne.OrbC2hDirectSectors
import VOA.Classification.COne.OrbC2hBounded
set_option maxSynthPendingDepth 3
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational HeisenbergN
  PlusC2Eval PlusUnitary PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod

def neutralDirectS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) : SectorVector :=
  reduceEach (neutralBoundS Q n S)

theorem evaluate_neutralDirectS (Q : RawPoly ℕ) (n : ℤ) (S : SectorVector) :
    evaluate (neutralDirectS Q n S) = (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) := by
  rw [neutralDirectS, evaluate_reduceEach, evaluate_neutralBoundS]

theorem neutralDirect_value (Q : RawPoly ℕ) (n : ℤ) (S T : SectorVector)
    (h : neutralDirectS Q n S = T) :
    (V2m 4 four_ge_one).smul (ls 4 Q) n (evaluate S) = evaluate T := by
  rw [← evaluate_neutralDirectS, h]
end VOA.Classification.COne.OrbC2h
