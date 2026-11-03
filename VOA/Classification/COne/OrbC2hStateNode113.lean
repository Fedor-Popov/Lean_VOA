import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode57
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node113_sector0 : RawPoly ℕ := []

def node113_sector1 : RawPoly ℕ := []

def node113_sector2 : RawPoly ℕ := []

def node113 : SectorVector := [(-2, node113_sector0), (0, node113_sector1), (2, node113_sector2)]
theorem node113_check : neutralDirectS JR (-18) node57 = node113 := by decide +kernel

theorem node113_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-18) (evaluate node57) = evaluate node113 :=
  neutralDirect_value JR (-18) node57 node113 node113_check

end VOA.Classification.COne.OrbC2h
