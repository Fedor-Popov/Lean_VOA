import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode73
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node121_sector0 : RawPoly ℕ := []

def node121_sector1 : RawPoly ℕ := []

def node121_sector2 : RawPoly ℕ := []

def node121 : SectorVector := [(-2, node121_sector0), (0, node121_sector1), (2, node121_sector2)]
theorem node121_check : neutralDirectS JR (-22) node73 = node121 := by decide +kernel

theorem node121_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-22) (evaluate node73) = evaluate node121 :=
  neutralDirect_value JR (-22) node73 node121 node121_check

end VOA.Classification.COne.OrbC2h
