import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode123
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node125_sector0 : RawPoly ℕ := []

def node125_sector1 : RawPoly ℕ := []

def node125_sector2 : RawPoly ℕ := []

def node125 : SectorVector := [(-2, node125_sector0), (0, node125_sector1), (2, node125_sector2)]
theorem node125_check : neutralDirectS JR (-23) node123 = node125 := by decide +kernel

theorem node125_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-23) (evaluate node123) = evaluate node125 :=
  neutralDirect_value JR (-23) node123 node125 node125_check

end VOA.Classification.COne.OrbC2h
