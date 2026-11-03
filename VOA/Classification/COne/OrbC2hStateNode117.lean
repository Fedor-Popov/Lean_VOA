import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode65
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node117_sector0 : RawPoly ℕ := []

def node117_sector1 : RawPoly ℕ := []

def node117_sector2 : RawPoly ℕ := []

def node117 : SectorVector := [(-2, node117_sector0), (0, node117_sector1), (2, node117_sector2)]
theorem node117_check : neutralDirectS JR (-20) node65 = node117 := by decide +kernel

theorem node117_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-20) (evaluate node65) = evaluate node117 :=
  neutralDirect_value JR (-20) node65 node117 node117_check

end VOA.Classification.COne.OrbC2h
