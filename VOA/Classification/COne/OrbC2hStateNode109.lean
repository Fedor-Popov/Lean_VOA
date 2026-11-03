import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode49
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node109_sector0 : RawPoly ℕ := []

def node109_sector1 : RawPoly ℕ := []

def node109_sector2 : RawPoly ℕ := []

def node109 : SectorVector := [(-2, node109_sector0), (0, node109_sector1), (2, node109_sector2)]
theorem node109_check : neutralDirectS JR (-16) node49 = node109 := by decide +kernel

theorem node109_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-16) (evaluate node49) = evaluate node109 :=
  neutralDirect_value JR (-16) node49 node109 node109_check

end VOA.Classification.COne.OrbC2h
