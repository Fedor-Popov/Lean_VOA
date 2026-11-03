import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode127
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node129_sector0 : RawPoly ℕ := []

def node129_sector1 : RawPoly ℕ := []

def node129_sector2 : RawPoly ℕ := []

def node129 : SectorVector := [(-2, node129_sector0), (0, node129_sector1), (2, node129_sector2)]
theorem node129_check : neutralDirectS JR (-24) node127 = node129 := by decide +kernel

theorem node129_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-24) (evaluate node127) = evaluate node129 :=
  neutralDirect_value JR (-24) node127 node129 node129_check

end VOA.Classification.COne.OrbC2h
