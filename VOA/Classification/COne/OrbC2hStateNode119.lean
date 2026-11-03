import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode69
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node119_sector0 : RawPoly ℕ := []

def node119_sector1 : RawPoly ℕ := []

def node119_sector2 : RawPoly ℕ := []

def node119 : SectorVector := [(-2, node119_sector0), (0, node119_sector1), (2, node119_sector2)]
theorem node119_check : neutralDirectS JR (-21) node69 = node119 := by decide +kernel

theorem node119_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-21) (evaluate node69) = evaluate node119 :=
  neutralDirect_value JR (-21) node69 node119 node119_check

end VOA.Classification.COne.OrbC2h
