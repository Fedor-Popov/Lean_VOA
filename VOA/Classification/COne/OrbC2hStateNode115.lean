import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode61
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node115_sector0 : RawPoly ℕ := []

def node115_sector1 : RawPoly ℕ := []

def node115_sector2 : RawPoly ℕ := []

def node115 : SectorVector := [(-2, node115_sector0), (0, node115_sector1), (2, node115_sector2)]
theorem node115_check : neutralDirectS JR (-19) node61 = node115 := by decide +kernel

theorem node115_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-19) (evaluate node61) = evaluate node115 :=
  neutralDirect_value JR (-19) node61 node115 node115_check

end VOA.Classification.COne.OrbC2h
