import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node126_sector0 : RawPoly ℕ := []

def node126_sector1 : RawPoly ℕ := []

def node126 : SectorVector := [(-1, node126_sector0), (1, node126_sector1)]
theorem node126_check : neutralDirectS JR (17) nineData = node126 := by decide +kernel

theorem node126_value : (V2m 4 four_ge_one).smul (ls 4 JR) (17) (evaluate nineData) = evaluate node126 :=
  neutralDirect_value JR (17) nineData node126 node126_check

end VOA.Classification.COne.OrbC2h
