import VOA.Classification.COne.OrbC2hDirectNeutral
import VOA.Classification.COne.OrbC2hBounded
import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hStateNode53
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node111_sector0 : RawPoly ℕ := []

def node111_sector1 : RawPoly ℕ := []

def node111_sector2 : RawPoly ℕ := []

def node111 : SectorVector := [(-2, node111_sector0), (0, node111_sector1), (2, node111_sector2)]
theorem node111_check : neutralDirectS JR (-17) node53 = node111 := by decide +kernel

theorem node111_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-17) (evaluate node53) = evaluate node111 :=
  neutralDirect_value JR (-17) node53 node111 node111_check

end VOA.Classification.COne.OrbC2h
