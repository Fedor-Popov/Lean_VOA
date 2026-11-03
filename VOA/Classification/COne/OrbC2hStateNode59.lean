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
def node59_sector0 : RawPoly ℕ := []

def node59_sector1 : RawPoly ℕ := []

def node59_sector2 : RawPoly ℕ := []

def node59 : SectorVector := [(-2, node59_sector0), (0, node59_sector1), (2, node59_sector2)]
theorem node59_check : VectorCertificate (neutralBoundS JR (-16) node57) node59 := by decide +kernel

theorem node59_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-16) (evaluate node57) = evaluate node59 :=
  neutralBound_value JR (-16) node57 node59 node59_check

end VOA.Classification.COne.OrbC2h
