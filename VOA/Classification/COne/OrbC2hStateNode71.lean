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
def node71_sector0 : RawPoly ℕ := []

def node71_sector1 : RawPoly ℕ := []

def node71_sector2 : RawPoly ℕ := []

def node71 : SectorVector := [(-2, node71_sector0), (0, node71_sector1), (2, node71_sector2)]
theorem node71_check : VectorCertificate (neutralBoundS JR (-19) node69) node71 := by decide +kernel

theorem node71_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-19) (evaluate node69) = evaluate node71 :=
  neutralBound_value JR (-19) node69 node71 node71_check

end VOA.Classification.COne.OrbC2h
