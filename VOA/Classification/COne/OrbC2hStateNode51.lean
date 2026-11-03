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
def node51_sector0 : RawPoly ℕ := []

def node51_sector1 : RawPoly ℕ := []

def node51_sector2 : RawPoly ℕ := []

def node51 : SectorVector := [(-2, node51_sector0), (0, node51_sector1), (2, node51_sector2)]
theorem node51_check : VectorCertificate (neutralBoundS JR (-14) node49) node51 := by decide +kernel

theorem node51_value : (V2m 4 four_ge_one).smul (ls 4 JR) (-14) (evaluate node49) = evaluate node51 :=
  neutralBound_value JR (-14) node49 node51 node51_check

end VOA.Classification.COne.OrbC2h
