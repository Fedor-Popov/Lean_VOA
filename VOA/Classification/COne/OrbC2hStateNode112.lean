import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode56
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node112_sector0 : RawPoly ℕ := []

def node112_sector1 : RawPoly ℕ := []

def node112_sector2 : RawPoly ℕ := []

def node112 : SectorVector := [(-2, node112_sector0), (0, node112_sector1), (2, node112_sector2)]
theorem node112_check : VectorCertificate (eLongS (-18) node56) node112 := by decide +kernel

theorem node112_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-18) (evaluate node56) = evaluate node112 :=
  eLong_value (-18) node56 node112 node112_check

end VOA.Classification.COne.OrbC2h
