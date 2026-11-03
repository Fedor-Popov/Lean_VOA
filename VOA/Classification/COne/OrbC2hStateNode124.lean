import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode122
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node124_sector0 : RawPoly ℕ := []

def node124_sector1 : RawPoly ℕ := []

def node124_sector2 : RawPoly ℕ := []

def node124 : SectorVector := [(-2, node124_sector0), (0, node124_sector1), (2, node124_sector2)]
theorem node124_check : VectorCertificate (eLongS (-23) node122) node124 := by decide +kernel

theorem node124_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-23) (evaluate node122) = evaluate node124 :=
  eLong_value (-23) node122 node124 node124_check

end VOA.Classification.COne.OrbC2h
