import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node123_sector0 : RawPoly ℕ := []

def node123_sector1 : RawPoly ℕ := []

def node123_sector2 : RawPoly ℕ := []

def node123 : SectorVector := [(-2, node123_sector0), (0, node123_sector1), (2, node123_sector2)]
theorem node123_check : VectorCertificate (eLongS (16) nineData) node123 := by decide +kernel

theorem node123_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (16) (evaluate nineData) = evaluate node123 :=
  eLong_value (16) nineData node123 node123_check

end VOA.Classification.COne.OrbC2h
