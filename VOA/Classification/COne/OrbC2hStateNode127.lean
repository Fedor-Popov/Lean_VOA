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
def node127_sector0 : RawPoly ℕ := []

def node127_sector1 : RawPoly ℕ := []

def node127_sector2 : RawPoly ℕ := []

def node127 : SectorVector := [(-2, node127_sector0), (0, node127_sector1), (2, node127_sector2)]
theorem node127_check : VectorCertificate (eLongS (17) nineData) node127 := by decide +kernel

theorem node127_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (17) (evaluate nineData) = evaluate node127 :=
  eLong_value (17) nineData node127 node127_check

end VOA.Classification.COne.OrbC2h
