import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hNine
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node69_sector0 : RawPoly ℕ := []

def node69_sector1 : RawPoly ℕ := []

def node69_sector2 : RawPoly ℕ := []

def node69 : SectorVector := [(-2, node69_sector0), (0, node69_sector1), (2, node69_sector2)]
theorem node69_check : VectorCertificate (eMemoS (14) nineData) node69 := by decide +kernel

theorem node69_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (14) (evaluate nineData) = evaluate node69 :=
  eMemo_value (14) nineData node69 node69_check

end VOA.Classification.COne.OrbC2h
