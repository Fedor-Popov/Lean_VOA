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
def node49_sector0 : RawPoly ℕ := []

def node49_sector1 : RawPoly ℕ := []

def node49_sector2 : RawPoly ℕ := []

def node49 : SectorVector := [(-2, node49_sector0), (0, node49_sector1), (2, node49_sector2)]
theorem node49_check : VectorCertificate (eMemoS (9) nineData) node49 := by decide +kernel

theorem node49_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (9) (evaluate nineData) = evaluate node49 :=
  eMemo_value (9) nineData node49 node49_check

end VOA.Classification.COne.OrbC2h
