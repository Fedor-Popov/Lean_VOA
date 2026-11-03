import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode52
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node54_sector0 : RawPoly ℕ := []

def node54_sector1 : RawPoly ℕ := []

def node54_sector2 : RawPoly ℕ := []

def node54 : SectorVector := [(-2, node54_sector0), (0, node54_sector1), (2, node54_sector2)]
theorem node54_check : VectorCertificate (eMemoS (-15) node52) node54 := by decide +kernel

theorem node54_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-15) (evaluate node52) = evaluate node54 :=
  eMemo_value (-15) node52 node54 node54_check

end VOA.Classification.COne.OrbC2h
