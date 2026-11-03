import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode60
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node62_sector0 : RawPoly ℕ := []

def node62_sector1 : RawPoly ℕ := []

def node62_sector2 : RawPoly ℕ := []

def node62 : SectorVector := [(-2, node62_sector0), (0, node62_sector1), (2, node62_sector2)]
theorem node62_check : VectorCertificate (eMemoS (-17) node60) node62 := by decide +kernel

theorem node62_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-17) (evaluate node60) = evaluate node62 :=
  eMemo_value (-17) node60 node62 node62_check

end VOA.Classification.COne.OrbC2h
