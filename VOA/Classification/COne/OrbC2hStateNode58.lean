import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode56
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node58_sector0 : RawPoly ℕ := []

def node58_sector1 : RawPoly ℕ := []

def node58_sector2 : RawPoly ℕ := []

def node58 : SectorVector := [(-2, node58_sector0), (0, node58_sector1), (2, node58_sector2)]
theorem node58_check : VectorCertificate (eMemoS (-16) node56) node58 := by decide +kernel

theorem node58_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-16) (evaluate node56) = evaluate node58 :=
  eMemo_value (-16) node56 node58 node58_check

end VOA.Classification.COne.OrbC2h
