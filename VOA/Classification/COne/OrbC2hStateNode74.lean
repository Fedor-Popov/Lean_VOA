import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode72
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node74_sector0 : RawPoly ℕ := []

def node74_sector1 : RawPoly ℕ := []

def node74_sector2 : RawPoly ℕ := []

def node74 : SectorVector := [(-2, node74_sector0), (0, node74_sector1), (2, node74_sector2)]
theorem node74_check : VectorCertificate (eMemoS (-20) node72) node74 := by decide +kernel

theorem node74_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-20) (evaluate node72) = evaluate node74 :=
  eMemo_value (-20) node72 node74 node74_check

end VOA.Classification.COne.OrbC2h
