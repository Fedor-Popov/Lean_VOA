import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode64
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node66_sector0 : RawPoly ℕ := []

def node66_sector1 : RawPoly ℕ := []

def node66_sector2 : RawPoly ℕ := []

def node66 : SectorVector := [(-2, node66_sector0), (0, node66_sector1), (2, node66_sector2)]
theorem node66_check : VectorCertificate (eMemoS (-18) node64) node66 := by decide +kernel

theorem node66_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-18) (evaluate node64) = evaluate node66 :=
  eMemo_value (-18) node64 node66 node66_check

end VOA.Classification.COne.OrbC2h
