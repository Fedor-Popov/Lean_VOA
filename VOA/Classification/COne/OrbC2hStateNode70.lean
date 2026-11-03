import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hMemoSectors
import VOA.Classification.COne.OrbC2hStateNode68
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node70_sector0 : RawPoly ℕ := []

def node70_sector1 : RawPoly ℕ := []

def node70_sector2 : RawPoly ℕ := []

def node70 : SectorVector := [(-2, node70_sector0), (0, node70_sector1), (2, node70_sector2)]
theorem node70_check : VectorCertificate (eMemoS (-19) node68) node70 := by decide +kernel

theorem node70_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-19) (evaluate node68) = evaluate node70 :=
  eMemo_value (-19) node68 node70 node70_check

end VOA.Classification.COne.OrbC2h
