import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode72
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node120_sector0 : RawPoly ℕ := []

def node120_sector1 : RawPoly ℕ := []

def node120_sector2 : RawPoly ℕ := []

def node120 : SectorVector := [(-2, node120_sector0), (0, node120_sector1), (2, node120_sector2)]
theorem node120_check : VectorCertificate (eLongS (-22) node72) node120 := by decide +kernel

theorem node120_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-22) (evaluate node72) = evaluate node120 :=
  eLong_value (-22) node72 node120 node120_check

end VOA.Classification.COne.OrbC2h
