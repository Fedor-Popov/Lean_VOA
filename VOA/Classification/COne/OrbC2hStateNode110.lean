import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode52
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node110_sector0 : RawPoly ℕ := []

def node110_sector1 : RawPoly ℕ := []

def node110_sector2 : RawPoly ℕ := []

def node110 : SectorVector := [(-2, node110_sector0), (0, node110_sector1), (2, node110_sector2)]
theorem node110_check : VectorCertificate (eLongS (-17) node52) node110 := by decide +kernel

theorem node110_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-17) (evaluate node52) = evaluate node110 :=
  eLong_value (-17) node52 node110 node110_check

end VOA.Classification.COne.OrbC2h
