import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode68
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node118_sector0 : RawPoly ℕ := []

def node118_sector1 : RawPoly ℕ := []

def node118_sector2 : RawPoly ℕ := []

def node118 : SectorVector := [(-2, node118_sector0), (0, node118_sector1), (2, node118_sector2)]
theorem node118_check : VectorCertificate (eLongS (-21) node68) node118 := by decide +kernel

theorem node118_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-21) (evaluate node68) = evaluate node118 :=
  eLong_value (-21) node68 node118 node118_check

end VOA.Classification.COne.OrbC2h
