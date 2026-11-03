import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode48
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node108_sector0 : RawPoly ℕ := []

def node108_sector1 : RawPoly ℕ := []

def node108_sector2 : RawPoly ℕ := []

def node108 : SectorVector := [(-2, node108_sector0), (0, node108_sector1), (2, node108_sector2)]
theorem node108_check : VectorCertificate (eLongS (-16) node48) node108 := by decide +kernel

theorem node108_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-16) (evaluate node48) = evaluate node108 :=
  eLong_value (-16) node48 node108 node108_check

end VOA.Classification.COne.OrbC2h
