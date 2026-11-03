import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode60
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node114_sector0 : RawPoly ℕ := []

def node114_sector1 : RawPoly ℕ := []

def node114_sector2 : RawPoly ℕ := []

def node114 : SectorVector := [(-2, node114_sector0), (0, node114_sector1), (2, node114_sector2)]
theorem node114_check : VectorCertificate (eLongS (-19) node60) node114 := by decide +kernel

theorem node114_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-19) (evaluate node60) = evaluate node114 :=
  eLong_value (-19) node60 node114 node114_check

end VOA.Classification.COne.OrbC2h
