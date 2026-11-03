import VOA.Classification.COne.OrbC2hAssemble
import VOA.Classification.COne.OrbC2hLongSectors
import VOA.Classification.COne.OrbC2hStateNode64
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def node116_sector0 : RawPoly ℕ := []

def node116_sector1 : RawPoly ℕ := []

def node116_sector2 : RawPoly ℕ := []

def node116 : SectorVector := [(-2, node116_sector0), (0, node116_sector1), (2, node116_sector2)]
theorem node116_check : VectorCertificate (eLongS (-20) node64) node116 := by decide +kernel

theorem node116_value : (V2m 4 four_ge_one).smul (EP 4 four_ge_one) (-20) (evaluate node64) = evaluate node116 :=
  eLong_value (-20) node64 node116 node116_check

end VOA.Classification.COne.OrbC2h
