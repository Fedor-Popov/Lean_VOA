import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode52
import VOA.Classification.COne.OrbC2hStateNode53
import VOA.Classification.COne.OrbC2hStateNode54
import VOA.Classification.COne.OrbC2hStateNode55
import VOA.Classification.COne.OrbC2hStateNode64
import VOA.Classification.COne.OrbC2hStateNode65
import VOA.Classification.COne.OrbC2hStateNode66
import VOA.Classification.COne.OrbC2hStateNode67
import VOA.Classification.COne.OrbC2hWeight20Step12
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term20_13_sector0 : RawPoly ℕ := []

def term20_13_sector1 : RawPoly ℕ := []

def term20_13_sector2 : RawPoly ℕ := []

def term20_13 : SectorVector := [(-2, term20_13_sector0), (0, term20_13_sector1), (2, term20_13_sector2)]
theorem term20_13_check : scaleVector 14 (zipMany 100000 [node55, scaleVector (-1) node66, scaleVector (-1) node54, node67]) = term20_13 := by decide +kernel

theorem term20_13_value : evaluate (iterateS (-3) 13 nineData) = evaluate term20_13 :=
  iterateS_sum_value (-3) 13 nineData node53 node64 node52 node65 node55 node66 node54 node67 term20_13
    node53_value node64_value node52_value node65_value node55_value node66_value node54_value node67_value (by
      have hq : ((13:ℕ):ℚ) + 1 = 14 := by norm_num
      rw [hq]
      exact term20_13_check)

end VOA.Classification.COne.OrbC2h
