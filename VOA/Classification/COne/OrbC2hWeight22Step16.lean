import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode56
import VOA.Classification.COne.OrbC2hStateNode57
import VOA.Classification.COne.OrbC2hStateNode112
import VOA.Classification.COne.OrbC2hStateNode113
import VOA.Classification.COne.OrbC2hStateNode122
import VOA.Classification.COne.OrbC2hStateNode123
import VOA.Classification.COne.OrbC2hStateNode124
import VOA.Classification.COne.OrbC2hStateNode125
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term22_16_sector0 : RawPoly ℕ := []

def term22_16_sector1 : RawPoly ℕ := []

def term22_16_sector2 : RawPoly ℕ := []

def term22_16 : SectorVector := [(-2, term22_16_sector0), (0, term22_16_sector1), (2, term22_16_sector2)]
theorem term22_16_check : scaleVector 17 (zipMany 100000 [node113, scaleVector (-1) node124, scaleVector (-1) node112, node125]) = term22_16 := by decide +kernel

theorem term22_16_value : evaluate (iterateS (-5) 16 nineData) = evaluate term22_16 :=
  iterateS_sum_value (-5) 16 nineData node57 node122 node56 node123 node113 node124 node112 node125 term22_16
    node57_value node122_value node56_value node123_value node113_value node124_value node112_value node125_value (by
      have hq : ((16:ℕ):ℚ) + 1 = 17 := by norm_num
      rw [hq]
      exact term22_16_check)

end VOA.Classification.COne.OrbC2h
