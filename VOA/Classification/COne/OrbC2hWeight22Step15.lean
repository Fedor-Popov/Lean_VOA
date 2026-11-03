import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode52
import VOA.Classification.COne.OrbC2hStateNode53
import VOA.Classification.COne.OrbC2hStateNode72
import VOA.Classification.COne.OrbC2hStateNode73
import VOA.Classification.COne.OrbC2hStateNode110
import VOA.Classification.COne.OrbC2hStateNode111
import VOA.Classification.COne.OrbC2hStateNode120
import VOA.Classification.COne.OrbC2hStateNode121
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term22_15_sector0 : RawPoly ℕ := []

def term22_15_sector1 : RawPoly ℕ := []

def term22_15_sector2 : RawPoly ℕ := []

def term22_15 : SectorVector := [(-2, term22_15_sector0), (0, term22_15_sector1), (2, term22_15_sector2)]
theorem term22_15_check : scaleVector 16 (zipMany 100000 [node111, scaleVector (-1) node120, scaleVector (-1) node110, node121]) = term22_15 := by decide +kernel

theorem term22_15_value : evaluate (iterateS (-5) 15 nineData) = evaluate term22_15 :=
  iterateS_sum_value (-5) 15 nineData node53 node72 node52 node73 node111 node120 node110 node121 term22_15
    node53_value node72_value node52_value node73_value node111_value node120_value node110_value node121_value (by
      have hq : ((15:ℕ):ℚ) + 1 = 16 := by norm_num
      rw [hq]
      exact term22_15_check)

end VOA.Classification.COne.OrbC2h
