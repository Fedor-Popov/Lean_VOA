import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode48
import VOA.Classification.COne.OrbC2hStateNode49
import VOA.Classification.COne.OrbC2hStateNode68
import VOA.Classification.COne.OrbC2hStateNode69
import VOA.Classification.COne.OrbC2hStateNode108
import VOA.Classification.COne.OrbC2hStateNode109
import VOA.Classification.COne.OrbC2hStateNode118
import VOA.Classification.COne.OrbC2hStateNode119
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term22_14_sector0 : RawPoly ℕ := []

def term22_14_sector1 : RawPoly ℕ := []

def term22_14_sector2 : RawPoly ℕ := []

def term22_14 : SectorVector := [(-2, term22_14_sector0), (0, term22_14_sector1), (2, term22_14_sector2)]
theorem term22_14_check : scaleVector 15 (zipMany 100000 [node109, scaleVector (-1) node118, scaleVector (-1) node108, node119]) = term22_14 := by decide +kernel

theorem term22_14_value : evaluate (iterateS (-5) 14 nineData) = evaluate term22_14 :=
  iterateS_sum_value (-5) 14 nineData node49 node68 node48 node69 node109 node118 node108 node119 term22_14
    node49_value node68_value node48_value node69_value node109_value node118_value node108_value node119_value (by
      have hq : ((14:ℕ):ℚ) + 1 = 15 := by norm_num
      rw [hq]
      exact term22_14_check)

end VOA.Classification.COne.OrbC2h
