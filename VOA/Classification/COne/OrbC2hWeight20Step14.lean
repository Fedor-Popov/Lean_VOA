import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode56
import VOA.Classification.COne.OrbC2hStateNode57
import VOA.Classification.COne.OrbC2hStateNode58
import VOA.Classification.COne.OrbC2hStateNode59
import VOA.Classification.COne.OrbC2hStateNode68
import VOA.Classification.COne.OrbC2hStateNode69
import VOA.Classification.COne.OrbC2hStateNode70
import VOA.Classification.COne.OrbC2hStateNode71
import VOA.Classification.COne.OrbC2hWeight20Step13
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term20_14_sector0 : RawPoly ℕ := []

def term20_14_sector1 : RawPoly ℕ := []

def term20_14_sector2 : RawPoly ℕ := []

def term20_14 : SectorVector := [(-2, term20_14_sector0), (0, term20_14_sector1), (2, term20_14_sector2)]
theorem term20_14_check : scaleVector 15 (zipMany 100000 [node59, scaleVector (-1) node70, scaleVector (-1) node58, node71]) = term20_14 := by decide +kernel

theorem term20_14_value : evaluate (iterateS (-3) 14 nineData) = evaluate term20_14 :=
  iterateS_sum_value (-3) 14 nineData node57 node68 node56 node69 node59 node70 node58 node71 term20_14
    node57_value node68_value node56_value node69_value node59_value node70_value node58_value node71_value (by
      have hq : ((14:ℕ):ℚ) + 1 = 15 := by norm_num
      rw [hq]
      exact term20_14_check)

end VOA.Classification.COne.OrbC2h
