import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode60
import VOA.Classification.COne.OrbC2hStateNode61
import VOA.Classification.COne.OrbC2hStateNode62
import VOA.Classification.COne.OrbC2hStateNode63
import VOA.Classification.COne.OrbC2hStateNode72
import VOA.Classification.COne.OrbC2hStateNode73
import VOA.Classification.COne.OrbC2hStateNode74
import VOA.Classification.COne.OrbC2hStateNode75
import VOA.Classification.COne.OrbC2hWeight20Step14
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term20_15_sector0 : RawPoly ℕ := []

def term20_15_sector1 : RawPoly ℕ := []

def term20_15_sector2 : RawPoly ℕ := []

def term20_15 : SectorVector := [(-2, term20_15_sector0), (0, term20_15_sector1), (2, term20_15_sector2)]
theorem term20_15_check : scaleVector 16 (zipMany 100000 [node63, scaleVector (-1) node74, scaleVector (-1) node62, node75]) = term20_15 := by decide +kernel

theorem term20_15_value : evaluate (iterateS (-3) 15 nineData) = evaluate term20_15 :=
  iterateS_sum_value (-3) 15 nineData node61 node72 node60 node73 node63 node74 node62 node75 term20_15
    node61_value node72_value node60_value node73_value node63_value node74_value node62_value node75_value (by
      have hq : ((15:ℕ):ℚ) + 1 = 16 := by norm_num
      rw [hq]
      exact term20_15_check)

end VOA.Classification.COne.OrbC2h
