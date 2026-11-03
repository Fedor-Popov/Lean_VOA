import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode48
import VOA.Classification.COne.OrbC2hStateNode49
import VOA.Classification.COne.OrbC2hStateNode50
import VOA.Classification.COne.OrbC2hStateNode51
import VOA.Classification.COne.OrbC2hStateNode60
import VOA.Classification.COne.OrbC2hStateNode61
import VOA.Classification.COne.OrbC2hStateNode62
import VOA.Classification.COne.OrbC2hStateNode63
import VOA.Classification.COne.OrbC2hWeight20Step11
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term20_12_sector0 : RawPoly ℕ := []

def term20_12_sector1 : RawPoly ℕ := []

def term20_12_sector2 : RawPoly ℕ := []

def term20_12 : SectorVector := [(-2, term20_12_sector0), (0, term20_12_sector1), (2, term20_12_sector2)]
theorem term20_12_check : scaleVector 13 (zipMany 100000 [node51, scaleVector (-1) node62, scaleVector (-1) node50, node63]) = term20_12 := by decide +kernel

theorem term20_12_value : evaluate (iterateS (-3) 12 nineData) = evaluate term20_12 :=
  iterateS_sum_value (-3) 12 nineData node49 node60 node48 node61 node51 node62 node50 node63 term20_12
    node49_value node60_value node48_value node61_value node51_value node62_value node50_value node63_value (by
      have hq : ((12:ℕ):ℚ) + 1 = 13 := by norm_num
      rw [hq]
      exact term20_12_check)

end VOA.Classification.COne.OrbC2h
