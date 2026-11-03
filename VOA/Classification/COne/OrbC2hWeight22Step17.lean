import VOA.Classification.COne.OrbC2hAssembleSum
import VOA.Classification.COne.OrbC2hStateNode60
import VOA.Classification.COne.OrbC2hStateNode61
import VOA.Classification.COne.OrbC2hStateNode114
import VOA.Classification.COne.OrbC2hStateNode115
import VOA.Classification.COne.OrbC2hStateNode126
import VOA.Classification.COne.OrbC2hStateNode127
import VOA.Classification.COne.OrbC2hStateNode128
import VOA.Classification.COne.OrbC2hStateNode129
set_option maxSynthPendingDepth 3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.style.longLine false
namespace VOA.Classification.COne.OrbC2h
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.SparseRational PlusC2Eval PlusUnitary
  PlusC2 OrbC2c OrbC2e OrbC2f OrbC2g LatMod
def term22_17_sector0 : RawPoly ℕ := []

def term22_17_sector1 : RawPoly ℕ := []

def term22_17_sector2 : RawPoly ℕ := []

def term22_17 : SectorVector := [(-2, term22_17_sector0), (0, term22_17_sector1), (2, term22_17_sector2)]
theorem term22_17_check : scaleVector 18 (zipMany 100000 [node115, scaleVector (-1) node128, scaleVector (-1) node114, node129]) = term22_17 := by decide +kernel

theorem term22_17_value : evaluate (iterateS (-5) 17 nineData) = evaluate term22_17 :=
  iterateS_sum_value (-5) 17 nineData node61 node126 node60 node127 node115 node128 node114 node129 term22_17
    node61_value node126_value node60_value node127_value node115_value node128_value node114_value node129_value (by
      have hq : ((17:ℕ):ℚ) + 1 = 18 := by norm_num
      rw [hq]
      exact term22_17_check)

end VOA.Classification.COne.OrbC2h
