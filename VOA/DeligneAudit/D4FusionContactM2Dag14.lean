import VOA.DeligneAudit.D4FusionContactM2Dag13

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node5058 : WordRow := [([2, 5, 14, 14], 1), ([2, 8, 13, 14], 1), ([2, 9, 12, 14], 1), ([3, 4, 14, 14], -1), ([4, 8, 11, 14], -1), ([4, 9, 10, 14], -1)]

def node5058Raw : WordRow := multiplyRow 14 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5058_check :
    collect (scaleRow 1 node5058Raw ++ scaleRow (-(1 : ℤ)) node5058 ++
      ([])) = [] := by
  decide +kernel

theorem node5058_mem : rowEval varIndex node5058 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5058Raw node5058 ([])
    (1) (1) (by decide) node5058_check
  · rw [node5058Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · exact candidateIdeal.zero_mem

def node5060 : WordRow := [([2, 5, 14, 16], 1), ([2, 8, 13, 16], 1), ([2, 9, 12, 16], 1), ([3, 4, 14, 16], -1), ([4, 8, 11, 16], -1), ([4, 9, 10, 16], -1)]

def node5060Raw : WordRow := multiplyRow 16 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5060_check :
    collect (scaleRow 1 node5060Raw ++ scaleRow (-(1 : ℤ)) node5060 ++
      ([])) = [] := by
  decide +kernel

theorem node5060_mem : rowEval varIndex node5060 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5060Raw node5060 ([])
    (1) (1) (by decide) node5060_check
  · rw [node5060Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · exact candidateIdeal.zero_mem

def node5061 : WordRow := [([2, 5, 14, 17], 1), ([2, 8, 13, 17], 1), ([2, 9, 12, 17], 1), ([3, 4, 14, 17], -1), ([4, 8, 11, 17], -1), ([4, 9, 10, 17], -1)]

def node5061Raw : WordRow := multiplyRow 17 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5061_check :
    collect (scaleRow 1 node5061Raw ++ scaleRow (-(1 : ℤ)) node5061 ++
      ([])) = [] := by
  decide +kernel

theorem node5061_mem : rowEval varIndex node5061 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5061Raw node5061 ([])
    (1) (1) (by decide) node5061_check
  · rw [node5061Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · exact candidateIdeal.zero_mem

def node5062 : WordRow := [([4, 4, 11, 15], 1), ([4, 5, 10, 15], 1), ([4, 5, 11, 14], 2), ([4, 6, 9, 15], 1), ([4, 7, 8, 15], 1), ([4, 7, 9, 14], 1), ([4, 9, 10, 13], -1), ([4, 9, 11, 12], 1), ([5, 5, 10, 14], 2), ([5, 6, 9, 14], 3), ([5, 7, 8, 14], 2), ([5, 8, 10, 13], 1), ([5, 8, 11, 12], -1), ([6, 8, 9, 13], 1), ([6, 9, 9, 12], 1), ([7, 8, 8, 13], 1), ([7, 8, 9, 12], 1)]

def node5062Raw : WordRow := multiplyRow 12 node0626

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5062_check :
    collect (scaleRow 2 node5062Raw ++ scaleRow (-(-2 : ℤ)) node5062 ++
      (scaleRow (-1) node5046 ++ scaleRow (-1) node5057)) = [] := by
  decide +kernel

theorem node5062_mem : rowEval varIndex node5062 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5062Raw node5062 (scaleRow (-1) node5046 ++ scaleRow (-1) node5057)
    (2) (-2) (by decide) node5062_check
  · rw [node5062Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0626_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5046 node5046_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5057 node5057_mem))

def node5071 : WordRow := [([4, 4, 10, 15], 1), ([4, 5, 10, 14], 1), ([4, 8, 10, 13], 1), ([4, 9, 10, 12], 1)]

def node5071Raw : WordRow := multiplyRow 10 node0627

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5071_check :
    collect (scaleRow 1 node5071Raw ++ scaleRow (-(1 : ℤ)) node5071 ++
      ([])) = [] := by
  decide +kernel

theorem node5071_mem : rowEval varIndex node5071 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5071Raw node5071 ([])
    (1) (1) (by decide) node5071_check
  · rw [node5071Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0627_mem
  · exact candidateIdeal.zero_mem

def node5072 : WordRow := [([4, 7, 8, 15], 1), ([4, 7, 9, 14], 1), ([4, 8, 11, 13], -1), ([4, 9, 10, 13], -1), ([5, 5, 10, 14], 2), ([5, 6, 8, 15], -1), ([5, 6, 9, 14], 3), ([5, 7, 8, 14], 2), ([5, 8, 10, 13], 1), ([5, 8, 11, 12], -1), ([6, 8, 9, 13], 1), ([6, 9, 9, 12], 1), ([7, 8, 8, 13], 1), ([7, 8, 9, 12], 1)]

def node5072Raw : WordRow := multiplyRow 11 node0627

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5072_check :
    collect (scaleRow 1 node5072Raw ++ scaleRow (-(-1 : ℤ)) node5072 ++
      (scaleRow (-1) node5062 ++ scaleRow (1) node2815 ++ scaleRow (1) node2821 ++ scaleRow (1) node3800)) = [] := by
  decide +kernel

theorem node5072_mem : rowEval varIndex node5072 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5072Raw node5072 (scaleRow (-1) node5062 ++ scaleRow (1) node2815 ++ scaleRow (1) node2821 ++ scaleRow (1) node3800)
    (1) (-1) (by decide) node5072_check
  · rw [node5072Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0627_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5062 node5062_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node2815 node2815_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node2821 node2821_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3800 node3800_mem))))

def node5076 : WordRow := [([4, 4, 15, 16], 1), ([4, 5, 14, 16], 1), ([4, 8, 13, 16], 1), ([4, 9, 12, 16], 1)]

def node5076Raw : WordRow := multiplyRow 16 node0627

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5076_check :
    collect (scaleRow 1 node5076Raw ++ scaleRow (-(1 : ℤ)) node5076 ++
      ([])) = [] := by
  decide +kernel

theorem node5076_mem : rowEval varIndex node5076 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5076Raw node5076 ([])
    (1) (1) (by decide) node5076_check
  · rw [node5076Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0627_mem
  · exact candidateIdeal.zero_mem

def node5079 : WordRow := [([4, 6, 8, 15], 1), ([5, 6, 8, 14], 1), ([6, 8, 8, 13], 1), ([6, 8, 9, 12], 1)]

def node5079Raw : WordRow := multiplyRow 8 node0628

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5079_check :
    collect (scaleRow 1 node5079Raw ++ scaleRow (-(1 : ℤ)) node5079 ++
      ([])) = [] := by
  decide +kernel

theorem node5079_mem : rowEval varIndex node5079 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5079Raw node5079 ([])
    (1) (1) (by decide) node5079_check
  · rw [node5079Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0628_mem
  · exact candidateIdeal.zero_mem

def node5080 : WordRow := [([5, 6, 8, 15], 1), ([5, 6, 9, 14], -1), ([6, 8, 9, 13], -1), ([6, 9, 9, 12], -1)]

def node5080Raw : WordRow := multiplyRow 9 node0628

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5080_check :
    collect (scaleRow 1 node5080Raw ++ scaleRow (-(-1 : ℤ)) node5080 ++
      (scaleRow (-1) node3800)) = [] := by
  decide +kernel

theorem node5080_mem : rowEval varIndex node5080 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5080Raw node5080 (scaleRow (-1) node3800)
    (1) (-1) (by decide) node5080_check
  · rw [node5080Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0628_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node3800 node3800_mem)

def node5081 : WordRow := [([4, 6, 10, 15], 1), ([5, 6, 10, 14], 1), ([6, 8, 10, 13], 1), ([6, 9, 10, 12], 1)]

def node5081Raw : WordRow := multiplyRow 10 node0628

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5081_check :
    collect (scaleRow 1 node5081Raw ++ scaleRow (-(1 : ℤ)) node5081 ++
      ([])) = [] := by
  decide +kernel

theorem node5081_mem : rowEval varIndex node5081 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5081Raw node5081 ([])
    (1) (1) (by decide) node5081_check
  · rw [node5081Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0628_mem
  · exact candidateIdeal.zero_mem

def node5085 : WordRow := [([4, 6, 14, 15], 1), ([5, 6, 14, 14], 1), ([6, 8, 13, 14], 1), ([6, 9, 12, 14], 1)]

def node5085Raw : WordRow := multiplyRow 14 node0628

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5085_check :
    collect (scaleRow 1 node5085Raw ++ scaleRow (-(1 : ℤ)) node5085 ++
      ([])) = [] := by
  decide +kernel

theorem node5085_mem : rowEval varIndex node5085 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5085Raw node5085 ([])
    (1) (1) (by decide) node5085_check
  · rw [node5085Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0628_mem
  · exact candidateIdeal.zero_mem

def node5087 : WordRow := [([4, 6, 15, 16], 1), ([5, 6, 14, 16], 1), ([6, 8, 13, 16], 1), ([6, 9, 12, 16], 1)]

def node5087Raw : WordRow := multiplyRow 16 node0628

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5087_check :
    collect (scaleRow 1 node5087Raw ++ scaleRow (-(1 : ℤ)) node5087 ++
      ([])) = [] := by
  decide +kernel

theorem node5087_mem : rowEval varIndex node5087 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5087Raw node5087 ([])
    (1) (1) (by decide) node5087_check
  · rw [node5087Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0628_mem
  · exact candidateIdeal.zero_mem

def node5094 : WordRow := [([4, 8, 10, 15], 1), ([5, 8, 10, 14], 1), ([8, 8, 10, 13], 1), ([8, 9, 10, 12], 1)]

def node5094Raw : WordRow := multiplyRow 10 node0630

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5094_check :
    collect (scaleRow 1 node5094Raw ++ scaleRow (-(1 : ℤ)) node5094 ++
      ([])) = [] := by
  decide +kernel

theorem node5094_mem : rowEval varIndex node5094 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5094Raw node5094 ([])
    (1) (1) (by decide) node5094_check
  · rw [node5094Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0630_mem
  · exact candidateIdeal.zero_mem

def node5100 : WordRow := [([4, 8, 15, 16], 1), ([5, 8, 14, 16], 1), ([8, 8, 13, 16], 1), ([8, 9, 12, 16], 1)]

def node5100Raw : WordRow := multiplyRow 16 node0630

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5100_check :
    collect (scaleRow 1 node5100Raw ++ scaleRow (-(1 : ℤ)) node5100 ++
      ([])) = [] := by
  decide +kernel

theorem node5100_mem : rowEval varIndex node5100 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5100Raw node5100 ([])
    (1) (1) (by decide) node5100_check
  · rw [node5100Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0630_mem
  · exact candidateIdeal.zero_mem

def node5107 : WordRow := [([4, 10, 10, 15], 1), ([5, 10, 10, 14], 1), ([8, 10, 10, 13], 1), ([9, 10, 10, 12], 1)]

def node5107Raw : WordRow := multiplyRow 10 node0632

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5107_check :
    collect (scaleRow 1 node5107Raw ++ scaleRow (-(1 : ℤ)) node5107 ++
      ([])) = [] := by
  decide +kernel

theorem node5107_mem : rowEval varIndex node5107 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5107Raw node5107 ([])
    (1) (1) (by decide) node5107_check
  · rw [node5107Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0632_mem
  · exact candidateIdeal.zero_mem

def node5108 : WordRow := [([4, 10, 12, 15], 1), ([5, 10, 12, 14], 1), ([8, 10, 12, 13], 1), ([9, 10, 12, 12], 1)]

def node5108Raw : WordRow := multiplyRow 12 node0632

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5108_check :
    collect (scaleRow 1 node5108Raw ++ scaleRow (-(1 : ℤ)) node5108 ++
      ([])) = [] := by
  decide +kernel

theorem node5108_mem : rowEval varIndex node5108 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5108Raw node5108 ([])
    (1) (1) (by decide) node5108_check
  · rw [node5108Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0632_mem
  · exact candidateIdeal.zero_mem

def node5109 : WordRow := [([5, 10, 12, 15], 1), ([5, 10, 13, 14], -1), ([8, 10, 13, 13], -1), ([9, 10, 12, 13], -1)]

def node5109Raw : WordRow := multiplyRow 13 node0632

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5109_check :
    collect (scaleRow 1 node5109Raw ++ scaleRow (-(-1 : ℤ)) node5109 ++
      (scaleRow (-1) node4388)) = [] := by
  decide +kernel

theorem node5109_mem : rowEval varIndex node5109 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5109Raw node5109 (scaleRow (-1) node4388)
    (1) (-1) (by decide) node5109_check
  · rw [node5109Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0632_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4388 node4388_mem)

def node5110 : WordRow := [([4, 10, 14, 15], 1), ([5, 10, 14, 14], 1), ([8, 10, 13, 14], 1), ([9, 10, 12, 14], 1)]

def node5110Raw : WordRow := multiplyRow 14 node0632

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5110_check :
    collect (scaleRow 1 node5110Raw ++ scaleRow (-(1 : ℤ)) node5110 ++
      ([])) = [] := by
  decide +kernel

theorem node5110_mem : rowEval varIndex node5110 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5110Raw node5110 ([])
    (1) (1) (by decide) node5110_check
  · rw [node5110Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0632_mem
  · exact candidateIdeal.zero_mem

def node5112 : WordRow := [([4, 10, 15, 16], 1), ([5, 10, 14, 16], 1), ([8, 10, 13, 16], 1), ([9, 10, 12, 16], 1)]

def node5112Raw : WordRow := multiplyRow 16 node0632

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5112_check :
    collect (scaleRow 1 node5112Raw ++ scaleRow (-(1 : ℤ)) node5112 ++
      ([])) = [] := by
  decide +kernel

theorem node5112_mem : rowEval varIndex node5112 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5112Raw node5112 ([])
    (1) (1) (by decide) node5112_check
  · rw [node5112Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0632_mem
  · exact candidateIdeal.zero_mem

def node5124 : WordRow := [([4, 12, 15, 16], 1), ([5, 12, 14, 16], 1), ([8, 12, 13, 16], 1), ([9, 12, 12, 16], 1)]

def node5124Raw : WordRow := multiplyRow 16 node0634

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5124_check :
    collect (scaleRow 1 node5124Raw ++ scaleRow (-(1 : ℤ)) node5124 ++
      ([])) = [] := by
  decide +kernel

theorem node5124_mem : rowEval varIndex node5124 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5124Raw node5124 ([])
    (1) (1) (by decide) node5124_check
  · rw [node5124Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0634_mem
  · exact candidateIdeal.zero_mem

def node5133 : WordRow := [([4, 14, 15, 16], 1), ([5, 14, 14, 16], 1), ([8, 13, 14, 16], 1), ([9, 12, 14, 16], 1)]

def node5133Raw : WordRow := multiplyRow 16 node0636

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5133_check :
    collect (scaleRow 1 node5133Raw ++ scaleRow (-(1 : ℤ)) node5133 ++
      ([])) = [] := by
  decide +kernel

theorem node5133_mem : rowEval varIndex node5133 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5133Raw node5133 ([])
    (1) (1) (by decide) node5133_check
  · rw [node5133Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0636_mem
  · exact candidateIdeal.zero_mem

def node5139 : WordRow := [([4, 15, 16, 17], 1), ([5, 14, 16, 17], 1), ([8, 13, 16, 17], 1), ([9, 12, 16, 17], 1)]

def node5139Raw : WordRow := multiplyRow 17 node0638

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5139_check :
    collect (scaleRow 1 node5139Raw ++ scaleRow (-(1 : ℤ)) node5139 ++
      ([])) = [] := by
  decide +kernel

theorem node5139_mem : rowEval varIndex node5139 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5139Raw node5139 ([])
    (1) (1) (by decide) node5139_check
  · rw [node5139Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0638_mem
  · exact candidateIdeal.zero_mem

def node5154 : WordRow := [([8, 10, 13, 13], 1), ([9, 10, 12, 13], 2)]

def node5154Raw : WordRow := multiplyRow 12 node0642

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5154_check :
    collect (scaleRow 1 node5154Raw ++ scaleRow (-(1 : ℤ)) node5154 ++
      (scaleRow (-1) node5109 ++ scaleRow (-1) node4437)) = [] := by
  decide +kernel

theorem node5154_mem : rowEval varIndex node5154 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5154Raw node5154 (scaleRow (-1) node5109 ++ scaleRow (-1) node4437)
    (1) (1) (by decide) node5154_check
  · rw [node5154Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0642_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5109 node5109_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4437 node4437_mem))

def node5186 : WordRow := [([1, 6, 8, 14], 2), ([1, 8, 10, 12], 2), ([2, 6, 8, 13], -1), ([2, 7, 8, 12], -1), ([3, 6, 8, 12], -2), ([4, 6, 8, 11], -1), ([4, 7, 8, 10], -1), ([5, 6, 8, 10], -2), ([6, 6, 8, 9], -1), ([6, 7, 8, 8], -1)]

def node5186Raw : WordRow := multiplyRow 8 node0650

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5186_check :
    collect (scaleRow 1 node5186Raw ++ scaleRow (-(1 : ℤ)) node5186 ++
      ([])) = [] := by
  decide +kernel

theorem node5186_mem : rowEval varIndex node5186 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5186Raw node5186 ([])
    (1) (1) (by decide) node5186_check
  · rw [node5186Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0650_mem
  · exact candidateIdeal.zero_mem

def node5187 : WordRow := [([3, 5, 10, 12], 2), ([3, 6, 8, 13], -1), ([3, 6, 9, 12], -6), ([3, 7, 8, 12], 1), ([4, 4, 11, 11], -2), ([4, 5, 10, 11], -2), ([4, 6, 9, 11], -3), ([4, 7, 8, 11], -4), ([4, 7, 9, 10], -3), ([5, 6, 9, 10], -2), ([5, 7, 8, 10], 2), ([6, 6, 9, 9], -1), ([6, 7, 8, 9], -1)]

def node5187Raw : WordRow := multiplyRow 9 node0650

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5187_check :
    collect (scaleRow 1 node5187Raw ++ scaleRow (-(1 : ℤ)) node5187 ++
      (scaleRow (-2) node2320 ++ scaleRow (-2) node1915 ++ scaleRow (-2) node2450 ++ scaleRow (2) node2414 ++ scaleRow (1) node3410 ++ scaleRow (1) node3419 ++ scaleRow (-2) node5052)) = [] := by
  decide +kernel

theorem node5187_mem : rowEval varIndex node5187 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5187Raw node5187 (scaleRow (-2) node2320 ++ scaleRow (-2) node1915 ++ scaleRow (-2) node2450 ++ scaleRow (2) node2414 ++ scaleRow (1) node3410 ++ scaleRow (1) node3419 ++ scaleRow (-2) node5052)
    (1) (1) (by decide) node5187_check
  · rw [node5187Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0650_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2320 node2320_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1915 node1915_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2450 node2450_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2414 node2414_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3410 node3410_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3419 node3419_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5052 node5052_mem)))))))

def node5190 : WordRow := [([1, 6, 14, 14], 2), ([1, 10, 12, 14], 2), ([2, 6, 13, 14], -1), ([2, 7, 12, 14], -1), ([3, 6, 12, 14], -2), ([4, 6, 11, 14], -1), ([4, 7, 10, 14], -1), ([5, 6, 10, 14], -2), ([6, 6, 9, 14], -1), ([6, 7, 8, 14], -1)]

def node5190Raw : WordRow := multiplyRow 14 node0650

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5190_check :
    collect (scaleRow 1 node5190Raw ++ scaleRow (-(1 : ℤ)) node5190 ++
      ([])) = [] := by
  decide +kernel

theorem node5190_mem : rowEval varIndex node5190 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5190Raw node5190 ([])
    (1) (1) (by decide) node5190_check
  · rw [node5190Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0650_mem
  · exact candidateIdeal.zero_mem

def node5192 : WordRow := [([1, 6, 14, 16], 2), ([1, 10, 12, 16], 2), ([2, 6, 13, 16], -1), ([2, 7, 12, 16], -1), ([3, 6, 12, 16], -2), ([4, 6, 11, 16], -1), ([4, 7, 10, 16], -1), ([5, 6, 10, 16], -2), ([6, 6, 9, 16], -1), ([6, 7, 8, 16], -1)]

def node5192Raw : WordRow := multiplyRow 16 node0650

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5192_check :
    collect (scaleRow 1 node5192Raw ++ scaleRow (-(1 : ℤ)) node5192 ++
      ([])) = [] := by
  decide +kernel

theorem node5192_mem : rowEval varIndex node5192 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5192Raw node5192 ([])
    (1) (1) (by decide) node5192_check
  · rw [node5192Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0650_mem
  · exact candidateIdeal.zero_mem

def node5195 : WordRow := [([2, 4, 7, 14], 1), ([2, 4, 10, 13], 1), ([2, 4, 11, 12], 1), ([3, 4, 6, 14], -1), ([4, 6, 8, 11], -1), ([4, 6, 9, 10], -1)]

def node5195Raw : WordRow := multiplyRow 4 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5195_check :
    collect (scaleRow 1 node5195Raw ++ scaleRow (-(1 : ℤ)) node5195 ++
      ([])) = [] := by
  decide +kernel

theorem node5195_mem : rowEval varIndex node5195 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5195Raw node5195 ([])
    (1) (1) (by decide) node5195_check
  · rw [node5195Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · exact candidateIdeal.zero_mem

def node5198 : WordRow := [([3, 7, 8, 14], 1), ([3, 8, 10, 13], 1), ([3, 8, 11, 12], 1), ([6, 8, 9, 11], 1), ([6, 9, 9, 10], 1)]

def node5198Raw : WordRow := multiplyRow 9 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5198_check :
    collect (scaleRow 1 node5198Raw ++ scaleRow (-(-1 : ℤ)) node5198 ++
      (scaleRow (-1) node3421 ++ scaleRow (-1) node3447 ++ scaleRow (-1) node3453 ++ scaleRow (1) node3509)) = [] := by
  decide +kernel

theorem node5198_mem : rowEval varIndex node5198 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5198Raw node5198 (scaleRow (-1) node3421 ++ scaleRow (-1) node3447 ++ scaleRow (-1) node3453 ++ scaleRow (1) node3509)
    (1) (-1) (by decide) node5198_check
  · rw [node5198Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3421 node3421_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3447 node3447_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3453 node3453_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3509 node3509_mem))))

def node5200 : WordRow := [([2, 7, 12, 14], 1), ([2, 10, 12, 13], 1), ([2, 11, 12, 12], 1), ([3, 6, 12, 14], -1), ([6, 8, 11, 12], -1), ([6, 9, 10, 12], -1)]

def node5200Raw : WordRow := multiplyRow 12 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5200_check :
    collect (scaleRow 1 node5200Raw ++ scaleRow (-(1 : ℤ)) node5200 ++
      ([])) = [] := by
  decide +kernel

theorem node5200_mem : rowEval varIndex node5200 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5200Raw node5200 ([])
    (1) (1) (by decide) node5200_check
  · rw [node5200Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · exact candidateIdeal.zero_mem

def node5202 : WordRow := [([2, 7, 14, 14], 1), ([2, 10, 13, 14], 1), ([2, 11, 12, 14], 1), ([3, 6, 14, 14], -1), ([6, 8, 11, 14], -1), ([6, 9, 10, 14], -1)]

def node5202Raw : WordRow := multiplyRow 14 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5202_check :
    collect (scaleRow 1 node5202Raw ++ scaleRow (-(1 : ℤ)) node5202 ++
      ([])) = [] := by
  decide +kernel

theorem node5202_mem : rowEval varIndex node5202 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5202Raw node5202 ([])
    (1) (1) (by decide) node5202_check
  · rw [node5202Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · exact candidateIdeal.zero_mem

def node5204 : WordRow := [([2, 7, 14, 16], 1), ([2, 10, 13, 16], 1), ([2, 11, 12, 16], 1), ([3, 6, 14, 16], -1), ([6, 8, 11, 16], -1), ([6, 9, 10, 16], -1)]

def node5204Raw : WordRow := multiplyRow 16 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5204_check :
    collect (scaleRow 1 node5204Raw ++ scaleRow (-(1 : ℤ)) node5204 ++
      ([])) = [] := by
  decide +kernel

theorem node5204_mem : rowEval varIndex node5204 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5204Raw node5204 ([])
    (1) (1) (by decide) node5204_check
  · rw [node5204Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · exact candidateIdeal.zero_mem

def node5205 : WordRow := [([2, 7, 14, 17], 1), ([2, 10, 13, 17], 1), ([2, 11, 12, 17], 1), ([3, 6, 14, 17], -1), ([6, 8, 11, 17], -1), ([6, 9, 10, 17], -1)]

def node5205Raw : WordRow := multiplyRow 17 node0651

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5205_check :
    collect (scaleRow 1 node5205Raw ++ scaleRow (-(1 : ℤ)) node5205 ++
      ([])) = [] := by
  decide +kernel

theorem node5205_mem : rowEval varIndex node5205 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5205Raw node5205 ([])
    (1) (1) (by decide) node5205_check
  · rw [node5205Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0651_mem
  · exact candidateIdeal.zero_mem

def node5214 : WordRow := [([5, 7, 8, 14], 1), ([5, 8, 10, 13], 1), ([5, 8, 11, 12], 1), ([6, 8, 9, 13], 1), ([6, 9, 9, 12], 1)]

def node5214Raw : WordRow := multiplyRow 9 node0653

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5214_check :
    collect (scaleRow 1 node5214Raw ++ scaleRow (-(-1 : ℤ)) node5214 ++
      (scaleRow (-1) node3809 ++ scaleRow (-1) node3835 ++ scaleRow (-1) node3841 ++ scaleRow (1) node3874)) = [] := by
  decide +kernel

theorem node5214_mem : rowEval varIndex node5214 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5214Raw node5214 (scaleRow (-1) node3809 ++ scaleRow (-1) node3835 ++ scaleRow (-1) node3841 ++ scaleRow (1) node3874)
    (1) (-1) (by decide) node5214_check
  · rw [node5214Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0653_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3809 node3809_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3835 node3835_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3841 node3841_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3874 node3874_mem))))

def node5215 : WordRow := [([4, 7, 10, 14], 1), ([4, 10, 10, 13], 1), ([4, 10, 11, 12], 1), ([5, 6, 10, 14], -1), ([6, 8, 10, 13], -1), ([6, 9, 10, 12], -1)]

def node5215Raw : WordRow := multiplyRow 10 node0653

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5215_check :
    collect (scaleRow 1 node5215Raw ++ scaleRow (-(1 : ℤ)) node5215 ++
      ([])) = [] := by
  decide +kernel

theorem node5215_mem : rowEval varIndex node5215 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5215Raw node5215 ([])
    (1) (1) (by decide) node5215_check
  · rw [node5215Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0653_mem
  · exact candidateIdeal.zero_mem

def node5219 : WordRow := [([4, 7, 14, 14], 1), ([4, 10, 13, 14], 1), ([4, 11, 12, 14], 1), ([5, 6, 14, 14], -1), ([6, 8, 13, 14], -1), ([6, 9, 12, 14], -1)]

def node5219Raw : WordRow := multiplyRow 14 node0653

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5219_check :
    collect (scaleRow 1 node5219Raw ++ scaleRow (-(1 : ℤ)) node5219 ++
      ([])) = [] := by
  decide +kernel

theorem node5219_mem : rowEval varIndex node5219 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5219Raw node5219 ([])
    (1) (1) (by decide) node5219_check
  · rw [node5219Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0653_mem
  · exact candidateIdeal.zero_mem

def node5221 : WordRow := [([4, 7, 14, 16], 1), ([4, 10, 13, 16], 1), ([4, 11, 12, 16], 1), ([5, 6, 14, 16], -1), ([6, 8, 13, 16], -1), ([6, 9, 12, 16], -1)]

def node5221Raw : WordRow := multiplyRow 16 node0653

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5221_check :
    collect (scaleRow 1 node5221Raw ++ scaleRow (-(1 : ℤ)) node5221 ++
      ([])) = [] := by
  decide +kernel

theorem node5221_mem : rowEval varIndex node5221 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5221Raw node5221 ([])
    (1) (1) (by decide) node5221_check
  · rw [node5221Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0653_mem
  · exact candidateIdeal.zero_mem

def node5222 : WordRow := [([4, 7, 14, 17], 1), ([4, 10, 13, 17], 1), ([4, 11, 12, 17], 1), ([5, 6, 14, 17], -1), ([6, 8, 13, 17], -1), ([6, 9, 12, 17], -1)]

def node5222Raw : WordRow := multiplyRow 17 node0653

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5222_check :
    collect (scaleRow 1 node5222Raw ++ scaleRow (-(1 : ℤ)) node5222 ++
      ([])) = [] := by
  decide +kernel

theorem node5222_mem : rowEval varIndex node5222 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5222Raw node5222 ([])
    (1) (1) (by decide) node5222_check
  · rw [node5222Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0653_mem
  · exact candidateIdeal.zero_mem

def node5228 : WordRow := [([6, 6, 8, 15], 1), ([6, 7, 8, 14], 1), ([6, 8, 10, 13], 1), ([6, 8, 11, 12], 1)]

def node5228Raw : WordRow := multiplyRow 8 node0655

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5228_check :
    collect (scaleRow 1 node5228Raw ++ scaleRow (-(1 : ℤ)) node5228 ++
      ([])) = [] := by
  decide +kernel

theorem node5228_mem : rowEval varIndex node5228 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5228Raw node5228 ([])
    (1) (1) (by decide) node5228_check
  · rw [node5228Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0655_mem
  · exact candidateIdeal.zero_mem

def node5233 : WordRow := [([6, 6, 15, 16], 1), ([6, 7, 14, 16], 1), ([6, 10, 13, 16], 1), ([6, 11, 12, 16], 1)]

def node5233Raw : WordRow := multiplyRow 16 node0655

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5233_check :
    collect (scaleRow 1 node5233Raw ++ scaleRow (-(1 : ℤ)) node5233 ++
      ([])) = [] := by
  decide +kernel

theorem node5233_mem : rowEval varIndex node5233 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5233Raw node5233 ([])
    (1) (1) (by decide) node5233_check
  · rw [node5233Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0655_mem
  · exact candidateIdeal.zero_mem

def node5235 : WordRow := [([6, 8, 8, 15], 1), ([7, 8, 8, 14], 1), ([8, 8, 10, 13], 1), ([8, 8, 11, 12], 1)]

def node5235Raw : WordRow := multiplyRow 8 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5235_check :
    collect (scaleRow 1 node5235Raw ++ scaleRow (-(1 : ℤ)) node5235 ++
      ([])) = [] := by
  decide +kernel

theorem node5235_mem : rowEval varIndex node5235 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5235Raw node5235 ([])
    (1) (1) (by decide) node5235_check
  · rw [node5235Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · exact candidateIdeal.zero_mem

def node5236 : WordRow := [([6, 8, 10, 15], 1), ([7, 8, 10, 14], 1), ([8, 10, 10, 13], 1), ([8, 10, 11, 12], 1)]

def node5236Raw : WordRow := multiplyRow 10 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5236_check :
    collect (scaleRow 1 node5236Raw ++ scaleRow (-(1 : ℤ)) node5236 ++
      ([])) = [] := by
  decide +kernel

theorem node5236_mem : rowEval varIndex node5236 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5236Raw node5236 ([])
    (1) (1) (by decide) node5236_check
  · rw [node5236Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · exact candidateIdeal.zero_mem

def node5238 : WordRow := [([6, 8, 12, 15], 1), ([7, 8, 12, 14], 1), ([8, 10, 12, 13], 1), ([8, 11, 12, 12], 1)]

def node5238Raw : WordRow := multiplyRow 12 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5238_check :
    collect (scaleRow 1 node5238Raw ++ scaleRow (-(1 : ℤ)) node5238 ++
      ([])) = [] := by
  decide +kernel

theorem node5238_mem : rowEval varIndex node5238 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5238Raw node5238 ([])
    (1) (1) (by decide) node5238_check
  · rw [node5238Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · exact candidateIdeal.zero_mem

def node5239 : WordRow := [([7, 8, 12, 15], 1), ([7, 8, 13, 14], -1), ([8, 10, 13, 13], -1), ([8, 11, 12, 13], -1)]

def node5239Raw : WordRow := multiplyRow 13 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5239_check :
    collect (scaleRow 1 node5239Raw ++ scaleRow (-(-1 : ℤ)) node5239 ++
      (scaleRow (-1) node4527)) = [] := by
  decide +kernel

theorem node5239_mem : rowEval varIndex node5239 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5239Raw node5239 (scaleRow (-1) node4527)
    (1) (-1) (by decide) node5239_check
  · rw [node5239Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4527 node4527_mem)

def node5240 : WordRow := [([6, 8, 14, 15], 1), ([7, 8, 14, 14], 1), ([8, 10, 13, 14], 1), ([8, 11, 12, 14], 1)]

def node5240Raw : WordRow := multiplyRow 14 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5240_check :
    collect (scaleRow 1 node5240Raw ++ scaleRow (-(1 : ℤ)) node5240 ++
      ([])) = [] := by
  decide +kernel

theorem node5240_mem : rowEval varIndex node5240 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5240Raw node5240 ([])
    (1) (1) (by decide) node5240_check
  · rw [node5240Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · exact candidateIdeal.zero_mem

def node5242 : WordRow := [([6, 8, 15, 16], 1), ([7, 8, 14, 16], 1), ([8, 10, 13, 16], 1), ([8, 11, 12, 16], 1)]

def node5242Raw : WordRow := multiplyRow 16 node0656

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5242_check :
    collect (scaleRow 1 node5242Raw ++ scaleRow (-(1 : ℤ)) node5242 ++
      ([])) = [] := by
  decide +kernel

theorem node5242_mem : rowEval varIndex node5242 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5242Raw node5242 ([])
    (1) (1) (by decide) node5242_check
  · rw [node5242Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0656_mem
  · exact candidateIdeal.zero_mem

def node5253 : WordRow := [([6, 10, 15, 16], 1), ([7, 10, 14, 16], 1), ([10, 10, 13, 16], 1), ([10, 11, 12, 16], 1)]

def node5253Raw : WordRow := multiplyRow 16 node0658

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5253_check :
    collect (scaleRow 1 node5253Raw ++ scaleRow (-(1 : ℤ)) node5253 ++
      ([])) = [] := by
  decide +kernel

theorem node5253_mem : rowEval varIndex node5253 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5253Raw node5253 ([])
    (1) (1) (by decide) node5253_check
  · rw [node5253Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0658_mem
  · exact candidateIdeal.zero_mem

def node5264 : WordRow := [([6, 12, 15, 16], 1), ([7, 12, 14, 16], 1), ([10, 12, 13, 16], 1), ([11, 12, 12, 16], 1)]

def node5264Raw : WordRow := multiplyRow 16 node0660

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5264_check :
    collect (scaleRow 1 node5264Raw ++ scaleRow (-(1 : ℤ)) node5264 ++
      ([])) = [] := by
  decide +kernel

theorem node5264_mem : rowEval varIndex node5264 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5264Raw node5264 ([])
    (1) (1) (by decide) node5264_check
  · rw [node5264Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0660_mem
  · exact candidateIdeal.zero_mem

def node5273 : WordRow := [([6, 14, 15, 16], 1), ([7, 14, 14, 16], 1), ([10, 13, 14, 16], 1), ([11, 12, 14, 16], 1)]

def node5273Raw : WordRow := multiplyRow 16 node0662

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5273_check :
    collect (scaleRow 1 node5273Raw ++ scaleRow (-(1 : ℤ)) node5273 ++
      ([])) = [] := by
  decide +kernel

theorem node5273_mem : rowEval varIndex node5273 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5273Raw node5273 ([])
    (1) (1) (by decide) node5273_check
  · rw [node5273Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0662_mem
  · exact candidateIdeal.zero_mem

def node5279 : WordRow := [([6, 15, 16, 17], 1), ([7, 14, 16, 17], 1), ([10, 13, 16, 17], 1), ([11, 12, 16, 17], 1)]

def node5279Raw : WordRow := multiplyRow 17 node0664

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5279_check :
    collect (scaleRow 1 node5279Raw ++ scaleRow (-(1 : ℤ)) node5279 ++
      ([])) = [] := by
  decide +kernel

theorem node5279_mem : rowEval varIndex node5279 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5279Raw node5279 ([])
    (1) (1) (by decide) node5279_check
  · rw [node5279Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0664_mem
  · exact candidateIdeal.zero_mem

def node5282 : WordRow := [([8, 11, 12, 13], 1), ([9, 10, 12, 13], -1)]

def node5282Raw : WordRow := multiplyRow 12 node0666

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5282_check :
    collect (scaleRow 1 node5282Raw ++ scaleRow (-(2 : ℤ)) node5282 ++
      (scaleRow (-1) node5239 ++ scaleRow (-1) node4577 ++ scaleRow (-1) node5154)) = [] := by
  decide +kernel

theorem node5282_mem : rowEval varIndex node5282 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5282Raw node5282 (scaleRow (-1) node5239 ++ scaleRow (-1) node4577 ++ scaleRow (-1) node5154)
    (1) (2) (by decide) node5282_check
  · rw [node5282Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0666_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5239 node5239_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4577 node4577_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5154 node5154_mem)))

def node5313 : WordRow := [([1, 2, 12, 12], 1), ([2, 4, 7, 12], -1), ([2, 5, 6, 12], -1)]

def node5313Raw : WordRow := multiplyRow 2 node0674

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5313_check :
    collect (scaleRow 1 node5313Raw ++ scaleRow (-(1 : ℤ)) node5313 ++
      ([])) = [] := by
  decide +kernel

theorem node5313_mem : rowEval varIndex node5313 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5313Raw node5313 ([])
    (1) (1) (by decide) node5313_check
  · rw [node5313Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0674_mem
  · exact candidateIdeal.zero_mem

def node5319 : WordRow := [([1, 12, 12, 16], 1), ([4, 7, 12, 16], -1), ([5, 6, 12, 16], -1)]

def node5319Raw : WordRow := multiplyRow 16 node0674

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5319_check :
    collect (scaleRow 1 node5319Raw ++ scaleRow (-(1 : ℤ)) node5319 ++
      ([])) = [] := by
  decide +kernel

theorem node5319_mem : rowEval varIndex node5319 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5319Raw node5319 ([])
    (1) (1) (by decide) node5319_check
  · rw [node5319Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0674_mem
  · exact candidateIdeal.zero_mem

def node5321 : WordRow := [([2, 2, 12, 13], 1)]

def node5321Raw : WordRow := multiplyRow 2 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5321_check :
    collect (scaleRow 1 node5321Raw ++ scaleRow (-(1 : ℤ)) node5321 ++
      ([])) = [] := by
  decide +kernel

theorem node5321_mem : rowEval varIndex node5321 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5321Raw node5321 ([])
    (1) (1) (by decide) node5321_check
  · rw [node5321Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5324 : WordRow := [([2, 8, 12, 13], 1)]

def node5324Raw : WordRow := multiplyRow 8 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5324_check :
    collect (scaleRow 1 node5324Raw ++ scaleRow (-(1 : ℤ)) node5324 ++
      ([])) = [] := by
  decide +kernel

theorem node5324_mem : rowEval varIndex node5324 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5324Raw node5324 ([])
    (1) (1) (by decide) node5324_check
  · rw [node5324Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5325 : WordRow := [([2, 10, 12, 13], 1)]

def node5325Raw : WordRow := multiplyRow 10 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5325_check :
    collect (scaleRow 1 node5325Raw ++ scaleRow (-(1 : ℤ)) node5325 ++
      ([])) = [] := by
  decide +kernel

theorem node5325_mem : rowEval varIndex node5325 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5325Raw node5325 ([])
    (1) (1) (by decide) node5325_check
  · rw [node5325Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5327 : WordRow := [([2, 12, 13, 14], 1)]

def node5327Raw : WordRow := multiplyRow 14 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5327_check :
    collect (scaleRow 1 node5327Raw ++ scaleRow (-(1 : ℤ)) node5327 ++
      ([])) = [] := by
  decide +kernel

theorem node5327_mem : rowEval varIndex node5327 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5327Raw node5327 ([])
    (1) (1) (by decide) node5327_check
  · rw [node5327Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5328 : WordRow := [([3, 12, 13, 14], 1), ([8, 11, 12, 13], 1), ([9, 10, 12, 13], 1)]

def node5328Raw : WordRow := multiplyRow 15 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5328_check :
    collect (scaleRow 1 node5328Raw ++ scaleRow (-(-1 : ℤ)) node5328 ++
      (scaleRow (-1) node4853)) = [] := by
  decide +kernel

theorem node5328_mem : rowEval varIndex node5328 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5328Raw node5328 (scaleRow (-1) node4853)
    (1) (-1) (by decide) node5328_check
  · rw [node5328Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4853 node4853_mem)

def node5329 : WordRow := [([2, 12, 13, 16], 1)]

def node5329Raw : WordRow := multiplyRow 16 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5329_check :
    collect (scaleRow 1 node5329Raw ++ scaleRow (-(1 : ℤ)) node5329 ++
      ([])) = [] := by
  decide +kernel

theorem node5329_mem : rowEval varIndex node5329 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5329Raw node5329 ([])
    (1) (1) (by decide) node5329_check
  · rw [node5329Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5330 : WordRow := [([2, 12, 13, 17], 1)]

def node5330Raw : WordRow := multiplyRow 17 node0675

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5330_check :
    collect (scaleRow 1 node5330Raw ++ scaleRow (-(1 : ℤ)) node5330 ++
      ([])) = [] := by
  decide +kernel

theorem node5330_mem : rowEval varIndex node5330 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5330Raw node5330 ([])
    (1) (1) (by decide) node5330_check
  · rw [node5330Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0675_mem
  · exact candidateIdeal.zero_mem

def node5331 : WordRow := [([9, 10, 12, 13], 1)]

def node5331Raw : WordRow := multiplyRow 14 node0676

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5331_check :
    collect (scaleRow 1 node5331Raw ++ scaleRow (-(-2 : ℤ)) node5331 ++
      (scaleRow (-1) node5328 ++ scaleRow (1) node5282)) = [] := by
  decide +kernel

theorem node5331_mem : rowEval varIndex node5331 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5331Raw node5331 (scaleRow (-1) node5328 ++ scaleRow (1) node5282)
    (1) (-2) (by decide) node5331_check
  · rw [node5331Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0676_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5328 node5328_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5282 node5282_mem))

def node5350 : WordRow := [([8, 10, 12, 13], 1)]

def node5350Raw : WordRow := multiplyRow 10 node0679

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5350_check :
    collect (scaleRow 1 node5350Raw ++ scaleRow (-(1 : ℤ)) node5350 ++
      ([])) = [] := by
  decide +kernel

theorem node5350_mem : rowEval varIndex node5350 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5350Raw node5350 ([])
    (1) (1) (by decide) node5350_check
  · rw [node5350Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0679_mem
  · exact candidateIdeal.zero_mem

def node5355 : WordRow := [([8, 12, 13, 17], 1)]

def node5355Raw : WordRow := multiplyRow 17 node0679

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5355_check :
    collect (scaleRow 1 node5355Raw ++ scaleRow (-(1 : ℤ)) node5355 ++
      ([])) = [] := by
  decide +kernel

theorem node5355_mem : rowEval varIndex node5355 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5355Raw node5355 ([])
    (1) (1) (by decide) node5355_check
  · rw [node5355Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0679_mem
  · exact candidateIdeal.zero_mem

def node5365 : WordRow := [([10, 12, 13, 17], 1)]

def node5365Raw : WordRow := multiplyRow 17 node0681

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5365_check :
    collect (scaleRow 1 node5365Raw ++ scaleRow (-(1 : ℤ)) node5365 ++
      ([])) = [] := by
  decide +kernel

theorem node5365_mem : rowEval varIndex node5365 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5365Raw node5365 ([])
    (1) (1) (by decide) node5365_check
  · rw [node5365Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0681_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node5365_mem
