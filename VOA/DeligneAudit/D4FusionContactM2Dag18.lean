import VOA.DeligneAudit.D4FusionContactM2Dag17

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node6051 : WordRow := [([5, 6, 8, 17], 1), ([5, 7, 8, 16], 1)]

def node6051Raw : WordRow := multiplyRow 4 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6051_check :
    collect (scaleRow 1 node6051Raw ++ scaleRow (-(-2 : ℤ)) node6051 ++
      (scaleRow (-1) node3802 ++ scaleRow (-1) node6011 ++ scaleRow (-1) node3811)) = [] := by
  decide +kernel

theorem node6051_mem : rowEval varIndex node6051 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6051Raw node6051 (scaleRow (-1) node3802 ++ scaleRow (-1) node6011 ++ scaleRow (-1) node3811)
    (1) (-2) (by decide) node6051_check
  · rw [node6051Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3802 node3802_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6011 node6011_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3811 node3811_mem)))

def node6053 : WordRow := [([7, 8, 8, 17], 1), ([7, 8, 9, 16], 1)]

def node6053Raw : WordRow := multiplyRow 8 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6053_check :
    collect (scaleRow 1 node6053Raw ++ scaleRow (-(1 : ℤ)) node6053 ++
      (scaleRow (-1) node4647)) = [] := by
  decide +kernel

theorem node6053_mem : rowEval varIndex node6053 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6053Raw node6053 (scaleRow (-1) node4647)
    (1) (1) (by decide) node6053_check
  · rw [node6053Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4647 node4647_mem)

def node6054 : WordRow := [([7, 8, 10, 17], 1), ([7, 9, 10, 16], 1)]

def node6054Raw : WordRow := multiplyRow 10 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6054_check :
    collect (scaleRow 1 node6054Raw ++ scaleRow (-(2 : ℤ)) node6054 ++
      (scaleRow (-1) node6043 ++ scaleRow (1) node4215)) = [] := by
  decide +kernel

theorem node6054_mem : rowEval varIndex node6054 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6054Raw node6054 (scaleRow (-1) node6043 ++ scaleRow (1) node4215)
    (1) (2) (by decide) node6054_check
  · rw [node6054Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6043 node6043_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4215 node4215_mem))

def node6055 : WordRow := [([6, 9, 12, 17], 1), ([7, 8, 12, 17], 1), ([7, 9, 12, 16], 1)]

def node6055Raw : WordRow := multiplyRow 12 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6055_check :
    collect (scaleRow 1 node6055Raw ++ scaleRow (-(1 : ℤ)) node6055 ++
      ([])) = [] := by
  decide +kernel

theorem node6055_mem : rowEval varIndex node6055 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6055Raw node6055 ([])
    (1) (1) (by decide) node6055_check
  · rw [node6055Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · exact candidateIdeal.zero_mem

def node6057 : WordRow := [([7, 8, 14, 17], 2), ([7, 9, 14, 16], 1), ([8, 10, 13, 17], 1), ([8, 11, 12, 17], 1)]

def node6057Raw : WordRow := multiplyRow 14 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6057_check :
    collect (scaleRow 1 node6057Raw ++ scaleRow (-(1 : ℤ)) node6057 ++
      (scaleRow (-1) node5444)) = [] := by
  decide +kernel

theorem node6057_mem : rowEval varIndex node6057 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6057Raw node6057 (scaleRow (-1) node5444)
    (1) (1) (by decide) node6057_check
  · rw [node6057Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5444 node5444_mem)

def node6059 : WordRow := [([7, 8, 16, 17], 2), ([7, 9, 16, 16], 1)]

def node6059Raw : WordRow := multiplyRow 16 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6059_check :
    collect (scaleRow 1 node6059Raw ++ scaleRow (-(1 : ℤ)) node6059 ++
      (scaleRow (-1) node5884)) = [] := by
  decide +kernel

theorem node6059_mem : rowEval varIndex node6059 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6059Raw node6059 (scaleRow (-1) node5884)
    (1) (1) (by decide) node6059_check
  · rw [node6059Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5884 node5884_mem)

def node6060 : WordRow := [([1, 8, 12, 17], 2), ([1, 8, 13, 16], 1), ([2, 5, 12, 17], -1), ([2, 5, 13, 16], -1), ([3, 4, 12, 17], -1), ([3, 4, 13, 16], -1), ([4, 7, 8, 17], -1), ([5, 6, 8, 17], -1)]

def node6060Raw : WordRow := multiplyRow 0 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6060_check :
    collect (scaleRow 1 node6060Raw ++ scaleRow (-(-1 : ℤ)) node6060 ++
      (scaleRow (-1) node3030 ++ scaleRow (-1) node2363 ++ scaleRow (-1) node2367)) = [] := by
  decide +kernel

theorem node6060_mem : rowEval varIndex node6060 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6060Raw node6060 (scaleRow (-1) node3030 ++ scaleRow (-1) node2363 ++ scaleRow (-1) node2367)
    (1) (-1) (by decide) node6060_check
  · rw [node6060Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3030 node3030_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2363 node2363_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2367 node2367_mem)))

def node6061 : WordRow := [([3, 8, 12, 17], 2), ([3, 8, 13, 16], 2), ([4, 8, 11, 17], 1), ([5, 8, 10, 17], 1), ([5, 8, 11, 16], 1), ([6, 8, 9, 17], 1), ([7, 8, 8, 17], 1), ([7, 8, 9, 16], 1)]

def node6061Raw : WordRow := multiplyRow 2 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6061_check :
    collect (scaleRow 1 node6061Raw ++ scaleRow (-(-1 : ℤ)) node6061 ++
      (scaleRow (-1) node5991 ++ scaleRow (-1) node3468 ++ scaleRow (-1) node6023)) = [] := by
  decide +kernel

theorem node6061_mem : rowEval varIndex node6061 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6061Raw node6061 (scaleRow (-1) node5991 ++ scaleRow (-1) node3468 ++ scaleRow (-1) node6023)
    (1) (-1) (by decide) node6061_check
  · rw [node6061Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5991 node5991_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3468 node3468_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node6023 node6023_mem)))

def node6062 : WordRow := [([5, 8, 12, 17], 2), ([5, 8, 13, 16], 1)]

def node6062Raw : WordRow := multiplyRow 4 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6062_check :
    collect (scaleRow 1 node6062Raw ++ scaleRow (-(-1 : ℤ)) node6062 ++
      (scaleRow (-1) node4374 ++ scaleRow (-1) node3852 ++ scaleRow (-1) node3856)) = [] := by
  decide +kernel

theorem node6062_mem : rowEval varIndex node6062 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6062Raw node6062 (scaleRow (-1) node4374 ++ scaleRow (-1) node3852 ++ scaleRow (-1) node3856)
    (1) (-1) (by decide) node6062_check
  · rw [node6062Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4374 node4374_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3852 node3852_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3856 node3856_mem)))

def node6063 : WordRow := [([7, 8, 12, 17], 1), ([7, 9, 12, 16], 1)]

def node6063Raw : WordRow := multiplyRow 6 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6063_check :
    collect (scaleRow 1 node6063Raw ++ scaleRow (-(-2 : ℤ)) node6063 ++
      (scaleRow (-1) node4529 ++ scaleRow (-1) node6055 ++ scaleRow (-1) node4537)) = [] := by
  decide +kernel

theorem node6063_mem : rowEval varIndex node6063 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6063Raw node6063 (scaleRow (-1) node4529 ++ scaleRow (-1) node6055 ++ scaleRow (-1) node4537)
    (1) (-2) (by decide) node6063_check
  · rw [node6063Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4529 node4529_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6055 node6055_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4537 node4537_mem)))

def node6065 : WordRow := [([8, 10, 13, 17], 1), ([9, 10, 12, 17], 1), ([9, 10, 13, 16], 1)]

def node6065Raw : WordRow := multiplyRow 10 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6065_check :
    collect (scaleRow 1 node6065Raw ++ scaleRow (-(1 : ℤ)) node6065 ++
      ([])) = [] := by
  decide +kernel

theorem node6065_mem : rowEval varIndex node6065 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6065Raw node6065 ([])
    (1) (1) (by decide) node6065_check
  · rw [node6065Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · exact candidateIdeal.zero_mem

def node6066 : WordRow := [([9, 12, 12, 17], 1), ([9, 12, 13, 16], 1)]

def node6066Raw : WordRow := multiplyRow 12 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6066_check :
    collect (scaleRow 1 node6066Raw ++ scaleRow (-(1 : ℤ)) node6066 ++
      (scaleRow (-1) node5355)) = [] := by
  decide +kernel

theorem node6066_mem : rowEval varIndex node6066 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6066Raw node6066 (scaleRow (-1) node5355)
    (1) (1) (by decide) node6066_check
  · rw [node6066Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5355 node5355_mem)

def node6067 : WordRow := [([9, 12, 14, 17], 2), ([9, 13, 14, 16], 1)]

def node6067Raw : WordRow := multiplyRow 14 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6067_check :
    collect (scaleRow 1 node6067Raw ++ scaleRow (-(1 : ℤ)) node6067 ++
      (scaleRow (-1) node5647)) = [] := by
  decide +kernel

theorem node6067_mem : rowEval varIndex node6067 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6067Raw node6067 (scaleRow (-1) node5647)
    (1) (1) (by decide) node6067_check
  · rw [node6067Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5647 node5647_mem)

def node6068 : WordRow := [([9, 12, 16, 17], 2), ([9, 13, 16, 16], 1)]

def node6068Raw : WordRow := multiplyRow 16 node0812

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6068_check :
    collect (scaleRow 1 node6068Raw ++ scaleRow (-(1 : ℤ)) node6068 ++
      (scaleRow (-1) node5912)) = [] := by
  decide +kernel

theorem node6068_mem : rowEval varIndex node6068 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6068Raw node6068 (scaleRow (-1) node5912)
    (1) (1) (by decide) node6068_check
  · rw [node6068Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0812_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5912 node5912_mem)

def node6069 : WordRow := [([1, 10, 12, 17], 2), ([1, 10, 13, 16], 1), ([2, 7, 12, 17], -1), ([2, 7, 13, 16], -1), ([3, 6, 12, 17], -1), ([3, 6, 13, 16], -1), ([4, 7, 10, 17], -1), ([5, 6, 10, 17], -1)]

def node6069Raw : WordRow := multiplyRow 0 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6069_check :
    collect (scaleRow 1 node6069Raw ++ scaleRow (-(-1 : ℤ)) node6069 ++
      (scaleRow (-1) node3047 ++ scaleRow (-1) node2610 ++ scaleRow (-1) node2614)) = [] := by
  decide +kernel

theorem node6069_mem : rowEval varIndex node6069 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6069Raw node6069 (scaleRow (-1) node3047 ++ scaleRow (-1) node2610 ++ scaleRow (-1) node2614)
    (1) (-1) (by decide) node6069_check
  · rw [node6069Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3047 node3047_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2610 node2610_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2614 node2614_mem)))

def node6070 : WordRow := [([3, 10, 12, 17], 2), ([3, 10, 13, 16], 2), ([4, 10, 11, 17], 1), ([5, 10, 10, 17], 1), ([5, 10, 11, 16], 1), ([6, 9, 10, 17], 1), ([7, 8, 10, 17], 1), ([7, 9, 10, 16], 1)]

def node6070Raw : WordRow := multiplyRow 2 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6070_check :
    collect (scaleRow 1 node6070Raw ++ scaleRow (-(-1 : ℤ)) node6070 ++
      (scaleRow (-1) node6004 ++ scaleRow (-1) node3684 ++ scaleRow (-1) node6024)) = [] := by
  decide +kernel

theorem node6070_mem : rowEval varIndex node6070 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6070Raw node6070 (scaleRow (-1) node6004 ++ scaleRow (-1) node3684 ++ scaleRow (-1) node6024)
    (1) (-1) (by decide) node6070_check
  · rw [node6070Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6004 node6004_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3684 node3684_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node6024 node6024_mem)))

def node6071 : WordRow := [([5, 10, 12, 17], 2), ([5, 11, 12, 16], 2), ([6, 9, 12, 17], 1), ([7, 8, 12, 17], 1), ([7, 9, 12, 16], 1)]

def node6071Raw : WordRow := multiplyRow 4 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6071_check :
    collect (scaleRow 1 node6071Raw ++ scaleRow (-(-1 : ℤ)) node6071 ++
      (scaleRow (-1) node4390 ++ scaleRow (-1) node6016 ++ scaleRow (-1) node4396 ++ scaleRow (-1) node6036)) = [] := by
  decide +kernel

theorem node6071_mem : rowEval varIndex node6071 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6071Raw node6071 (scaleRow (-1) node4390 ++ scaleRow (-1) node6016 ++ scaleRow (-1) node4396 ++ scaleRow (-1) node6036)
    (1) (-1) (by decide) node6071_check
  · rw [node6071Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4390 node4390_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6016 node6016_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4396 node4396_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node6036 node6036_mem))))

def node6072 : WordRow := [([7, 10, 12, 17], 2), ([7, 10, 13, 16], 1)]

def node6072Raw : WordRow := multiplyRow 6 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6072_check :
    collect (scaleRow 1 node6072Raw ++ scaleRow (-(-1 : ℤ)) node6072 ++
      (scaleRow (-1) node4546 ++ scaleRow (-1) node4237 ++ scaleRow (-1) node4241)) = [] := by
  decide +kernel

theorem node6072_mem : rowEval varIndex node6072 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6072Raw node6072 (scaleRow (-1) node4546 ++ scaleRow (-1) node4237 ++ scaleRow (-1) node4241)
    (1) (-1) (by decide) node6072_check
  · rw [node6072Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4546 node4546_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4237 node4237_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4241 node4241_mem)))

def node6073 : WordRow := [([9, 10, 12, 17], 1), ([9, 10, 13, 16], 1), ([9, 11, 12, 16], 1)]

def node6073Raw : WordRow := multiplyRow 8 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6073_check :
    collect (scaleRow 1 node6073Raw ++ scaleRow (-(-2 : ℤ)) node6073 ++
      (scaleRow (-1) node6065 ++ scaleRow (-1) node6046 ++ scaleRow (-1) node5491)) = [] := by
  decide +kernel

theorem node6073_mem : rowEval varIndex node6073 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6073Raw node6073 (scaleRow (-1) node6065 ++ scaleRow (-1) node6046 ++ scaleRow (-1) node5491)
    (1) (-2) (by decide) node6073_check
  · rw [node6073Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6065 node6065_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6046 node6046_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5491 node5491_mem)))

def node6075 : WordRow := [([11, 12, 12, 17], 1), ([11, 12, 13, 16], 1)]

def node6075Raw : WordRow := multiplyRow 12 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6075_check :
    collect (scaleRow 1 node6075Raw ++ scaleRow (-(1 : ℤ)) node6075 ++
      (scaleRow (-1) node5365)) = [] := by
  decide +kernel

theorem node6075_mem : rowEval varIndex node6075 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6075Raw node6075 (scaleRow (-1) node5365)
    (1) (1) (by decide) node6075_check
  · rw [node6075Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5365 node5365_mem)

def node6076 : WordRow := [([11, 12, 14, 17], 2), ([11, 13, 14, 16], 1)]

def node6076Raw : WordRow := multiplyRow 14 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6076_check :
    collect (scaleRow 1 node6076Raw ++ scaleRow (-(1 : ℤ)) node6076 ++
      (scaleRow (-1) node5655)) = [] := by
  decide +kernel

theorem node6076_mem : rowEval varIndex node6076 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6076Raw node6076 (scaleRow (-1) node5655)
    (1) (1) (by decide) node6076_check
  · rw [node6076Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5655 node5655_mem)

def node6077 : WordRow := [([11, 12, 16, 17], 2), ([11, 13, 16, 16], 1)]

def node6077Raw : WordRow := multiplyRow 16 node0814

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6077_check :
    collect (scaleRow 1 node6077Raw ++ scaleRow (-(1 : ℤ)) node6077 ++
      (scaleRow (-1) node5914)) = [] := by
  decide +kernel

theorem node6077_mem : rowEval varIndex node6077 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6077Raw node6077 (scaleRow (-1) node5914)
    (1) (1) (by decide) node6077_check
  · rw [node6077Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0814_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5914 node5914_mem)

def node6095 : WordRow := [([0, 2, 8, 17], 2), ([2, 2, 4, 17], -1)]

def node6095Raw : WordRow := multiplyRow 17 node0817

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6095_check :
    collect (scaleRow 1 node6095Raw ++ scaleRow (-(1 : ℤ)) node6095 ++
      ([])) = [] := by
  decide +kernel

theorem node6095_mem : rowEval varIndex node6095 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6095Raw node6095 ([])
    (1) (1) (by decide) node6095_check
  · rw [node6095Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0817_mem
  · exact candidateIdeal.zero_mem

def node6103 : WordRow := [([0, 2, 10, 17], 2), ([2, 2, 6, 17], -1)]

def node6103Raw : WordRow := multiplyRow 17 node0818

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6103_check :
    collect (scaleRow 1 node6103Raw ++ scaleRow (-(1 : ℤ)) node6103 ++
      ([])) = [] := by
  decide +kernel

theorem node6103_mem : rowEval varIndex node6103 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6103Raw node6103 ([])
    (1) (1) (by decide) node6103_check
  · rw [node6103Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0818_mem
  · exact candidateIdeal.zero_mem

def node6112 : WordRow := [([0, 4, 8, 17], 2), ([2, 4, 4, 17], -1)]

def node6112Raw : WordRow := multiplyRow 17 node0819

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6112_check :
    collect (scaleRow 1 node6112Raw ++ scaleRow (-(1 : ℤ)) node6112 ++
      ([])) = [] := by
  decide +kernel

theorem node6112_mem : rowEval varIndex node6112 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6112Raw node6112 ([])
    (1) (1) (by decide) node6112_check
  · rw [node6112Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0819_mem
  · exact candidateIdeal.zero_mem

def node6118 : WordRow := [([2, 5, 10, 12], 1), ([2, 6, 8, 13], -2), ([2, 6, 9, 12], -2), ([2, 7, 8, 12], -1), ([3, 4, 6, 14], 2), ([3, 4, 10, 12], 1), ([3, 6, 8, 12], -1), ([4, 4, 10, 11], -1), ([4, 5, 10, 10], -1), ([4, 7, 8, 10], -1), ([5, 6, 8, 10], -1), ([6, 6, 8, 9], -1), ([6, 7, 8, 8], -1)]

def node6118Raw : WordRow := multiplyRow 15 node0820

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6118_check :
    collect (scaleRow 1 node6118Raw ++ scaleRow (-(2 : ℤ)) node6118 ++
      (scaleRow (-1) node3949 ++ scaleRow (1) node1031 ++ scaleRow (2) node3961 ++ scaleRow (-1) node2961 ++ scaleRow (-1) node1328 ++ scaleRow (2) node3978 ++ scaleRow (-1) node2532 ++ scaleRow (-1) node1602 ++ scaleRow (2) node3995 ++ scaleRow (-1) node2309 ++ scaleRow (-1) node1837 ++ scaleRow (2) node5321 ++ scaleRow (2) node2092 ++ scaleRow (-2) node4789 ++ scaleRow (-2) node5195 ++ scaleRow (4) node4323 ++ scaleRow (4) node3607 ++ scaleRow (-2) node5051)) = [] := by
  decide +kernel

theorem node6118_mem : rowEval varIndex node6118 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6118Raw node6118 (scaleRow (-1) node3949 ++ scaleRow (1) node1031 ++ scaleRow (2) node3961 ++ scaleRow (-1) node2961 ++ scaleRow (-1) node1328 ++ scaleRow (2) node3978 ++ scaleRow (-1) node2532 ++ scaleRow (-1) node1602 ++ scaleRow (2) node3995 ++ scaleRow (-1) node2309 ++ scaleRow (-1) node1837 ++ scaleRow (2) node5321 ++ scaleRow (2) node2092 ++ scaleRow (-2) node4789 ++ scaleRow (-2) node5195 ++ scaleRow (4) node4323 ++ scaleRow (4) node3607 ++ scaleRow (-2) node5051)
    (1) (2) (by decide) node6118_check
  · rw [node6118Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0820_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3949 node3949_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node1031 node1031_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3961 node3961_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2961 node2961_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1328 node1328_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3978 node3978_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2532 node2532_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1602 node1602_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3995 node3995_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2309 node2309_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1837 node1837_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5321 node5321_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2092 node2092_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4789 node4789_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5195 node5195_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (4) node4323 node4323_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (4) node3607 node3607_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5051 node5051_mem))))))))))))))))))

def node6120 : WordRow := [([0, 0, 14, 17], 1), ([0, 2, 12, 17], -2), ([0, 4, 10, 17], -2), ([0, 6, 8, 17], -2), ([2, 4, 6, 17], 2)]

def node6120Raw : WordRow := multiplyRow 17 node0820

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6120_check :
    collect (scaleRow 1 node6120Raw ++ scaleRow (-(1 : ℤ)) node6120 ++
      ([])) = [] := by
  decide +kernel

theorem node6120_mem : rowEval varIndex node6120 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6120Raw node6120 ([])
    (1) (1) (by decide) node6120_check
  · rw [node6120Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0820_mem
  · exact candidateIdeal.zero_mem

def node6128 : WordRow := [([0, 6, 10, 17], 2), ([2, 6, 6, 17], -1)]

def node6128Raw : WordRow := multiplyRow 17 node0821

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6128_check :
    collect (scaleRow 1 node6128Raw ++ scaleRow (-(1 : ℤ)) node6128 ++
      ([])) = [] := by
  decide +kernel

theorem node6128_mem : rowEval varIndex node6128 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6128Raw node6128 ([])
    (1) (1) (by decide) node6128_check
  · rw [node6128Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0821_mem
  · exact candidateIdeal.zero_mem

def node6144 : WordRow := [([0, 4, 12, 17], 2), ([4, 4, 6, 17], -1)]

def node6144Raw : WordRow := multiplyRow 17 node0823

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6144_check :
    collect (scaleRow 1 node6144Raw ++ scaleRow (-(1 : ℤ)) node6144 ++
      ([])) = [] := by
  decide +kernel

theorem node6144_mem : rowEval varIndex node6144 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6144Raw node6144 ([])
    (1) (1) (by decide) node6144_check
  · rw [node6144Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0823_mem
  · exact candidateIdeal.zero_mem

def node6152 : WordRow := [([0, 6, 12, 17], 2), ([4, 6, 6, 17], -1)]

def node6152Raw : WordRow := multiplyRow 17 node0824

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6152_check :
    collect (scaleRow 1 node6152Raw ++ scaleRow (-(1 : ℤ)) node6152 ++
      ([])) = [] := by
  decide +kernel

theorem node6152_mem : rowEval varIndex node6152 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6152Raw node6152 ([])
    (1) (1) (by decide) node6152_check
  · rw [node6152Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0824_mem
  · exact candidateIdeal.zero_mem

def node6182 : WordRow := [([0, 8, 8, 17], 1), ([2, 4, 8, 17], -2)]

def node6182Raw : WordRow := multiplyRow 17 node0828

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6182_check :
    collect (scaleRow 1 node6182Raw ++ scaleRow (-(1 : ℤ)) node6182 ++
      ([])) = [] := by
  decide +kernel

theorem node6182_mem : rowEval varIndex node6182 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6182Raw node6182 ([])
    (1) (1) (by decide) node6182_check
  · rw [node6182Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0828_mem
  · exact candidateIdeal.zero_mem

def node6188 : WordRow := [([2, 8, 10, 13], 1), ([2, 8, 11, 12], 1), ([2, 9, 10, 12], 1), ([3, 8, 10, 12], 1), ([4, 8, 10, 11], 2), ([4, 9, 10, 10], 1), ([5, 8, 10, 10], 1), ([6, 8, 8, 11], 1), ([6, 8, 9, 10], 2), ([7, 8, 8, 10], 1)]

def node6188Raw : WordRow := multiplyRow 15 node0829

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6188_check :
    collect (scaleRow 1 node6188Raw ++ scaleRow (-(2 : ℤ)) node6188 ++
      (scaleRow (-2) node3963 ++ scaleRow (-2) node4016 ++ scaleRow (1) node4773 ++ scaleRow (1) node4782 ++ scaleRow (-1) node5620 ++ scaleRow (-3) node2094 ++ scaleRow (2) node4792 ++ scaleRow (-1) node3609 ++ scaleRow (2) node4807 ++ scaleRow (-1) node3411)) = [] := by
  decide +kernel

theorem node6188_mem : rowEval varIndex node6188 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6188Raw node6188 (scaleRow (-2) node3963 ++ scaleRow (-2) node4016 ++ scaleRow (1) node4773 ++ scaleRow (1) node4782 ++ scaleRow (-1) node5620 ++ scaleRow (-3) node2094 ++ scaleRow (2) node4792 ++ scaleRow (-1) node3609 ++ scaleRow (2) node4807 ++ scaleRow (-1) node3411)
    (1) (2) (by decide) node6188_check
  · rw [node6188Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0829_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3963 node3963_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4016 node4016_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4773 node4773_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4782 node4782_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5620 node5620_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-3) node2094 node2094_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4792 node4792_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3609 node3609_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4807 node4807_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3411 node3411_mem))))))))))

def node6190 : WordRow := [([0, 2, 14, 17], 2), ([0, 8, 10, 17], 2), ([2, 2, 12, 17], -1), ([2, 4, 10, 17], -2), ([2, 6, 8, 17], -2)]

def node6190Raw : WordRow := multiplyRow 17 node0829

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6190_check :
    collect (scaleRow 1 node6190Raw ++ scaleRow (-(1 : ℤ)) node6190 ++
      ([])) = [] := by
  decide +kernel

theorem node6190_mem : rowEval varIndex node6190 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6190Raw node6190 ([])
    (1) (1) (by decide) node6190_check
  · rw [node6190Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0829_mem
  · exact candidateIdeal.zero_mem

def node6198 : WordRow := [([0, 10, 10, 17], 1), ([2, 6, 10, 17], -2)]

def node6198Raw : WordRow := multiplyRow 17 node0830

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6198_check :
    collect (scaleRow 1 node6198Raw ++ scaleRow (-(1 : ℤ)) node6198 ++
      ([])) = [] := by
  decide +kernel

theorem node6198_mem : rowEval varIndex node6198 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6198Raw node6198 ([])
    (1) (1) (by decide) node6198_check
  · rw [node6198Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0830_mem
  · exact candidateIdeal.zero_mem

def node6211 : WordRow := [([4, 8, 11, 12], 1), ([4, 9, 10, 12], 1), ([6, 8, 8, 13], 1), ([6, 8, 9, 12], 2), ([7, 8, 8, 12], 1)]

def node6211Raw : WordRow := multiplyRow 15 node0832

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6211_check :
    collect (scaleRow 1 node6211Raw ++ scaleRow (-(2 : ℤ)) node6211 ++
      (scaleRow (-2) node3982 ++ scaleRow (-2) node4018 ++ scaleRow (1) node5045 ++ scaleRow (2) node4794 ++ scaleRow (-1) node4327 ++ scaleRow (2) node5056 ++ scaleRow (-4) node5324 ++ scaleRow (-2) node3459 ++ scaleRow (1) node5071 ++ scaleRow (-1) node5540 ++ scaleRow (-3) node2814 ++ scaleRow (2) node5079 ++ scaleRow (-1) node3799 ++ scaleRow (-2) node4367)) = [] := by
  decide +kernel

theorem node6211_mem : rowEval varIndex node6211 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6211Raw node6211 (scaleRow (-2) node3982 ++ scaleRow (-2) node4018 ++ scaleRow (1) node5045 ++ scaleRow (2) node4794 ++ scaleRow (-1) node4327 ++ scaleRow (2) node5056 ++ scaleRow (-4) node5324 ++ scaleRow (-2) node3459 ++ scaleRow (1) node5071 ++ scaleRow (-1) node5540 ++ scaleRow (-3) node2814 ++ scaleRow (2) node5079 ++ scaleRow (-1) node3799 ++ scaleRow (-2) node4367)
    (1) (2) (by decide) node6211_check
  · rw [node6211Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0832_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3982 node3982_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4018 node4018_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5045 node5045_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4794 node4794_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4327 node4327_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5056 node5056_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node5324 node5324_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3459 node3459_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5071 node5071_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5540 node5540_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-3) node2814 node2814_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5079 node5079_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3799 node3799_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4367 node4367_mem))))))))))))))

def node6213 : WordRow := [([0, 4, 14, 17], 2), ([0, 8, 12, 17], 2), ([2, 4, 12, 17], -2), ([4, 4, 10, 17], -1), ([4, 6, 8, 17], -2)]

def node6213Raw : WordRow := multiplyRow 17 node0832

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6213_check :
    collect (scaleRow 1 node6213Raw ++ scaleRow (-(1 : ℤ)) node6213 ++
      ([])) = [] := by
  decide +kernel

theorem node6213_mem : rowEval varIndex node6213 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6213Raw node6213 ([])
    (1) (1) (by decide) node6213_check
  · rw [node6213Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0832_mem
  · exact candidateIdeal.zero_mem

def node6215 : WordRow := [([0, 6, 8, 14], 2), ([0, 8, 10, 12], 2), ([2, 6, 8, 12], -2), ([4, 6, 8, 10], -2), ([6, 6, 8, 8], -1)]

def node6215Raw : WordRow := multiplyRow 8 node0833

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6215_check :
    collect (scaleRow 1 node6215Raw ++ scaleRow (-(1 : ℤ)) node6215 ++
      ([])) = [] := by
  decide +kernel

theorem node6215_mem : rowEval varIndex node6215 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6215Raw node6215 ([])
    (1) (1) (by decide) node6215_check
  · rw [node6215Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0833_mem
  · exact candidateIdeal.zero_mem

def node6219 : WordRow := [([6, 9, 10, 12], 1), ([7, 8, 10, 12], -1)]

def node6219Raw : WordRow := multiplyRow 15 node0833

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6219_check :
    collect (scaleRow 1 node6219Raw ++ scaleRow (-(2 : ℤ)) node6219 ++
      (scaleRow (-2) node4001 ++ scaleRow (-2) node4035 ++ scaleRow (1) node5190 ++ scaleRow (2) node4811 ++ scaleRow (-1) node4486 ++ scaleRow (2) node5200 ++ scaleRow (-4) node5325 ++ scaleRow (-2) node3675 ++ scaleRow (2) node5081 ++ scaleRow (-1) node4177 ++ scaleRow (2) node5215 ++ scaleRow (-2) node4383 ++ scaleRow (-4) node4943 ++ scaleRow (1) node5228 ++ scaleRow (-1) node5435 ++ scaleRow (-3) node3240 ++ scaleRow (-2) node4522 ++ scaleRow (-2) node4202)) = [] := by
  decide +kernel

theorem node6219_mem : rowEval varIndex node6219 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6219Raw node6219 (scaleRow (-2) node4001 ++ scaleRow (-2) node4035 ++ scaleRow (1) node5190 ++ scaleRow (2) node4811 ++ scaleRow (-1) node4486 ++ scaleRow (2) node5200 ++ scaleRow (-4) node5325 ++ scaleRow (-2) node3675 ++ scaleRow (2) node5081 ++ scaleRow (-1) node4177 ++ scaleRow (2) node5215 ++ scaleRow (-2) node4383 ++ scaleRow (-4) node4943 ++ scaleRow (1) node5228 ++ scaleRow (-1) node5435 ++ scaleRow (-3) node3240 ++ scaleRow (-2) node4522 ++ scaleRow (-2) node4202)
    (1) (2) (by decide) node6219_check
  · rw [node6219Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0833_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4001 node4001_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4035 node4035_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5190 node5190_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4811 node4811_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4486 node4486_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5200 node5200_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node5325 node5325_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3675 node3675_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5081 node5081_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4177 node4177_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5215 node5215_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4383 node4383_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node4943 node4943_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5228 node5228_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5435 node5435_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-3) node3240 node3240_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4522 node4522_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4202 node4202_mem))))))))))))))))))

def node6221 : WordRow := [([0, 6, 14, 17], 2), ([0, 10, 12, 17], 2), ([2, 6, 12, 17], -2), ([4, 6, 10, 17], -2), ([6, 6, 8, 17], -1)]

def node6221Raw : WordRow := multiplyRow 17 node0833

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6221_check :
    collect (scaleRow 1 node6221Raw ++ scaleRow (-(1 : ℤ)) node6221 ++
      ([])) = [] := by
  decide +kernel

theorem node6221_mem : rowEval varIndex node6221 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6221Raw node6221 ([])
    (1) (1) (by decide) node6221_check
  · rw [node6221Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0833_mem
  · exact candidateIdeal.zero_mem

def node6241 : WordRow := [([0, 12, 12, 17], 1), ([4, 6, 12, 17], -2)]

def node6241Raw : WordRow := multiplyRow 17 node0836

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6241_check :
    collect (scaleRow 1 node6241Raw ++ scaleRow (-(1 : ℤ)) node6241 ++
      ([])) = [] := by
  decide +kernel

theorem node6241_mem : rowEval varIndex node6241 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6241Raw node6241 ([])
    (1) (1) (by decide) node6241_check
  · rw [node6241Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0836_mem
  · exact candidateIdeal.zero_mem

def node6260 : WordRow := [([2, 2, 14, 17], 1), ([2, 8, 10, 17], 2)]

def node6260Raw : WordRow := multiplyRow 17 node0839

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6260_check :
    collect (scaleRow 1 node6260Raw ++ scaleRow (-(1 : ℤ)) node6260 ++
      ([])) = [] := by
  decide +kernel

theorem node6260_mem : rowEval varIndex node6260 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6260Raw node6260 ([])
    (1) (1) (by decide) node6260_check
  · rw [node6260Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0839_mem
  · exact candidateIdeal.zero_mem

def node6274 : WordRow := [([0, 8, 10, 12], 1), ([2, 4, 6, 14], 1)]

def node6274Raw : WordRow := multiplyRow 6 node0842

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6274_check :
    collect (scaleRow 1 node6274Raw ++ scaleRow (-(-2 : ℤ)) node6274 ++
      (scaleRow (-1) node6215)) = [] := by
  decide +kernel

theorem node6274_mem : rowEval varIndex node6274 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6274Raw node6274 (scaleRow (-1) node6215)
    (1) (-2) (by decide) node6274_check
  · rw [node6274Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0842_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node6215 node6215_mem)

def node6279 : WordRow := [([8, 8, 10, 13], 1), ([8, 8, 11, 12], 1), ([8, 9, 10, 12], 4)]

def node6279Raw : WordRow := multiplyRow 15 node0842

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6279_check :
    collect (scaleRow 1 node6279Raw ++ scaleRow (-(1 : ℤ)) node6279 ++
      (scaleRow (-2) node4020 ++ scaleRow (1) node5412 ++ scaleRow (2) node4796 ++ scaleRow (1) node5058 ++ scaleRow (2) node4824 ++ scaleRow (-2) node5621 ++ scaleRow (-1) node3461 ++ scaleRow (-2) node5420 ++ scaleRow (2) node5094 ++ scaleRow (-2) node5542 ++ scaleRow (-1) node3836 ++ scaleRow (-2) node5428 ++ scaleRow (1) node5235 ++ scaleRow (-1) node4644 ++ scaleRow (-2) node5436)) = [] := by
  decide +kernel

theorem node6279_mem : rowEval varIndex node6279 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6279Raw node6279 (scaleRow (-2) node4020 ++ scaleRow (1) node5412 ++ scaleRow (2) node4796 ++ scaleRow (1) node5058 ++ scaleRow (2) node4824 ++ scaleRow (-2) node5621 ++ scaleRow (-1) node3461 ++ scaleRow (-2) node5420 ++ scaleRow (2) node5094 ++ scaleRow (-2) node5542 ++ scaleRow (-1) node3836 ++ scaleRow (-2) node5428 ++ scaleRow (1) node5235 ++ scaleRow (-1) node4644 ++ scaleRow (-2) node5436)
    (1) (1) (by decide) node6279_check
  · rw [node6279Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0842_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4020 node4020_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5412 node5412_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4796 node4796_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5058 node5058_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4824 node4824_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5621 node5621_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3461 node3461_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5420 node5420_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5094 node5094_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5542 node5542_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3836 node3836_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5428 node5428_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5235 node5235_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4644 node4644_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5436 node5436_mem)))))))))))))))

def node6281 : WordRow := [([0, 8, 14, 17], 2), ([2, 4, 14, 17], -2), ([2, 8, 12, 17], -2), ([4, 8, 10, 17], -2), ([6, 8, 8, 17], -1)]

def node6281Raw : WordRow := multiplyRow 17 node0842

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6281_check :
    collect (scaleRow 1 node6281Raw ++ scaleRow (-(1 : ℤ)) node6281 ++
      ([])) = [] := by
  decide +kernel

theorem node6281_mem : rowEval varIndex node6281 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6281Raw node6281 ([])
    (1) (1) (by decide) node6281_check
  · rw [node6281Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0842_mem
  · exact candidateIdeal.zero_mem

def node6287 : WordRow := [([8, 10, 10, 13], 1), ([8, 10, 11, 12], 4), ([9, 10, 10, 12], 1)]

def node6287Raw : WordRow := multiplyRow 15 node0843

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6287_check :
    collect (scaleRow 1 node6287Raw ++ scaleRow (-(1 : ℤ)) node6287 ++
      (scaleRow (-2) node4037 ++ scaleRow (1) node5530 ++ scaleRow (2) node4813 ++ scaleRow (1) node5202 ++ scaleRow (2) node4839 ++ scaleRow (-2) node5622 ++ scaleRow (-1) node3677 ++ scaleRow (-2) node5536 ++ scaleRow (1) node5107 ++ scaleRow (-1) node4945 ++ scaleRow (-2) node5543 ++ scaleRow (2) node5236 ++ scaleRow (-1) node4204 ++ scaleRow (-2) node5437 ++ scaleRow (-2) node5553)) = [] := by
  decide +kernel

theorem node6287_mem : rowEval varIndex node6287 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6287Raw node6287 (scaleRow (-2) node4037 ++ scaleRow (1) node5530 ++ scaleRow (2) node4813 ++ scaleRow (1) node5202 ++ scaleRow (2) node4839 ++ scaleRow (-2) node5622 ++ scaleRow (-1) node3677 ++ scaleRow (-2) node5536 ++ scaleRow (1) node5107 ++ scaleRow (-1) node4945 ++ scaleRow (-2) node5543 ++ scaleRow (2) node5236 ++ scaleRow (-1) node4204 ++ scaleRow (-2) node5437 ++ scaleRow (-2) node5553)
    (1) (1) (by decide) node6287_check
  · rw [node6287Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0843_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4037 node4037_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5530 node5530_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4813 node4813_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5202 node5202_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4839 node4839_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5622 node5622_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3677 node3677_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5536 node5536_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5107 node5107_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4945 node4945_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5543 node5543_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5236 node5236_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4204 node4204_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5437 node5437_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5553 node5553_mem)))))))))))))))

def node6289 : WordRow := [([0, 10, 14, 17], 2), ([2, 6, 14, 17], -2), ([2, 10, 12, 17], -2), ([4, 10, 10, 17], -1), ([6, 8, 10, 17], -2)]

def node6289Raw : WordRow := multiplyRow 17 node0843

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6289_check :
    collect (scaleRow 1 node6289Raw ++ scaleRow (-(1 : ℤ)) node6289 ++
      ([])) = [] := by
  decide +kernel

theorem node6289_mem : rowEval varIndex node6289 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6289Raw node6289 ([])
    (1) (1) (by decide) node6289_check
  · rw [node6289Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0843_mem
  · exact candidateIdeal.zero_mem

def node6301 : WordRow := [([4, 4, 14, 17], 1), ([4, 8, 12, 17], 2)]

def node6301Raw : WordRow := multiplyRow 17 node0845

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6301_check :
    collect (scaleRow 1 node6301Raw ++ scaleRow (-(1 : ℤ)) node6301 ++
      ([])) = [] := by
  decide +kernel

theorem node6301_mem : rowEval varIndex node6301 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6301Raw node6301 ([])
    (1) (1) (by decide) node6301_check
  · rw [node6301Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0845_mem
  · exact candidateIdeal.zero_mem

def node6307 : WordRow := [([8, 11, 12, 12], 1), ([9, 10, 12, 12], 1)]

def node6307Raw : WordRow := multiplyRow 15 node0846

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6307_check :
    collect (scaleRow 1 node6307Raw ++ scaleRow (-(1 : ℤ)) node6307 ++
      (scaleRow (-2) node4050 ++ scaleRow (1) node5617 ++ scaleRow (1) node4852 ++ scaleRow (-1) node5327 ++ scaleRow (-2) node5623 ++ scaleRow (2) node5085 ++ scaleRow (1) node5219 ++ scaleRow (2) node5108 ++ scaleRow (-1) node4387 ++ scaleRow (-2) node5544 ++ scaleRow (-2) node5631 ++ scaleRow (2) node5238 ++ scaleRow (-1) node4526 ++ scaleRow (-2) node5439 ++ scaleRow (-2) node5636 ++ scaleRow (-4) node5350)) = [] := by
  decide +kernel

theorem node6307_mem : rowEval varIndex node6307 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6307Raw node6307 (scaleRow (-2) node4050 ++ scaleRow (1) node5617 ++ scaleRow (1) node4852 ++ scaleRow (-1) node5327 ++ scaleRow (-2) node5623 ++ scaleRow (2) node5085 ++ scaleRow (1) node5219 ++ scaleRow (2) node5108 ++ scaleRow (-1) node4387 ++ scaleRow (-2) node5544 ++ scaleRow (-2) node5631 ++ scaleRow (2) node5238 ++ scaleRow (-1) node4526 ++ scaleRow (-2) node5439 ++ scaleRow (-2) node5636 ++ scaleRow (-4) node5350)
    (1) (1) (by decide) node6307_check
  · rw [node6307Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0846_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4050 node4050_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5617 node5617_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4852 node4852_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5327 node5327_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5623 node5623_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5085 node5085_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5219 node5219_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5108 node5108_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4387 node4387_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5544 node5544_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5631 node5631_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5238 node5238_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4526 node4526_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5439 node5439_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5636 node5636_mem) (rowEval_scale_mem varIndex candidateIdeal (-4) node5350 node5350_mem))))))))))))))))

def node6309 : WordRow := [([0, 12, 14, 17], 2), ([2, 12, 12, 17], -1), ([4, 6, 14, 17], -2), ([4, 10, 12, 17], -2), ([6, 8, 12, 17], -2)]

def node6309Raw : WordRow := multiplyRow 17 node0846

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6309_check :
    collect (scaleRow 1 node6309Raw ++ scaleRow (-(1 : ℤ)) node6309 ++
      ([])) = [] := by
  decide +kernel

theorem node6309_mem : rowEval varIndex node6309 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6309Raw node6309 ([])
    (1) (1) (by decide) node6309_check
  · rw [node6309Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0846_mem
  · exact candidateIdeal.zero_mem

def node6314 : WordRow := [([6, 6, 14, 17], 1), ([6, 10, 12, 17], 2)]

def node6314Raw : WordRow := multiplyRow 17 node0847

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6314_check :
    collect (scaleRow 1 node6314Raw ++ scaleRow (-(1 : ℤ)) node6314 ++
      ([])) = [] := by
  decide +kernel

theorem node6314_mem : rowEval varIndex node6314 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6314Raw node6314 ([])
    (1) (1) (by decide) node6314_check
  · rw [node6314Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0847_mem
  · exact candidateIdeal.zero_mem

def node6338 : WordRow := [([2, 8, 14, 17], 2), ([8, 8, 10, 17], 1)]

def node6338Raw : WordRow := multiplyRow 17 node0851

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6338_check :
    collect (scaleRow 1 node6338Raw ++ scaleRow (-(1 : ℤ)) node6338 ++
      ([])) = [] := by
  decide +kernel

theorem node6338_mem : rowEval varIndex node6338 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6338Raw node6338 ([])
    (1) (1) (by decide) node6338_check
  · rw [node6338Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0851_mem
  · exact candidateIdeal.zero_mem

def node6344 : WordRow := [([2, 10, 14, 17], 2), ([8, 10, 10, 17], 1)]

def node6344Raw : WordRow := multiplyRow 17 node0852

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6344_check :
    collect (scaleRow 1 node6344Raw ++ scaleRow (-(1 : ℤ)) node6344 ++
      ([])) = [] := by
  decide +kernel

theorem node6344_mem : rowEval varIndex node6344 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6344Raw node6344 ([])
    (1) (1) (by decide) node6344_check
  · rw [node6344Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0852_mem
  · exact candidateIdeal.zero_mem

def node6355 : WordRow := [([4, 8, 14, 17], 2), ([8, 8, 12, 17], 1)]

def node6355Raw : WordRow := multiplyRow 17 node0854

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6355_check :
    collect (scaleRow 1 node6355Raw ++ scaleRow (-(1 : ℤ)) node6355 ++
      ([])) = [] := by
  decide +kernel

theorem node6355_mem : rowEval varIndex node6355 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6355Raw node6355 ([])
    (1) (1) (by decide) node6355_check
  · rw [node6355Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0854_mem
  · exact candidateIdeal.zero_mem

def node6361 : WordRow := [([9, 10, 12, 14], 1)]

def node6361Raw : WordRow := multiplyRow 15 node0855

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6361_check :
    collect (scaleRow 1 node6361Raw ++ scaleRow (-(2 : ℤ)) node6361 ++
      (scaleRow (-1) node4059 ++ scaleRow (1) node5686 ++ scaleRow (2) node4854 ++ scaleRow (-2) node5689 ++ scaleRow (2) node5110 ++ scaleRow (-2) node5693 ++ scaleRow (2) node5240 ++ scaleRow (-2) node5697 ++ scaleRow (2) node5457)) = [] := by
  decide +kernel

theorem node6361_mem : rowEval varIndex node6361 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6361Raw node6361 (scaleRow (-1) node4059 ++ scaleRow (1) node5686 ++ scaleRow (2) node4854 ++ scaleRow (-2) node5689 ++ scaleRow (2) node5110 ++ scaleRow (-2) node5693 ++ scaleRow (2) node5240 ++ scaleRow (-2) node5697 ++ scaleRow (2) node5457)
    (1) (2) (by decide) node6361_check
  · rw [node6361Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0855_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4059 node4059_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5686 node5686_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4854 node4854_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5689 node5689_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5110 node5110_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5693 node5693_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5240 node5240_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5697 node5697_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5457 node5457_mem)))))))))

def node6363 : WordRow := [([0, 14, 14, 17], 1), ([2, 12, 14, 17], -2), ([4, 10, 14, 17], -2), ([6, 8, 14, 17], -2), ([8, 10, 12, 17], -2)]

def node6363Raw : WordRow := multiplyRow 17 node0855

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6363_check :
    collect (scaleRow 1 node6363Raw ++ scaleRow (-(1 : ℤ)) node6363 ++
      ([])) = [] := by
  decide +kernel

theorem node6363_mem : rowEval varIndex node6363 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6363Raw node6363 ([])
    (1) (1) (by decide) node6363_check
  · rw [node6363Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0855_mem
  · exact candidateIdeal.zero_mem

def node6368 : WordRow := [([6, 10, 14, 17], 2), ([10, 10, 12, 17], 1)]

def node6368Raw : WordRow := multiplyRow 17 node0856

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6368_check :
    collect (scaleRow 1 node6368Raw ++ scaleRow (-(1 : ℤ)) node6368 ++
      ([])) = [] := by
  decide +kernel

theorem node6368_mem : rowEval varIndex node6368 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6368Raw node6368 ([])
    (1) (1) (by decide) node6368_check
  · rw [node6368Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0856_mem
  · exact candidateIdeal.zero_mem

def node6374 : WordRow := [([4, 12, 14, 17], 2), ([8, 12, 12, 17], 1)]

def node6374Raw : WordRow := multiplyRow 17 node0857

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6374_check :
    collect (scaleRow 1 node6374Raw ++ scaleRow (-(1 : ℤ)) node6374 ++
      ([])) = [] := by
  decide +kernel

theorem node6374_mem : rowEval varIndex node6374 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6374Raw node6374 ([])
    (1) (1) (by decide) node6374_check
  · rw [node6374Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0857_mem
  · exact candidateIdeal.zero_mem

def node6379 : WordRow := [([6, 12, 14, 17], 2), ([10, 12, 12, 17], 1)]

def node6379Raw : WordRow := multiplyRow 17 node0858

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6379_check :
    collect (scaleRow 1 node6379Raw ++ scaleRow (-(1 : ℤ)) node6379 ++
      ([])) = [] := by
  decide +kernel

theorem node6379_mem : rowEval varIndex node6379 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6379Raw node6379 ([])
    (1) (1) (by decide) node6379_check
  · rw [node6379Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0858_mem
  · exact candidateIdeal.zero_mem

def node6395 : WordRow := [([2, 14, 14, 17], 1), ([8, 10, 14, 17], 2)]

def node6395Raw : WordRow := multiplyRow 17 node0861

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6395_check :
    collect (scaleRow 1 node6395Raw ++ scaleRow (-(1 : ℤ)) node6395 ++
      ([])) = [] := by
  decide +kernel

theorem node6395_mem : rowEval varIndex node6395 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6395Raw node6395 ([])
    (1) (1) (by decide) node6395_check
  · rw [node6395Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0861_mem
  · exact candidateIdeal.zero_mem

def node6405 : WordRow := [([4, 14, 14, 17], 1), ([8, 12, 14, 17], 2)]

def node6405Raw : WordRow := multiplyRow 17 node0863

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6405_check :
    collect (scaleRow 1 node6405Raw ++ scaleRow (-(1 : ℤ)) node6405 ++
      ([])) = [] := by
  decide +kernel

theorem node6405_mem : rowEval varIndex node6405 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6405Raw node6405 ([])
    (1) (1) (by decide) node6405_check
  · rw [node6405Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0863_mem
  · exact candidateIdeal.zero_mem

def node6406 : WordRow := [([6, 8, 14, 14], 1), ([8, 10, 12, 14], 2)]

def node6406Raw : WordRow := multiplyRow 8 node0864

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6406_check :
    collect (scaleRow 1 node6406Raw ++ scaleRow (-(1 : ℤ)) node6406 ++
      ([])) = [] := by
  decide +kernel

theorem node6406_mem : rowEval varIndex node6406 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6406Raw node6406 ([])
    (1) (1) (by decide) node6406_check
  · rw [node6406Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0864_mem
  · exact candidateIdeal.zero_mem

def node6410 : WordRow := [([6, 14, 14, 17], 1), ([10, 12, 14, 17], 2)]

def node6410Raw : WordRow := multiplyRow 17 node0864

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6410_check :
    collect (scaleRow 1 node6410Raw ++ scaleRow (-(1 : ℤ)) node6410 ++
      ([])) = [] := by
  decide +kernel

theorem node6410_mem : rowEval varIndex node6410 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6410Raw node6410 ([])
    (1) (1) (by decide) node6410_check
  · rw [node6410Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0864_mem
  · exact candidateIdeal.zero_mem

def node6414 : WordRow := [([8, 10, 12, 14], 1)]

def node6414Raw : WordRow := multiplyRow 6 node0866

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6414_check :
    collect (scaleRow 1 node6414Raw ++ scaleRow (-(-2 : ℤ)) node6414 ++
      (scaleRow (-1) node6406)) = [] := by
  decide +kernel

theorem node6414_mem : rowEval varIndex node6414 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6414Raw node6414 (scaleRow (-1) node6406)
    (1) (-2) (by decide) node6414_check
  · rw [node6414Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0866_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node6406 node6406_mem)

def node6430 : WordRow := [([16, 16, 16, 17], 1)]

def node6430Raw : WordRow := [(seedWords 4,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6430_check :
    collect (scaleRow 1 node6430Raw ++ scaleRow (-(1 : ℤ)) node6430 ++
      ([])) = [] := by
  decide +kernel

theorem node6430_mem : rowEval varIndex node6430 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6430Raw node6430 ([])
    (1) (1) (by decide) node6430_check
  · exact seedWord_mem 4
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node6430_mem
