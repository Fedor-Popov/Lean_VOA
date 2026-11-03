import VOA.DeligneAudit.D4FusionContactM2Dag11

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node4001 : WordRow := [([0, 6, 14, 15], 1), ([1, 6, 14, 14], 1), ([2, 6, 13, 14], -1), ([3, 6, 12, 14], -1), ([4, 6, 11, 14], -1), ([5, 6, 10, 14], -1), ([6, 6, 9, 14], -1), ([6, 7, 8, 14], -1)]

def node4001Raw : WordRow := multiplyRow 14 node0450

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4001_check :
    collect (scaleRow 1 node4001Raw ++ scaleRow (-(1 : ℤ)) node4001 ++
      ([])) = [] := by
  decide +kernel

theorem node4001_mem : rowEval varIndex node4001 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4001Raw node4001 ([])
    (1) (1) (by decide) node4001_check
  · rw [node4001Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0450_mem
  · exact candidateIdeal.zero_mem

def node4003 : WordRow := [([0, 6, 15, 16], 1), ([1, 6, 14, 16], 1), ([2, 6, 13, 16], -1), ([3, 6, 12, 16], -1), ([4, 6, 11, 16], -1), ([5, 6, 10, 16], -1), ([6, 6, 9, 16], -1), ([6, 7, 8, 16], -1)]

def node4003Raw : WordRow := multiplyRow 16 node0450

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4003_check :
    collect (scaleRow 1 node4003Raw ++ scaleRow (-(1 : ℤ)) node4003 ++
      ([])) = [] := by
  decide +kernel

theorem node4003_mem : rowEval varIndex node4003 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4003Raw node4003 ([])
    (1) (1) (by decide) node4003_check
  · rw [node4003Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0450_mem
  · exact candidateIdeal.zero_mem

def node4016 : WordRow := [([0, 8, 10, 15], 1), ([1, 8, 10, 14], 1), ([2, 8, 10, 13], -1), ([3, 8, 10, 12], -1), ([4, 8, 10, 11], -1), ([5, 8, 10, 10], -1), ([6, 8, 9, 10], -1), ([7, 8, 8, 10], -1)]

def node4016Raw : WordRow := multiplyRow 10 node0452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4016_check :
    collect (scaleRow 1 node4016Raw ++ scaleRow (-(1 : ℤ)) node4016 ++
      ([])) = [] := by
  decide +kernel

theorem node4016_mem : rowEval varIndex node4016 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4016Raw node4016 ([])
    (1) (1) (by decide) node4016_check
  · rw [node4016Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0452_mem
  · exact candidateIdeal.zero_mem

def node4018 : WordRow := [([0, 8, 12, 15], 1), ([1, 8, 12, 14], 1), ([2, 8, 12, 13], -1), ([3, 8, 12, 12], -1), ([4, 8, 11, 12], -1), ([5, 8, 10, 12], -1), ([6, 8, 9, 12], -1), ([7, 8, 8, 12], -1)]

def node4018Raw : WordRow := multiplyRow 12 node0452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4018_check :
    collect (scaleRow 1 node4018Raw ++ scaleRow (-(1 : ℤ)) node4018 ++
      ([])) = [] := by
  decide +kernel

theorem node4018_mem : rowEval varIndex node4018 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4018Raw node4018 ([])
    (1) (1) (by decide) node4018_check
  · rw [node4018Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0452_mem
  · exact candidateIdeal.zero_mem

def node4019 : WordRow := [([1, 8, 12, 15], 1), ([1, 8, 13, 14], -1), ([2, 8, 13, 13], 1), ([3, 8, 12, 13], 1), ([4, 7, 8, 15], -1), ([4, 8, 11, 13], 1), ([5, 6, 8, 15], -1), ([5, 8, 10, 13], 1), ([6, 8, 9, 13], 1), ([7, 8, 8, 13], 1)]

def node4019Raw : WordRow := multiplyRow 13 node0452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4019_check :
    collect (scaleRow 1 node4019Raw ++ scaleRow (-(-1 : ℤ)) node4019 ++
      (scaleRow (-1) node3028)) = [] := by
  decide +kernel

theorem node4019_mem : rowEval varIndex node4019 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4019Raw node4019 (scaleRow (-1) node3028)
    (1) (-1) (by decide) node4019_check
  · rw [node4019Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0452_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node3028 node3028_mem)

def node4020 : WordRow := [([0, 8, 14, 15], 1), ([1, 8, 14, 14], 1), ([2, 8, 13, 14], -1), ([3, 8, 12, 14], -1), ([4, 8, 11, 14], -1), ([5, 8, 10, 14], -1), ([6, 8, 9, 14], -1), ([7, 8, 8, 14], -1)]

def node4020Raw : WordRow := multiplyRow 14 node0452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4020_check :
    collect (scaleRow 1 node4020Raw ++ scaleRow (-(1 : ℤ)) node4020 ++
      ([])) = [] := by
  decide +kernel

theorem node4020_mem : rowEval varIndex node4020 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4020Raw node4020 ([])
    (1) (1) (by decide) node4020_check
  · rw [node4020Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0452_mem
  · exact candidateIdeal.zero_mem

def node4022 : WordRow := [([0, 8, 15, 16], 1), ([1, 8, 14, 16], 1), ([2, 8, 13, 16], -1), ([3, 8, 12, 16], -1), ([4, 8, 11, 16], -1), ([5, 8, 10, 16], -1), ([6, 8, 9, 16], -1), ([7, 8, 8, 16], -1)]

def node4022Raw : WordRow := multiplyRow 16 node0452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4022_check :
    collect (scaleRow 1 node4022Raw ++ scaleRow (-(1 : ℤ)) node4022 ++
      ([])) = [] := by
  decide +kernel

theorem node4022_mem : rowEval varIndex node4022 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4022Raw node4022 ([])
    (1) (1) (by decide) node4022_check
  · rw [node4022Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0452_mem
  · exact candidateIdeal.zero_mem

def node4027 : WordRow := [([2, 5, 12, 15], 1), ([2, 5, 13, 14], -1), ([2, 8, 13, 13], 1), ([2, 9, 12, 13], -1), ([3, 4, 12, 15], 1), ([3, 4, 13, 14], -1), ([3, 8, 12, 13], 1), ([3, 9, 12, 12], -1), ([4, 7, 8, 15], -1), ([4, 7, 9, 14], 1), ([4, 8, 11, 13], 1), ([4, 9, 11, 12], -1), ([5, 6, 8, 15], -1), ([5, 6, 9, 14], 1), ([5, 8, 10, 13], 1), ([5, 9, 10, 12], -1), ([6, 8, 9, 13], 1), ([6, 9, 9, 12], -1), ([7, 8, 8, 13], 1), ([7, 8, 9, 12], -1)]

def node4027Raw : WordRow := multiplyRow 12 node0453

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4027_check :
    collect (scaleRow 1 node4027Raw ++ scaleRow (-(-1 : ℤ)) node4027 ++
      (scaleRow (-1) node4019 ++ scaleRow (-1) node3036)) = [] := by
  decide +kernel

theorem node4027_mem : rowEval varIndex node4027 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4027Raw node4027 (scaleRow (-1) node4019 ++ scaleRow (-1) node3036)
    (1) (-1) (by decide) node4027_check
  · rw [node4027Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0453_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4019 node4019_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3036 node3036_mem))

def node4035 : WordRow := [([0, 10, 12, 15], 1), ([1, 10, 12, 14], 1), ([2, 10, 12, 13], -1), ([3, 10, 12, 12], -1), ([4, 10, 11, 12], -1), ([5, 10, 10, 12], -1), ([6, 9, 10, 12], -1), ([7, 8, 10, 12], -1)]

def node4035Raw : WordRow := multiplyRow 12 node0454

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4035_check :
    collect (scaleRow 1 node4035Raw ++ scaleRow (-(1 : ℤ)) node4035 ++
      ([])) = [] := by
  decide +kernel

theorem node4035_mem : rowEval varIndex node4035 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4035Raw node4035 ([])
    (1) (1) (by decide) node4035_check
  · rw [node4035Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0454_mem
  · exact candidateIdeal.zero_mem

def node4037 : WordRow := [([0, 10, 14, 15], 1), ([1, 10, 14, 14], 1), ([2, 10, 13, 14], -1), ([3, 10, 12, 14], -1), ([4, 10, 11, 14], -1), ([5, 10, 10, 14], -1), ([6, 9, 10, 14], -1), ([7, 8, 10, 14], -1)]

def node4037Raw : WordRow := multiplyRow 14 node0454

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4037_check :
    collect (scaleRow 1 node4037Raw ++ scaleRow (-(1 : ℤ)) node4037 ++
      ([])) = [] := by
  decide +kernel

theorem node4037_mem : rowEval varIndex node4037 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4037Raw node4037 ([])
    (1) (1) (by decide) node4037_check
  · rw [node4037Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0454_mem
  · exact candidateIdeal.zero_mem

def node4039 : WordRow := [([0, 10, 15, 16], 1), ([1, 10, 14, 16], 1), ([2, 10, 13, 16], -1), ([3, 10, 12, 16], -1), ([4, 10, 11, 16], -1), ([5, 10, 10, 16], -1), ([6, 9, 10, 16], -1), ([7, 8, 10, 16], -1)]

def node4039Raw : WordRow := multiplyRow 16 node0454

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4039_check :
    collect (scaleRow 1 node4039Raw ++ scaleRow (-(1 : ℤ)) node4039 ++
      ([])) = [] := by
  decide +kernel

theorem node4039_mem : rowEval varIndex node4039 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4039Raw node4039 ([])
    (1) (1) (by decide) node4039_check
  · rw [node4039Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0454_mem
  · exact candidateIdeal.zero_mem

def node4050 : WordRow := [([0, 12, 14, 15], 1), ([1, 12, 14, 14], 1), ([2, 12, 13, 14], -1), ([3, 12, 12, 14], -1), ([4, 11, 12, 14], -1), ([5, 10, 12, 14], -1), ([6, 9, 12, 14], -1), ([7, 8, 12, 14], -1)]

def node4050Raw : WordRow := multiplyRow 14 node0456

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4050_check :
    collect (scaleRow 1 node4050Raw ++ scaleRow (-(1 : ℤ)) node4050 ++
      ([])) = [] := by
  decide +kernel

theorem node4050_mem : rowEval varIndex node4050 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4050Raw node4050 ([])
    (1) (1) (by decide) node4050_check
  · rw [node4050Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0456_mem
  · exact candidateIdeal.zero_mem

def node4052 : WordRow := [([0, 12, 15, 16], 1), ([1, 12, 14, 16], 1), ([2, 12, 13, 16], -1), ([3, 12, 12, 16], -1), ([4, 11, 12, 16], -1), ([5, 10, 12, 16], -1), ([6, 9, 12, 16], -1), ([7, 8, 12, 16], -1)]

def node4052Raw : WordRow := multiplyRow 16 node0456

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4052_check :
    collect (scaleRow 1 node4052Raw ++ scaleRow (-(1 : ℤ)) node4052 ++
      ([])) = [] := by
  decide +kernel

theorem node4052_mem : rowEval varIndex node4052 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4052Raw node4052 ([])
    (1) (1) (by decide) node4052_check
  · rw [node4052Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0456_mem
  · exact candidateIdeal.zero_mem

def node4059 : WordRow := [([0, 14, 14, 15], 1), ([1, 14, 14, 14], 1), ([2, 13, 14, 14], -1), ([3, 12, 14, 14], -1), ([4, 11, 14, 14], -1), ([5, 10, 14, 14], -1), ([6, 9, 14, 14], -1), ([7, 8, 14, 14], -1)]

def node4059Raw : WordRow := multiplyRow 14 node0458

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4059_check :
    collect (scaleRow 1 node4059Raw ++ scaleRow (-(1 : ℤ)) node4059 ++
      ([])) = [] := by
  decide +kernel

theorem node4059_mem : rowEval varIndex node4059 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4059Raw node4059 ([])
    (1) (1) (by decide) node4059_check
  · rw [node4059Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0458_mem
  · exact candidateIdeal.zero_mem

def node4061 : WordRow := [([0, 14, 15, 16], 1), ([1, 14, 14, 16], 1), ([2, 13, 14, 16], -1), ([3, 12, 14, 16], -1), ([4, 11, 14, 16], -1), ([5, 10, 14, 16], -1), ([6, 9, 14, 16], -1), ([7, 8, 14, 16], -1)]

def node4061Raw : WordRow := multiplyRow 16 node0458

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4061_check :
    collect (scaleRow 1 node4061Raw ++ scaleRow (-(1 : ℤ)) node4061 ++
      ([])) = [] := by
  decide +kernel

theorem node4061_mem : rowEval varIndex node4061 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4061Raw node4061 ([])
    (1) (1) (by decide) node4061_check
  · rw [node4061Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0458_mem
  · exact candidateIdeal.zero_mem

def node4067 : WordRow := [([0, 15, 16, 17], 1), ([1, 14, 16, 17], 1), ([2, 13, 16, 17], -1), ([3, 12, 16, 17], -1), ([4, 11, 16, 17], -1), ([5, 10, 16, 17], -1), ([6, 9, 16, 17], -1), ([7, 8, 16, 17], -1)]

def node4067Raw : WordRow := multiplyRow 17 node0460

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4067_check :
    collect (scaleRow 1 node4067Raw ++ scaleRow (-(1 : ℤ)) node4067 ++
      ([])) = [] := by
  decide +kernel

theorem node4067_mem : rowEval varIndex node4067 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4067Raw node4067 ([])
    (1) (1) (by decide) node4067_check
  · rw [node4067Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0460_mem
  · exact candidateIdeal.zero_mem

def node4090 : WordRow := [([2, 8, 13, 13], 1), ([3, 8, 12, 13], 2), ([4, 7, 8, 15], -1), ([4, 8, 11, 13], 1), ([5, 6, 8, 15], -1), ([5, 7, 8, 14], -1), ([5, 8, 10, 13], 1), ([5, 8, 11, 12], 1), ([6, 8, 9, 13], 1), ([7, 8, 8, 13], 1), ([7, 8, 9, 12], 1)]

def node4090Raw : WordRow := multiplyRow 12 node0464

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4090_check :
    collect (scaleRow 1 node4090Raw ++ scaleRow (-(-1 : ℤ)) node4090 ++
      (scaleRow (-1) node4027 ++ scaleRow (-1) node3105)) = [] := by
  decide +kernel

theorem node4090_mem : rowEval varIndex node4090 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4090Raw node4090 (scaleRow (-1) node4027 ++ scaleRow (-1) node3105)
    (1) (-1) (by decide) node4090_check
  · rw [node4090Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0464_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4027 node4027_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3105 node3105_mem))

def node4141 : WordRow := [([1, 4, 6, 10], 2), ([2, 4, 6, 7], -1), ([3, 4, 6, 6], -1)]

def node4141Raw : WordRow := multiplyRow 4 node0474

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4141_check :
    collect (scaleRow 1 node4141Raw ++ scaleRow (-(1 : ℤ)) node4141 ++
      ([])) = [] := by
  decide +kernel

theorem node4141_mem : rowEval varIndex node4141 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4141Raw node4141 ([])
    (1) (1) (by decide) node4141_check
  · rw [node4141Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0474_mem
  · exact candidateIdeal.zero_mem

def node4143 : WordRow := [([1, 6, 8, 10], 2), ([2, 6, 7, 8], -1), ([3, 6, 6, 8], -1)]

def node4143Raw : WordRow := multiplyRow 8 node0474

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4143_check :
    collect (scaleRow 1 node4143Raw ++ scaleRow (-(1 : ℤ)) node4143 ++
      ([])) = [] := by
  decide +kernel

theorem node4143_mem : rowEval varIndex node4143 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4143Raw node4143 ([])
    (1) (1) (by decide) node4143_check
  · rw [node4143Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0474_mem
  · exact candidateIdeal.zero_mem

def node4144 : WordRow := [([3, 5, 6, 10], 2), ([3, 6, 6, 9], -1)]

def node4144Raw : WordRow := multiplyRow 9 node0474

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4144_check :
    collect (scaleRow 1 node4144Raw ++ scaleRow (-(1 : ℤ)) node4144 ++
      (scaleRow (-2) node2316 ++ scaleRow (-2) node1911 ++ scaleRow (2) node2410 ++ scaleRow (1) node3171)) = [] := by
  decide +kernel

theorem node4144_mem : rowEval varIndex node4144 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4144Raw node4144 (scaleRow (-2) node2316 ++ scaleRow (-2) node1911 ++ scaleRow (2) node2410 ++ scaleRow (1) node3171)
    (1) (1) (by decide) node4144_check
  · rw [node4144Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0474_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2316 node2316_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1911 node1911_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2410 node2410_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3171 node3171_mem))))

def node4149 : WordRow := [([1, 6, 10, 16], 2), ([2, 6, 7, 16], -1), ([3, 6, 6, 16], -1)]

def node4149Raw : WordRow := multiplyRow 16 node0474

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4149_check :
    collect (scaleRow 1 node4149Raw ++ scaleRow (-(1 : ℤ)) node4149 ++
      ([])) = [] := by
  decide +kernel

theorem node4149_mem : rowEval varIndex node4149 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4149Raw node4149 ([])
    (1) (1) (by decide) node4149_check
  · rw [node4149Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0474_mem
  · exact candidateIdeal.zero_mem

def node4163 : WordRow := [([2, 7, 10, 17], 1), ([3, 6, 10, 17], -1)]

def node4163Raw : WordRow := multiplyRow 17 node0475

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4163_check :
    collect (scaleRow 1 node4163Raw ++ scaleRow (-(1 : ℤ)) node4163 ++
      ([])) = [] := by
  decide +kernel

theorem node4163_mem : rowEval varIndex node4163 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4163Raw node4163 ([])
    (1) (1) (by decide) node4163_check
  · rw [node4163Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0475_mem
  · exact candidateIdeal.zero_mem

def node4177 : WordRow := [([4, 6, 11, 14], 1), ([4, 7, 10, 14], 1)]

def node4177Raw : WordRow := multiplyRow 14 node0477

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4177_check :
    collect (scaleRow 1 node4177Raw ++ scaleRow (-(1 : ℤ)) node4177 ++
      ([])) = [] := by
  decide +kernel

theorem node4177_mem : rowEval varIndex node4177 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4177Raw node4177 ([])
    (1) (1) (by decide) node4177_check
  · rw [node4177Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0477_mem
  · exact candidateIdeal.zero_mem

def node4179 : WordRow := [([4, 6, 11, 16], 1), ([4, 7, 10, 16], 1)]

def node4179Raw : WordRow := multiplyRow 16 node0477

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4179_check :
    collect (scaleRow 1 node4179Raw ++ scaleRow (-(1 : ℤ)) node4179 ++
      ([])) = [] := by
  decide +kernel

theorem node4179_mem : rowEval varIndex node4179 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4179Raw node4179 ([])
    (1) (1) (by decide) node4179_check
  · rw [node4179Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0477_mem
  · exact candidateIdeal.zero_mem

def node4180 : WordRow := [([4, 6, 11, 17], 1), ([4, 7, 10, 17], 1)]

def node4180Raw : WordRow := multiplyRow 17 node0477

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4180_check :
    collect (scaleRow 1 node4180Raw ++ scaleRow (-(1 : ℤ)) node4180 ++
      ([])) = [] := by
  decide +kernel

theorem node4180_mem : rowEval varIndex node4180 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4180Raw node4180 ([])
    (1) (1) (by decide) node4180_check
  · rw [node4180Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0477_mem
  · exact candidateIdeal.zero_mem

def node4202 : WordRow := [([6, 8, 11, 12], 1), ([7, 8, 10, 12], 1)]

def node4202Raw : WordRow := multiplyRow 12 node0480

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4202_check :
    collect (scaleRow 1 node4202Raw ++ scaleRow (-(1 : ℤ)) node4202 ++
      ([])) = [] := by
  decide +kernel

theorem node4202_mem : rowEval varIndex node4202 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4202Raw node4202 ([])
    (1) (1) (by decide) node4202_check
  · rw [node4202Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0480_mem
  · exact candidateIdeal.zero_mem

def node4203 : WordRow := [([6, 8, 11, 13], 1), ([7, 8, 10, 13], 1)]

def node4203Raw : WordRow := multiplyRow 13 node0480

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4203_check :
    collect (scaleRow 1 node4203Raw ++ scaleRow (-(1 : ℤ)) node4203 ++
      ([])) = [] := by
  decide +kernel

theorem node4203_mem : rowEval varIndex node4203 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4203Raw node4203 ([])
    (1) (1) (by decide) node4203_check
  · rw [node4203Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0480_mem
  · exact candidateIdeal.zero_mem

def node4204 : WordRow := [([6, 8, 11, 14], 1), ([7, 8, 10, 14], 1)]

def node4204Raw : WordRow := multiplyRow 14 node0480

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4204_check :
    collect (scaleRow 1 node4204Raw ++ scaleRow (-(1 : ℤ)) node4204 ++
      ([])) = [] := by
  decide +kernel

theorem node4204_mem : rowEval varIndex node4204 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4204Raw node4204 ([])
    (1) (1) (by decide) node4204_check
  · rw [node4204Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0480_mem
  · exact candidateIdeal.zero_mem

def node4207 : WordRow := [([6, 8, 11, 17], 1), ([7, 8, 10, 17], 1)]

def node4207Raw : WordRow := multiplyRow 17 node0480

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4207_check :
    collect (scaleRow 1 node4207Raw ++ scaleRow (-(1 : ℤ)) node4207 ++
      ([])) = [] := by
  decide +kernel

theorem node4207_mem : rowEval varIndex node4207 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4207Raw node4207 ([])
    (1) (1) (by decide) node4207_check
  · rw [node4207Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0480_mem
  · exact candidateIdeal.zero_mem

def node4211 : WordRow := [([6, 9, 11, 12], 1), ([7, 9, 10, 12], 1)]

def node4211Raw : WordRow := multiplyRow 12 node0481

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4211_check :
    collect (scaleRow 1 node4211Raw ++ scaleRow (-(1 : ℤ)) node4211 ++
      ([])) = [] := by
  decide +kernel

theorem node4211_mem : rowEval varIndex node4211 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4211Raw node4211 ([])
    (1) (1) (by decide) node4211_check
  · rw [node4211Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0481_mem
  · exact candidateIdeal.zero_mem

def node4215 : WordRow := [([6, 9, 11, 16], 1), ([7, 9, 10, 16], 1)]

def node4215Raw : WordRow := multiplyRow 16 node0481

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4215_check :
    collect (scaleRow 1 node4215Raw ++ scaleRow (-(1 : ℤ)) node4215 ++
      ([])) = [] := by
  decide +kernel

theorem node4215_mem : rowEval varIndex node4215 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4215Raw node4215 ([])
    (1) (1) (by decide) node4215_check
  · rw [node4215Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0481_mem
  · exact candidateIdeal.zero_mem

def node4237 : WordRow := [([6, 11, 12, 17], 1), ([7, 10, 12, 17], 1)]

def node4237Raw : WordRow := multiplyRow 17 node0484

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4237_check :
    collect (scaleRow 1 node4237Raw ++ scaleRow (-(1 : ℤ)) node4237 ++
      ([])) = [] := by
  decide +kernel

theorem node4237_mem : rowEval varIndex node4237 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4237Raw node4237 ([])
    (1) (1) (by decide) node4237_check
  · rw [node4237Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0484_mem
  · exact candidateIdeal.zero_mem

def node4241 : WordRow := [([6, 11, 13, 16], 1), ([7, 10, 13, 16], 1)]

def node4241Raw : WordRow := multiplyRow 16 node0485

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4241_check :
    collect (scaleRow 1 node4241Raw ++ scaleRow (-(1 : ℤ)) node4241 ++
      ([])) = [] := by
  decide +kernel

theorem node4241_mem : rowEval varIndex node4241 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4241Raw node4241 ([])
    (1) (1) (by decide) node4241_check
  · rw [node4241Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0485_mem
  · exact candidateIdeal.zero_mem

def node4245 : WordRow := [([6, 11, 14, 16], 1), ([7, 10, 14, 16], 1)]

def node4245Raw : WordRow := multiplyRow 16 node0486

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4245_check :
    collect (scaleRow 1 node4245Raw ++ scaleRow (-(1 : ℤ)) node4245 ++
      ([])) = [] := by
  decide +kernel

theorem node4245_mem : rowEval varIndex node4245 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4245Raw node4245 ([])
    (1) (1) (by decide) node4245_check
  · rw [node4245Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0486_mem
  · exact candidateIdeal.zero_mem

def node4251 : WordRow := [([6, 11, 16, 17], 1), ([7, 10, 16, 17], 1)]

def node4251Raw : WordRow := multiplyRow 17 node0488

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4251_check :
    collect (scaleRow 1 node4251Raw ++ scaleRow (-(1 : ℤ)) node4251 ++
      ([])) = [] := by
  decide +kernel

theorem node4251_mem : rowEval varIndex node4251 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4251Raw node4251 ([])
    (1) (1) (by decide) node4251_check
  · rw [node4251Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0488_mem
  · exact candidateIdeal.zero_mem

def node4256 : WordRow := [([7, 8, 11, 12], 1)]

def node4256Raw : WordRow := multiplyRow 12 node0490

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4256_check :
    collect (scaleRow 1 node4256Raw ++ scaleRow (-(1 : ℤ)) node4256 ++
      ([])) = [] := by
  decide +kernel

theorem node4256_mem : rowEval varIndex node4256 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4256Raw node4256 ([])
    (1) (1) (by decide) node4256_check
  · rw [node4256Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0490_mem
  · exact candidateIdeal.zero_mem

def node4306 : WordRow := [([1, 2, 4, 12], 2), ([2, 4, 4, 7], -1), ([2, 4, 5, 6], -1)]

def node4306Raw : WordRow := multiplyRow 2 node0500

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4306_check :
    collect (scaleRow 1 node4306Raw ++ scaleRow (-(1 : ℤ)) node4306 ++
      ([])) = [] := by
  decide +kernel

theorem node4306_mem : rowEval varIndex node4306 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4306Raw node4306 ([])
    (1) (1) (by decide) node4306_check
  · rw [node4306Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0500_mem
  · exact candidateIdeal.zero_mem

def node4310 : WordRow := [([1, 4, 10, 12], 2), ([4, 4, 7, 10], -1), ([4, 5, 6, 10], -1)]

def node4310Raw : WordRow := multiplyRow 10 node0500

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4310_check :
    collect (scaleRow 1 node4310Raw ++ scaleRow (-(1 : ℤ)) node4310 ++
      ([])) = [] := by
  decide +kernel

theorem node4310_mem : rowEval varIndex node4310 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4310Raw node4310 ([])
    (1) (1) (by decide) node4310_check
  · rw [node4310Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0500_mem
  · exact candidateIdeal.zero_mem

def node4316 : WordRow := [([1, 4, 12, 16], 2), ([4, 4, 7, 16], -1), ([4, 5, 6, 16], -1)]

def node4316Raw : WordRow := multiplyRow 16 node0500

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4316_check :
    collect (scaleRow 1 node4316Raw ++ scaleRow (-(1 : ℤ)) node4316 ++
      ([])) = [] := by
  decide +kernel

theorem node4316_mem : rowEval varIndex node4316 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4316Raw node4316 ([])
    (1) (1) (by decide) node4316_check
  · rw [node4316Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0500_mem
  · exact candidateIdeal.zero_mem

def node4318 : WordRow := [([2, 2, 4, 13], 1), ([2, 2, 5, 12], 1)]

def node4318Raw : WordRow := multiplyRow 2 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4318_check :
    collect (scaleRow 1 node4318Raw ++ scaleRow (-(1 : ℤ)) node4318 ++
      ([])) = [] := by
  decide +kernel

theorem node4318_mem : rowEval varIndex node4318 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4318Raw node4318 ([])
    (1) (1) (by decide) node4318_check
  · rw [node4318Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4320 : WordRow := [([2, 4, 6, 13], 1), ([2, 5, 6, 12], 1)]

def node4320Raw : WordRow := multiplyRow 6 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4320_check :
    collect (scaleRow 1 node4320Raw ++ scaleRow (-(1 : ℤ)) node4320 ++
      ([])) = [] := by
  decide +kernel

theorem node4320_mem : rowEval varIndex node4320 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4320Raw node4320 ([])
    (1) (1) (by decide) node4320_check
  · rw [node4320Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4323 : WordRow := [([2, 4, 10, 13], 1), ([2, 5, 10, 12], 1)]

def node4323Raw : WordRow := multiplyRow 10 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4323_check :
    collect (scaleRow 1 node4323Raw ++ scaleRow (-(1 : ℤ)) node4323 ++
      ([])) = [] := by
  decide +kernel

theorem node4323_mem : rowEval varIndex node4323 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4323Raw node4323 ([])
    (1) (1) (by decide) node4323_check
  · rw [node4323Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4324 : WordRow := [([3, 4, 10, 13], 1), ([3, 4, 11, 12], 1), ([3, 5, 10, 12], 1), ([3, 6, 9, 12], -1)]

def node4324Raw : WordRow := multiplyRow 11 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4324_check :
    collect (scaleRow 1 node4324Raw ++ scaleRow (-(-1 : ℤ)) node4324 ++
      (scaleRow (-1) node3608 ++ scaleRow (-1) node2653 ++ scaleRow (-1) node3419)) = [] := by
  decide +kernel

theorem node4324_mem : rowEval varIndex node4324 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4324Raw node4324 (scaleRow (-1) node3608 ++ scaleRow (-1) node2653 ++ scaleRow (-1) node3419)
    (1) (-1) (by decide) node4324_check
  · rw [node4324Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3608 node3608_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2653 node2653_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3419 node3419_mem)))

def node4327 : WordRow := [([2, 4, 13, 14], 1), ([2, 5, 12, 14], 1)]

def node4327Raw : WordRow := multiplyRow 14 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4327_check :
    collect (scaleRow 1 node4327Raw ++ scaleRow (-(1 : ℤ)) node4327 ++
      ([])) = [] := by
  decide +kernel

theorem node4327_mem : rowEval varIndex node4327 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4327Raw node4327 ([])
    (1) (1) (by decide) node4327_check
  · rw [node4327Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4328 : WordRow := [([2, 4, 13, 15], 1), ([2, 5, 12, 15], 1)]

def node4328Raw : WordRow := multiplyRow 15 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4328_check :
    collect (scaleRow 1 node4328Raw ++ scaleRow (-(1 : ℤ)) node4328 ++
      ([])) = [] := by
  decide +kernel

theorem node4328_mem : rowEval varIndex node4328 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4328Raw node4328 ([])
    (1) (1) (by decide) node4328_check
  · rw [node4328Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4329 : WordRow := [([2, 4, 13, 16], 1), ([2, 5, 12, 16], 1)]

def node4329Raw : WordRow := multiplyRow 16 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4329_check :
    collect (scaleRow 1 node4329Raw ++ scaleRow (-(1 : ℤ)) node4329 ++
      ([])) = [] := by
  decide +kernel

theorem node4329_mem : rowEval varIndex node4329 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4329Raw node4329 ([])
    (1) (1) (by decide) node4329_check
  · rw [node4329Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4330 : WordRow := [([2, 4, 13, 17], 1), ([2, 5, 12, 17], 1)]

def node4330Raw : WordRow := multiplyRow 17 node0501

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4330_check :
    collect (scaleRow 1 node4330Raw ++ scaleRow (-(1 : ℤ)) node4330 ++
      ([])) = [] := by
  decide +kernel

theorem node4330_mem : rowEval varIndex node4330 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4330Raw node4330 ([])
    (1) (1) (by decide) node4330_check
  · rw [node4330Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0501_mem
  · exact candidateIdeal.zero_mem

def node4333 : WordRow := [([3, 4, 13, 14], 1), ([3, 5, 12, 14], 1)]

def node4333Raw : WordRow := multiplyRow 14 node0502

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4333_check :
    collect (scaleRow 1 node4333Raw ++ scaleRow (-(1 : ℤ)) node4333 ++
      ([])) = [] := by
  decide +kernel

theorem node4333_mem : rowEval varIndex node4333 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4333Raw node4333 ([])
    (1) (1) (by decide) node4333_check
  · rw [node4333Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0502_mem
  · exact candidateIdeal.zero_mem

def node4367 : WordRow := [([4, 8, 10, 13], 1), ([5, 8, 10, 12], 1)]

def node4367Raw : WordRow := multiplyRow 10 node0506

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4367_check :
    collect (scaleRow 1 node4367Raw ++ scaleRow (-(1 : ℤ)) node4367 ++
      ([])) = [] := by
  decide +kernel

theorem node4367_mem : rowEval varIndex node4367 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4367Raw node4367 ([])
    (1) (1) (by decide) node4367_check
  · rw [node4367Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0506_mem
  · exact candidateIdeal.zero_mem

def node4368 : WordRow := [([4, 8, 11, 13], 1), ([5, 8, 11, 12], 1)]

def node4368Raw : WordRow := multiplyRow 11 node0506

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4368_check :
    collect (scaleRow 1 node4368Raw ++ scaleRow (-(1 : ℤ)) node4368 ++
      ([])) = [] := by
  decide +kernel

theorem node4368_mem : rowEval varIndex node4368 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4368Raw node4368 ([])
    (1) (1) (by decide) node4368_check
  · rw [node4368Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0506_mem
  · exact candidateIdeal.zero_mem

def node4374 : WordRow := [([4, 8, 13, 17], 1), ([5, 8, 12, 17], 1)]

def node4374Raw : WordRow := multiplyRow 17 node0506

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4374_check :
    collect (scaleRow 1 node4374Raw ++ scaleRow (-(1 : ℤ)) node4374 ++
      ([])) = [] := by
  decide +kernel

theorem node4374_mem : rowEval varIndex node4374 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4374Raw node4374 ([])
    (1) (1) (by decide) node4374_check
  · rw [node4374Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0506_mem
  · exact candidateIdeal.zero_mem

def node4383 : WordRow := [([4, 10, 10, 13], 1), ([5, 10, 10, 12], 1)]

def node4383Raw : WordRow := multiplyRow 10 node0508

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4383_check :
    collect (scaleRow 1 node4383Raw ++ scaleRow (-(1 : ℤ)) node4383 ++
      ([])) = [] := by
  decide +kernel

theorem node4383_mem : rowEval varIndex node4383 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4383Raw node4383 ([])
    (1) (1) (by decide) node4383_check
  · rw [node4383Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0508_mem
  · exact candidateIdeal.zero_mem

def node4387 : WordRow := [([4, 10, 13, 14], 1), ([5, 10, 12, 14], 1)]

def node4387Raw : WordRow := multiplyRow 14 node0508

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4387_check :
    collect (scaleRow 1 node4387Raw ++ scaleRow (-(1 : ℤ)) node4387 ++
      ([])) = [] := by
  decide +kernel

theorem node4387_mem : rowEval varIndex node4387 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4387Raw node4387 ([])
    (1) (1) (by decide) node4387_check
  · rw [node4387Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0508_mem
  · exact candidateIdeal.zero_mem

def node4388 : WordRow := [([4, 10, 13, 15], 1), ([5, 10, 12, 15], 1)]

def node4388Raw : WordRow := multiplyRow 15 node0508

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4388_check :
    collect (scaleRow 1 node4388Raw ++ scaleRow (-(1 : ℤ)) node4388 ++
      ([])) = [] := by
  decide +kernel

theorem node4388_mem : rowEval varIndex node4388 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4388Raw node4388 ([])
    (1) (1) (by decide) node4388_check
  · rw [node4388Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0508_mem
  · exact candidateIdeal.zero_mem

def node4389 : WordRow := [([4, 10, 13, 16], 1), ([5, 10, 12, 16], 1)]

def node4389Raw : WordRow := multiplyRow 16 node0508

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4389_check :
    collect (scaleRow 1 node4389Raw ++ scaleRow (-(1 : ℤ)) node4389 ++
      ([])) = [] := by
  decide +kernel

theorem node4389_mem : rowEval varIndex node4389 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4389Raw node4389 ([])
    (1) (1) (by decide) node4389_check
  · rw [node4389Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0508_mem
  · exact candidateIdeal.zero_mem

def node4390 : WordRow := [([4, 10, 13, 17], 1), ([5, 10, 12, 17], 1)]

def node4390Raw : WordRow := multiplyRow 17 node0508

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4390_check :
    collect (scaleRow 1 node4390Raw ++ scaleRow (-(1 : ℤ)) node4390 ++
      ([])) = [] := by
  decide +kernel

theorem node4390_mem : rowEval varIndex node4390 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4390Raw node4390 ([])
    (1) (1) (by decide) node4390_check
  · rw [node4390Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0508_mem
  · exact candidateIdeal.zero_mem

def node4396 : WordRow := [([4, 11, 13, 16], 1), ([5, 11, 12, 16], 1)]

def node4396Raw : WordRow := multiplyRow 16 node0509

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4396_check :
    collect (scaleRow 1 node4396Raw ++ scaleRow (-(1 : ℤ)) node4396 ++
      ([])) = [] := by
  decide +kernel

theorem node4396_mem : rowEval varIndex node4396 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4396Raw node4396 ([])
    (1) (1) (by decide) node4396_check
  · rw [node4396Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0509_mem
  · exact candidateIdeal.zero_mem

def node4411 : WordRow := [([4, 13, 14, 16], 1), ([5, 12, 14, 16], 1)]

def node4411Raw : WordRow := multiplyRow 16 node0512

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4411_check :
    collect (scaleRow 1 node4411Raw ++ scaleRow (-(1 : ℤ)) node4411 ++
      ([])) = [] := by
  decide +kernel

theorem node4411_mem : rowEval varIndex node4411 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4411Raw node4411 ([])
    (1) (1) (by decide) node4411_check
  · rw [node4411Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0512_mem
  · exact candidateIdeal.zero_mem

def node4417 : WordRow := [([4, 13, 16, 17], 1), ([5, 12, 16, 17], 1)]

def node4417Raw : WordRow := multiplyRow 17 node0514

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4417_check :
    collect (scaleRow 1 node4417Raw ++ scaleRow (-(1 : ℤ)) node4417 ++
      ([])) = [] := by
  decide +kernel

theorem node4417_mem : rowEval varIndex node4417 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4417Raw node4417 ([])
    (1) (1) (by decide) node4417_check
  · rw [node4417Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0514_mem
  · exact candidateIdeal.zero_mem

def node4437 : WordRow := [([5, 10, 13, 14], 1)]

def node4437Raw : WordRow := multiplyRow 14 node0518

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4437_check :
    collect (scaleRow 1 node4437Raw ++ scaleRow (-(1 : ℤ)) node4437 ++
      ([])) = [] := by
  decide +kernel

theorem node4437_mem : rowEval varIndex node4437 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4437Raw node4437 ([])
    (1) (1) (by decide) node4437_check
  · rw [node4437Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0518_mem
  · exact candidateIdeal.zero_mem

def node4468 : WordRow := [([1, 2, 6, 12], 2), ([2, 4, 6, 7], -1), ([2, 5, 6, 6], -1)]

def node4468Raw : WordRow := multiplyRow 2 node0526

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4468_check :
    collect (scaleRow 1 node4468Raw ++ scaleRow (-(1 : ℤ)) node4468 ++
      ([])) = [] := by
  decide +kernel

theorem node4468_mem : rowEval varIndex node4468 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4468Raw node4468 ([])
    (1) (1) (by decide) node4468_check
  · rw [node4468Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0526_mem
  · exact candidateIdeal.zero_mem

def node4470 : WordRow := [([1, 6, 8, 12], 2), ([4, 6, 7, 8], -1), ([5, 6, 6, 8], -1)]

def node4470Raw : WordRow := multiplyRow 8 node0526

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4470_check :
    collect (scaleRow 1 node4470Raw ++ scaleRow (-(1 : ℤ)) node4470 ++
      ([])) = [] := by
  decide +kernel

theorem node4470_mem : rowEval varIndex node4470 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4470Raw node4470 ([])
    (1) (1) (by decide) node4470_check
  · rw [node4470Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0526_mem
  · exact candidateIdeal.zero_mem

def node4471 : WordRow := [([3, 5, 6, 12], 2), ([4, 6, 7, 9], -1), ([5, 6, 6, 9], -1)]

def node4471Raw : WordRow := multiplyRow 9 node0526

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4471_check :
    collect (scaleRow 1 node4471Raw ++ scaleRow (-(1 : ℤ)) node4471 ++
      (scaleRow (-2) node2318 ++ scaleRow (-2) node1913 ++ scaleRow (2) node2412)) = [] := by
  decide +kernel

theorem node4471_mem : rowEval varIndex node4471 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4471Raw node4471 (scaleRow (-2) node2318 ++ scaleRow (-2) node1913 ++ scaleRow (2) node2412)
    (1) (1) (by decide) node4471_check
  · rw [node4471Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0526_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2318 node2318_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1913 node1913_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node2412 node2412_mem)))

def node4476 : WordRow := [([1, 6, 12, 16], 2), ([4, 6, 7, 16], -1), ([5, 6, 6, 16], -1)]

def node4476Raw : WordRow := multiplyRow 16 node0526

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4476_check :
    collect (scaleRow 1 node4476Raw ++ scaleRow (-(1 : ℤ)) node4476 ++
      ([])) = [] := by
  decide +kernel

theorem node4476_mem : rowEval varIndex node4476 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4476Raw node4476 ([])
    (1) (1) (by decide) node4476_check
  · rw [node4476Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0526_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node4476_mem
