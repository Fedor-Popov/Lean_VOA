import VOA.DeligneAudit.D4FusionContactM2Dag00

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0092 : WordRow := [([0, 3, 4], 1), ([1, 2, 4], 1)]

def node0092Raw : WordRow := multiplyRow 4 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0092_check :
    collect (scaleRow 1 node0092Raw ++ scaleRow (-(1 : ℤ)) node0092 ++
      ([])) = [] := by
  decide +kernel

theorem node0092_mem : rowEval varIndex node0092 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0092Raw node0092 ([])
    (1) (1) (by decide) node0092_check
  · rw [node0092Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0093 : WordRow := [([0, 3, 5], 1), ([1, 2, 5], 1)]

def node0093Raw : WordRow := multiplyRow 5 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0093_check :
    collect (scaleRow 1 node0093Raw ++ scaleRow (-(1 : ℤ)) node0093 ++
      ([])) = [] := by
  decide +kernel

theorem node0093_mem : rowEval varIndex node0093 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0093Raw node0093 ([])
    (1) (1) (by decide) node0093_check
  · rw [node0093Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0094 : WordRow := [([0, 3, 6], 1), ([1, 2, 6], 1)]

def node0094Raw : WordRow := multiplyRow 6 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0094_check :
    collect (scaleRow 1 node0094Raw ++ scaleRow (-(1 : ℤ)) node0094 ++
      ([])) = [] := by
  decide +kernel

theorem node0094_mem : rowEval varIndex node0094 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0094Raw node0094 ([])
    (1) (1) (by decide) node0094_check
  · rw [node0094Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0095 : WordRow := [([0, 3, 7], 1), ([1, 2, 7], 1)]

def node0095Raw : WordRow := multiplyRow 7 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0095_check :
    collect (scaleRow 1 node0095Raw ++ scaleRow (-(1 : ℤ)) node0095 ++
      ([])) = [] := by
  decide +kernel

theorem node0095_mem : rowEval varIndex node0095 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0095Raw node0095 ([])
    (1) (1) (by decide) node0095_check
  · rw [node0095Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0096 : WordRow := [([0, 3, 8], 1), ([1, 2, 8], 1)]

def node0096Raw : WordRow := multiplyRow 8 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0096_check :
    collect (scaleRow 1 node0096Raw ++ scaleRow (-(1 : ℤ)) node0096 ++
      ([])) = [] := by
  decide +kernel

theorem node0096_mem : rowEval varIndex node0096 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0096Raw node0096 ([])
    (1) (1) (by decide) node0096_check
  · rw [node0096Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0098 : WordRow := [([0, 3, 10], 1), ([1, 2, 10], 1)]

def node0098Raw : WordRow := multiplyRow 10 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0098_check :
    collect (scaleRow 1 node0098Raw ++ scaleRow (-(1 : ℤ)) node0098 ++
      ([])) = [] := by
  decide +kernel

theorem node0098_mem : rowEval varIndex node0098 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0098Raw node0098 ([])
    (1) (1) (by decide) node0098_check
  · rw [node0098Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0100 : WordRow := [([0, 3, 12], 1), ([1, 2, 12], 1)]

def node0100Raw : WordRow := multiplyRow 12 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0100_check :
    collect (scaleRow 1 node0100Raw ++ scaleRow (-(1 : ℤ)) node0100 ++
      ([])) = [] := by
  decide +kernel

theorem node0100_mem : rowEval varIndex node0100 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0100Raw node0100 ([])
    (1) (1) (by decide) node0100_check
  · rw [node0100Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0101 : WordRow := [([0, 3, 13], 1), ([1, 2, 13], 1)]

def node0101Raw : WordRow := multiplyRow 13 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0101_check :
    collect (scaleRow 1 node0101Raw ++ scaleRow (-(1 : ℤ)) node0101 ++
      ([])) = [] := by
  decide +kernel

theorem node0101_mem : rowEval varIndex node0101 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0101Raw node0101 ([])
    (1) (1) (by decide) node0101_check
  · rw [node0101Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0102 : WordRow := [([0, 3, 14], 1), ([1, 2, 14], 1)]

def node0102Raw : WordRow := multiplyRow 14 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0102_check :
    collect (scaleRow 1 node0102Raw ++ scaleRow (-(1 : ℤ)) node0102 ++
      ([])) = [] := by
  decide +kernel

theorem node0102_mem : rowEval varIndex node0102 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0102Raw node0102 ([])
    (1) (1) (by decide) node0102_check
  · rw [node0102Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0104 : WordRow := [([0, 3, 16], 1), ([1, 2, 16], 1)]

def node0104Raw : WordRow := multiplyRow 16 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0104_check :
    collect (scaleRow 1 node0104Raw ++ scaleRow (-(1 : ℤ)) node0104 ++
      ([])) = [] := by
  decide +kernel

theorem node0104_mem : rowEval varIndex node0104 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0104Raw node0104 ([])
    (1) (1) (by decide) node0104_check
  · rw [node0104Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0122 : WordRow := [([0, 0, 5], 1), ([0, 1, 4], 1)]

def node0122Raw : WordRow := multiplyRow 0 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0122_check :
    collect (scaleRow 1 node0122Raw ++ scaleRow (-(1 : ℤ)) node0122 ++
      ([])) = [] := by
  decide +kernel

theorem node0122_mem : rowEval varIndex node0122 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0122Raw node0122 ([])
    (1) (1) (by decide) node0122_check
  · rw [node0122Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0123 : WordRow := [([0, 2, 5], 1), ([1, 2, 4], 1)]

def node0123Raw : WordRow := multiplyRow 2 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0123_check :
    collect (scaleRow 1 node0123Raw ++ scaleRow (-(1 : ℤ)) node0123 ++
      ([])) = [] := by
  decide +kernel

theorem node0123_mem : rowEval varIndex node0123 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0123Raw node0123 ([])
    (1) (1) (by decide) node0123_check
  · rw [node0123Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0125 : WordRow := [([0, 4, 5], 1), ([1, 4, 4], 1)]

def node0125Raw : WordRow := multiplyRow 4 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0125_check :
    collect (scaleRow 1 node0125Raw ++ scaleRow (-(1 : ℤ)) node0125 ++
      ([])) = [] := by
  decide +kernel

theorem node0125_mem : rowEval varIndex node0125 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0125Raw node0125 ([])
    (1) (1) (by decide) node0125_check
  · rw [node0125Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0127 : WordRow := [([0, 5, 6], 1), ([1, 4, 6], 1)]

def node0127Raw : WordRow := multiplyRow 6 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0127_check :
    collect (scaleRow 1 node0127Raw ++ scaleRow (-(1 : ℤ)) node0127 ++
      ([])) = [] := by
  decide +kernel

theorem node0127_mem : rowEval varIndex node0127 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0127Raw node0127 ([])
    (1) (1) (by decide) node0127_check
  · rw [node0127Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0128 : WordRow := [([0, 5, 7], 1), ([1, 4, 7], 1)]

def node0128Raw : WordRow := multiplyRow 7 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0128_check :
    collect (scaleRow 1 node0128Raw ++ scaleRow (-(1 : ℤ)) node0128 ++
      ([])) = [] := by
  decide +kernel

theorem node0128_mem : rowEval varIndex node0128 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0128Raw node0128 ([])
    (1) (1) (by decide) node0128_check
  · rw [node0128Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0129 : WordRow := [([0, 5, 8], 1), ([1, 4, 8], 1)]

def node0129Raw : WordRow := multiplyRow 8 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0129_check :
    collect (scaleRow 1 node0129Raw ++ scaleRow (-(1 : ℤ)) node0129 ++
      ([])) = [] := by
  decide +kernel

theorem node0129_mem : rowEval varIndex node0129 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0129Raw node0129 ([])
    (1) (1) (by decide) node0129_check
  · rw [node0129Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0130 : WordRow := [([0, 5, 9], 1), ([1, 4, 9], 1)]

def node0130Raw : WordRow := multiplyRow 9 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0130_check :
    collect (scaleRow 1 node0130Raw ++ scaleRow (-(1 : ℤ)) node0130 ++
      ([])) = [] := by
  decide +kernel

theorem node0130_mem : rowEval varIndex node0130 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0130Raw node0130 ([])
    (1) (1) (by decide) node0130_check
  · rw [node0130Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0131 : WordRow := [([0, 5, 10], 1), ([1, 4, 10], 1)]

def node0131Raw : WordRow := multiplyRow 10 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0131_check :
    collect (scaleRow 1 node0131Raw ++ scaleRow (-(1 : ℤ)) node0131 ++
      ([])) = [] := by
  decide +kernel

theorem node0131_mem : rowEval varIndex node0131 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0131Raw node0131 ([])
    (1) (1) (by decide) node0131_check
  · rw [node0131Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0132 : WordRow := [([0, 5, 11], 1), ([1, 4, 11], 1)]

def node0132Raw : WordRow := multiplyRow 11 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0132_check :
    collect (scaleRow 1 node0132Raw ++ scaleRow (-(1 : ℤ)) node0132 ++
      ([])) = [] := by
  decide +kernel

theorem node0132_mem : rowEval varIndex node0132 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0132Raw node0132 ([])
    (1) (1) (by decide) node0132_check
  · rw [node0132Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0133 : WordRow := [([0, 5, 12], 1), ([1, 4, 12], 1)]

def node0133Raw : WordRow := multiplyRow 12 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0133_check :
    collect (scaleRow 1 node0133Raw ++ scaleRow (-(1 : ℤ)) node0133 ++
      ([])) = [] := by
  decide +kernel

theorem node0133_mem : rowEval varIndex node0133 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0133Raw node0133 ([])
    (1) (1) (by decide) node0133_check
  · rw [node0133Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0135 : WordRow := [([0, 5, 14], 1), ([1, 4, 14], 1)]

def node0135Raw : WordRow := multiplyRow 14 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0135_check :
    collect (scaleRow 1 node0135Raw ++ scaleRow (-(1 : ℤ)) node0135 ++
      ([])) = [] := by
  decide +kernel

theorem node0135_mem : rowEval varIndex node0135 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0135Raw node0135 ([])
    (1) (1) (by decide) node0135_check
  · rw [node0135Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0136 : WordRow := [([0, 5, 15], 1), ([1, 4, 15], 1)]

def node0136Raw : WordRow := multiplyRow 15 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0136_check :
    collect (scaleRow 1 node0136Raw ++ scaleRow (-(1 : ℤ)) node0136 ++
      ([])) = [] := by
  decide +kernel

theorem node0136_mem : rowEval varIndex node0136 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0136Raw node0136 ([])
    (1) (1) (by decide) node0136_check
  · rw [node0136Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0137 : WordRow := [([0, 5, 16], 1), ([1, 4, 16], 1)]

def node0137Raw : WordRow := multiplyRow 16 node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0137_check :
    collect (scaleRow 1 node0137Raw ++ scaleRow (-(1 : ℤ)) node0137 ++
      ([])) = [] := by
  decide +kernel

theorem node0137_mem : rowEval varIndex node0137 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0137Raw node0137 ([])
    (1) (1) (by decide) node0137_check
  · rw [node0137Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0139 : WordRow := [([1, 4, 5], 1)]

def node0139Raw : WordRow := multiplyRow 4 node0005

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0139_check :
    collect (scaleRow 1 node0139Raw ++ scaleRow (-(1 : ℤ)) node0139 ++
      ([])) = [] := by
  decide +kernel

theorem node0139_mem : rowEval varIndex node0139 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0139Raw node0139 ([])
    (1) (1) (by decide) node0139_check
  · rw [node0139Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0005_mem
  · exact candidateIdeal.zero_mem

def node0143 : WordRow := [([1, 5, 8], 1)]

def node0143Raw : WordRow := multiplyRow 8 node0005

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0143_check :
    collect (scaleRow 1 node0143Raw ++ scaleRow (-(1 : ℤ)) node0143 ++
      ([])) = [] := by
  decide +kernel

theorem node0143_mem : rowEval varIndex node0143 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0143Raw node0143 ([])
    (1) (1) (by decide) node0143_check
  · rw [node0143Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0005_mem
  · exact candidateIdeal.zero_mem

def node0145 : WordRow := [([1, 5, 10], 1)]

def node0145Raw : WordRow := multiplyRow 10 node0005

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0145_check :
    collect (scaleRow 1 node0145Raw ++ scaleRow (-(1 : ℤ)) node0145 ++
      ([])) = [] := by
  decide +kernel

theorem node0145_mem : rowEval varIndex node0145 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0145Raw node0145 ([])
    (1) (1) (by decide) node0145_check
  · rw [node0145Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0005_mem
  · exact candidateIdeal.zero_mem

def node0149 : WordRow := [([1, 5, 14], 1)]

def node0149Raw : WordRow := multiplyRow 14 node0005

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0149_check :
    collect (scaleRow 1 node0149Raw ++ scaleRow (-(1 : ℤ)) node0149 ++
      ([])) = [] := by
  decide +kernel

theorem node0149_mem : rowEval varIndex node0149 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0149Raw node0149 ([])
    (1) (1) (by decide) node0149_check
  · rw [node0149Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0005_mem
  · exact candidateIdeal.zero_mem

def node0153 : WordRow := [([0, 0, 7], 1), ([0, 1, 6], 1)]

def node0153Raw : WordRow := multiplyRow 0 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0153_check :
    collect (scaleRow 1 node0153Raw ++ scaleRow (-(1 : ℤ)) node0153 ++
      ([])) = [] := by
  decide +kernel

theorem node0153_mem : rowEval varIndex node0153 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0153Raw node0153 ([])
    (1) (1) (by decide) node0153_check
  · rw [node0153Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0154 : WordRow := [([0, 2, 7], 1), ([1, 2, 6], 1)]

def node0154Raw : WordRow := multiplyRow 2 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0154_check :
    collect (scaleRow 1 node0154Raw ++ scaleRow (-(1 : ℤ)) node0154 ++
      ([])) = [] := by
  decide +kernel

theorem node0154_mem : rowEval varIndex node0154 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0154Raw node0154 ([])
    (1) (1) (by decide) node0154_check
  · rw [node0154Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0156 : WordRow := [([0, 4, 7], 1), ([1, 4, 6], 1)]

def node0156Raw : WordRow := multiplyRow 4 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0156_check :
    collect (scaleRow 1 node0156Raw ++ scaleRow (-(1 : ℤ)) node0156 ++
      ([])) = [] := by
  decide +kernel

theorem node0156_mem : rowEval varIndex node0156 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0156Raw node0156 ([])
    (1) (1) (by decide) node0156_check
  · rw [node0156Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0157 : WordRow := [([1, 4, 7], 1), ([1, 5, 6], -1)]

def node0157Raw : WordRow := multiplyRow 5 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0157_check :
    collect (scaleRow 1 node0157Raw ++ scaleRow (-(-1 : ℤ)) node0157 ++
      (scaleRow (-1) node0128)) = [] := by
  decide +kernel

theorem node0157_mem : rowEval varIndex node0157 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0157Raw node0157 (scaleRow (-1) node0128)
    (1) (-1) (by decide) node0157_check
  · rw [node0157Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0128 node0128_mem)

def node0158 : WordRow := [([0, 6, 7], 1), ([1, 6, 6], 1)]

def node0158Raw : WordRow := multiplyRow 6 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0158_check :
    collect (scaleRow 1 node0158Raw ++ scaleRow (-(1 : ℤ)) node0158 ++
      ([])) = [] := by
  decide +kernel

theorem node0158_mem : rowEval varIndex node0158 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0158Raw node0158 ([])
    (1) (1) (by decide) node0158_check
  · rw [node0158Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0160 : WordRow := [([0, 7, 8], 1), ([1, 6, 8], 1)]

def node0160Raw : WordRow := multiplyRow 8 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0160_check :
    collect (scaleRow 1 node0160Raw ++ scaleRow (-(1 : ℤ)) node0160 ++
      ([])) = [] := by
  decide +kernel

theorem node0160_mem : rowEval varIndex node0160 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0160Raw node0160 ([])
    (1) (1) (by decide) node0160_check
  · rw [node0160Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0161 : WordRow := [([0, 7, 9], 1), ([1, 6, 9], 1)]

def node0161Raw : WordRow := multiplyRow 9 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0161_check :
    collect (scaleRow 1 node0161Raw ++ scaleRow (-(1 : ℤ)) node0161 ++
      ([])) = [] := by
  decide +kernel

theorem node0161_mem : rowEval varIndex node0161 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0161Raw node0161 ([])
    (1) (1) (by decide) node0161_check
  · rw [node0161Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0162 : WordRow := [([0, 7, 10], 1), ([1, 6, 10], 1)]

def node0162Raw : WordRow := multiplyRow 10 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0162_check :
    collect (scaleRow 1 node0162Raw ++ scaleRow (-(1 : ℤ)) node0162 ++
      ([])) = [] := by
  decide +kernel

theorem node0162_mem : rowEval varIndex node0162 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0162Raw node0162 ([])
    (1) (1) (by decide) node0162_check
  · rw [node0162Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0164 : WordRow := [([0, 7, 12], 1), ([1, 6, 12], 1)]

def node0164Raw : WordRow := multiplyRow 12 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0164_check :
    collect (scaleRow 1 node0164Raw ++ scaleRow (-(1 : ℤ)) node0164 ++
      ([])) = [] := by
  decide +kernel

theorem node0164_mem : rowEval varIndex node0164 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0164Raw node0164 ([])
    (1) (1) (by decide) node0164_check
  · rw [node0164Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0166 : WordRow := [([0, 7, 14], 1), ([1, 6, 14], 1)]

def node0166Raw : WordRow := multiplyRow 14 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0166_check :
    collect (scaleRow 1 node0166Raw ++ scaleRow (-(1 : ℤ)) node0166 ++
      ([])) = [] := by
  decide +kernel

theorem node0166_mem : rowEval varIndex node0166 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0166Raw node0166 ([])
    (1) (1) (by decide) node0166_check
  · rw [node0166Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0168 : WordRow := [([0, 7, 16], 1), ([1, 6, 16], 1)]

def node0168Raw : WordRow := multiplyRow 16 node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0168_check :
    collect (scaleRow 1 node0168Raw ++ scaleRow (-(1 : ℤ)) node0168 ++
      ([])) = [] := by
  decide +kernel

theorem node0168_mem : rowEval varIndex node0168 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0168Raw node0168 ([])
    (1) (1) (by decide) node0168_check
  · rw [node0168Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0170 : WordRow := [([1, 6, 7], 1)]

def node0170Raw : WordRow := multiplyRow 6 node0007

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0170_check :
    collect (scaleRow 1 node0170Raw ++ scaleRow (-(1 : ℤ)) node0170 ++
      ([])) = [] := by
  decide +kernel

theorem node0170_mem : rowEval varIndex node0170 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0170Raw node0170 ([])
    (1) (1) (by decide) node0170_check
  · rw [node0170Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0007_mem
  · exact candidateIdeal.zero_mem

def node0172 : WordRow := [([1, 7, 8], 1)]

def node0172Raw : WordRow := multiplyRow 8 node0007

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0172_check :
    collect (scaleRow 1 node0172Raw ++ scaleRow (-(1 : ℤ)) node0172 ++
      ([])) = [] := by
  decide +kernel

theorem node0172_mem : rowEval varIndex node0172 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0172Raw node0172 ([])
    (1) (1) (by decide) node0172_check
  · rw [node0172Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0007_mem
  · exact candidateIdeal.zero_mem

def node0173 : WordRow := [([1, 7, 9], 1)]

def node0173Raw : WordRow := multiplyRow 9 node0007

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0173_check :
    collect (scaleRow 1 node0173Raw ++ scaleRow (-(1 : ℤ)) node0173 ++
      ([])) = [] := by
  decide +kernel

theorem node0173_mem : rowEval varIndex node0173 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0173Raw node0173 ([])
    (1) (1) (by decide) node0173_check
  · rw [node0173Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0007_mem
  · exact candidateIdeal.zero_mem

def node0182 : WordRow := [([1, 2, 2], 1)]

def node0182Raw : WordRow := multiplyRow 0 node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0182_check :
    collect (scaleRow 1 node0182Raw ++ scaleRow (-(-1 : ℤ)) node0182 ++
      (scaleRow (-1) node0090)) = [] := by
  decide +kernel

theorem node0182_mem : rowEval varIndex node0182 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0182Raw node0182 (scaleRow (-1) node0090)
    (1) (-1) (by decide) node0182_check
  · rw [node0182Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0008_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0090 node0090_mem)

def node0185 : WordRow := [([2, 3, 4], 1)]

def node0185Raw : WordRow := multiplyRow 4 node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0185_check :
    collect (scaleRow 1 node0185Raw ++ scaleRow (-(1 : ℤ)) node0185 ++
      ([])) = [] := by
  decide +kernel

theorem node0185_mem : rowEval varIndex node0185 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0185Raw node0185 ([])
    (1) (1) (by decide) node0185_check
  · rw [node0185Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0187 : WordRow := [([2, 3, 6], 1)]

def node0187Raw : WordRow := multiplyRow 6 node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0187_check :
    collect (scaleRow 1 node0187Raw ++ scaleRow (-(1 : ℤ)) node0187 ++
      ([])) = [] := by
  decide +kernel

theorem node0187_mem : rowEval varIndex node0187 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0187Raw node0187 ([])
    (1) (1) (by decide) node0187_check
  · rw [node0187Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0193 : WordRow := [([2, 3, 12], 1)]

def node0193Raw : WordRow := multiplyRow 12 node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0193_check :
    collect (scaleRow 1 node0193Raw ++ scaleRow (-(1 : ℤ)) node0193 ++
      ([])) = [] := by
  decide +kernel

theorem node0193_mem : rowEval varIndex node0193 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0193Raw node0193 ([])
    (1) (1) (by decide) node0193_check
  · rw [node0193Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0195 : WordRow := [([2, 3, 14], 1)]

def node0195Raw : WordRow := multiplyRow 14 node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0195_check :
    collect (scaleRow 1 node0195Raw ++ scaleRow (-(1 : ℤ)) node0195 ++
      ([])) = [] := by
  decide +kernel

theorem node0195_mem : rowEval varIndex node0195 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0195Raw node0195 ([])
    (1) (1) (by decide) node0195_check
  · rw [node0195Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0214 : WordRow := [([0, 0, 9], 1), ([0, 1, 8], 1), ([0, 2, 5], -1), ([0, 3, 4], -1)]

def node0214Raw : WordRow := multiplyRow 0 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0214_check :
    collect (scaleRow 1 node0214Raw ++ scaleRow (-(1 : ℤ)) node0214 ++
      ([])) = [] := by
  decide +kernel

theorem node0214_mem : rowEval varIndex node0214 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0214Raw node0214 ([])
    (1) (1) (by decide) node0214_check
  · rw [node0214Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0215 : WordRow := [([0, 2, 9], 1), ([1, 2, 8], 1), ([2, 2, 5], -1), ([2, 3, 4], -1)]

def node0215Raw : WordRow := multiplyRow 2 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0215_check :
    collect (scaleRow 1 node0215Raw ++ scaleRow (-(1 : ℤ)) node0215 ++
      ([])) = [] := by
  decide +kernel

theorem node0215_mem : rowEval varIndex node0215 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0215Raw node0215 ([])
    (1) (1) (by decide) node0215_check
  · rw [node0215Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0217 : WordRow := [([0, 4, 9], 1), ([1, 4, 8], 1), ([2, 4, 5], -1), ([3, 4, 4], -1)]

def node0217Raw : WordRow := multiplyRow 4 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0217_check :
    collect (scaleRow 1 node0217Raw ++ scaleRow (-(1 : ℤ)) node0217 ++
      ([])) = [] := by
  decide +kernel

theorem node0217_mem : rowEval varIndex node0217 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0217Raw node0217 ([])
    (1) (1) (by decide) node0217_check
  · rw [node0217Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0218 : WordRow := [([1, 4, 9], 1), ([1, 5, 8], -1), ([2, 5, 5], 1), ([3, 4, 5], 1)]

def node0218Raw : WordRow := multiplyRow 5 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0218_check :
    collect (scaleRow 1 node0218Raw ++ scaleRow (-(-1 : ℤ)) node0218 ++
      (scaleRow (-1) node0130)) = [] := by
  decide +kernel

theorem node0218_mem : rowEval varIndex node0218 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0218Raw node0218 (scaleRow (-1) node0130)
    (1) (-1) (by decide) node0218_check
  · rw [node0218Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0130 node0130_mem)

def node0219 : WordRow := [([0, 6, 9], 1), ([1, 6, 8], 1), ([2, 5, 6], -1), ([3, 4, 6], -1)]

def node0219Raw : WordRow := multiplyRow 6 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0219_check :
    collect (scaleRow 1 node0219Raw ++ scaleRow (-(1 : ℤ)) node0219 ++
      ([])) = [] := by
  decide +kernel

theorem node0219_mem : rowEval varIndex node0219 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0219Raw node0219 ([])
    (1) (1) (by decide) node0219_check
  · rw [node0219Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0220 : WordRow := [([1, 6, 9], 1), ([1, 7, 8], -1), ([2, 5, 7], 1), ([3, 4, 7], 1)]

def node0220Raw : WordRow := multiplyRow 7 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0220_check :
    collect (scaleRow 1 node0220Raw ++ scaleRow (-(-1 : ℤ)) node0220 ++
      (scaleRow (-1) node0161)) = [] := by
  decide +kernel

theorem node0220_mem : rowEval varIndex node0220 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0220Raw node0220 (scaleRow (-1) node0161)
    (1) (-1) (by decide) node0220_check
  · rw [node0220Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0161 node0161_mem)

def node0221 : WordRow := [([0, 8, 9], 1), ([1, 8, 8], 1), ([2, 5, 8], -1), ([3, 4, 8], -1)]

def node0221Raw : WordRow := multiplyRow 8 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0221_check :
    collect (scaleRow 1 node0221Raw ++ scaleRow (-(1 : ℤ)) node0221 ++
      ([])) = [] := by
  decide +kernel

theorem node0221_mem : rowEval varIndex node0221 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0221Raw node0221 ([])
    (1) (1) (by decide) node0221_check
  · rw [node0221Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0223 : WordRow := [([0, 9, 10], 1), ([1, 8, 10], 1), ([2, 5, 10], -1), ([3, 4, 10], -1)]

def node0223Raw : WordRow := multiplyRow 10 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0223_check :
    collect (scaleRow 1 node0223Raw ++ scaleRow (-(1 : ℤ)) node0223 ++
      ([])) = [] := by
  decide +kernel

theorem node0223_mem : rowEval varIndex node0223 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0223Raw node0223 ([])
    (1) (1) (by decide) node0223_check
  · rw [node0223Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0224 : WordRow := [([0, 9, 11], 1), ([1, 8, 11], 1), ([2, 5, 11], -1), ([3, 4, 11], -1)]

def node0224Raw : WordRow := multiplyRow 11 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0224_check :
    collect (scaleRow 1 node0224Raw ++ scaleRow (-(1 : ℤ)) node0224 ++
      ([])) = [] := by
  decide +kernel

theorem node0224_mem : rowEval varIndex node0224 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0224Raw node0224 ([])
    (1) (1) (by decide) node0224_check
  · rw [node0224Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0225 : WordRow := [([0, 9, 12], 1), ([1, 8, 12], 1), ([2, 5, 12], -1), ([3, 4, 12], -1)]

def node0225Raw : WordRow := multiplyRow 12 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0225_check :
    collect (scaleRow 1 node0225Raw ++ scaleRow (-(1 : ℤ)) node0225 ++
      ([])) = [] := by
  decide +kernel

theorem node0225_mem : rowEval varIndex node0225 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0225Raw node0225 ([])
    (1) (1) (by decide) node0225_check
  · rw [node0225Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0226 : WordRow := [([0, 9, 13], 1), ([1, 8, 13], 1), ([2, 5, 13], -1), ([3, 4, 13], -1)]

def node0226Raw : WordRow := multiplyRow 13 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0226_check :
    collect (scaleRow 1 node0226Raw ++ scaleRow (-(1 : ℤ)) node0226 ++
      ([])) = [] := by
  decide +kernel

theorem node0226_mem : rowEval varIndex node0226 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0226Raw node0226 ([])
    (1) (1) (by decide) node0226_check
  · rw [node0226Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0227 : WordRow := [([0, 9, 14], 1), ([1, 8, 14], 1), ([2, 5, 14], -1), ([3, 4, 14], -1)]

def node0227Raw : WordRow := multiplyRow 14 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0227_check :
    collect (scaleRow 1 node0227Raw ++ scaleRow (-(1 : ℤ)) node0227 ++
      ([])) = [] := by
  decide +kernel

theorem node0227_mem : rowEval varIndex node0227 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0227Raw node0227 ([])
    (1) (1) (by decide) node0227_check
  · rw [node0227Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0228 : WordRow := [([0, 9, 15], 1), ([1, 8, 15], 1), ([2, 5, 15], -1), ([3, 4, 15], -1)]

def node0228Raw : WordRow := multiplyRow 15 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0228_check :
    collect (scaleRow 1 node0228Raw ++ scaleRow (-(1 : ℤ)) node0228 ++
      ([])) = [] := by
  decide +kernel

theorem node0228_mem : rowEval varIndex node0228 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0228Raw node0228 ([])
    (1) (1) (by decide) node0228_check
  · rw [node0228Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0229 : WordRow := [([0, 9, 16], 1), ([1, 8, 16], 1), ([2, 5, 16], -1), ([3, 4, 16], -1)]

def node0229Raw : WordRow := multiplyRow 16 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0229_check :
    collect (scaleRow 1 node0229Raw ++ scaleRow (-(1 : ℤ)) node0229 ++
      ([])) = [] := by
  decide +kernel

theorem node0229_mem : rowEval varIndex node0229 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0229Raw node0229 ([])
    (1) (1) (by decide) node0229_check
  · rw [node0229Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0230 : WordRow := [([0, 9, 17], 1), ([1, 8, 17], 1), ([2, 5, 17], -1), ([3, 4, 17], -1)]

def node0230Raw : WordRow := multiplyRow 17 node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0230_check :
    collect (scaleRow 1 node0230Raw ++ scaleRow (-(1 : ℤ)) node0230 ++
      ([])) = [] := by
  decide +kernel

theorem node0230_mem : rowEval varIndex node0230 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0230Raw node0230 ([])
    (1) (1) (by decide) node0230_check
  · rw [node0230Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0231 : WordRow := [([2, 5, 5], 1), ([3, 4, 5], 2)]

def node0231Raw : WordRow := multiplyRow 4 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0231_check :
    collect (scaleRow 1 node0231Raw ++ scaleRow (-(-1 : ℤ)) node0231 ++
      (scaleRow (-1) node0218 ++ scaleRow (-1) node0143)) = [] := by
  decide +kernel

theorem node0231_mem : rowEval varIndex node0231 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0231Raw node0231 (scaleRow (-1) node0218 ++ scaleRow (-1) node0143)
    (1) (-1) (by decide) node0231_check
  · rw [node0231Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0218 node0218_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0143 node0143_mem))

def node0233 : WordRow := [([2, 5, 7], 1), ([3, 4, 7], 1), ([3, 5, 6], 1)]

def node0233Raw : WordRow := multiplyRow 6 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0233_check :
    collect (scaleRow 1 node0233Raw ++ scaleRow (-(-1 : ℤ)) node0233 ++
      (scaleRow (-1) node0220 ++ scaleRow (-1) node0172)) = [] := by
  decide +kernel

theorem node0233_mem : rowEval varIndex node0233 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0233Raw node0233 (scaleRow (-1) node0220 ++ scaleRow (-1) node0172)
    (1) (-1) (by decide) node0233_check
  · rw [node0233Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0220 node0220_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0172 node0172_mem))

def node0234 : WordRow := [([3, 5, 7], 1)]

def node0234Raw : WordRow := multiplyRow 7 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0234_check :
    collect (scaleRow 1 node0234Raw ++ scaleRow (-(-1 : ℤ)) node0234 ++
      (scaleRow (-1) node0173)) = [] := by
  decide +kernel

theorem node0234_mem : rowEval varIndex node0234 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0234Raw node0234 (scaleRow (-1) node0173)
    (1) (-1) (by decide) node0234_check
  · rw [node0234Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0173 node0173_mem)

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0234_mem
