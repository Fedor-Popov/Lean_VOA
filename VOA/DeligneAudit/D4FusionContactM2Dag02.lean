import VOA.DeligneAudit.D4FusionContactM2Dag01

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0237 : WordRow := [([1, 9, 10], 1), ([3, 5, 10], -1)]

def node0237Raw : WordRow := multiplyRow 10 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0237_check :
    collect (scaleRow 1 node0237Raw ++ scaleRow (-(1 : ℤ)) node0237 ++
      ([])) = [] := by
  decide +kernel

theorem node0237_mem : rowEval varIndex node0237 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0237Raw node0237 ([])
    (1) (1) (by decide) node0237_check
  · rw [node0237Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · exact candidateIdeal.zero_mem

def node0239 : WordRow := [([1, 9, 12], 1), ([3, 5, 12], -1)]

def node0239Raw : WordRow := multiplyRow 12 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0239_check :
    collect (scaleRow 1 node0239Raw ++ scaleRow (-(1 : ℤ)) node0239 ++
      ([])) = [] := by
  decide +kernel

theorem node0239_mem : rowEval varIndex node0239 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0239Raw node0239 ([])
    (1) (1) (by decide) node0239_check
  · rw [node0239Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · exact candidateIdeal.zero_mem

def node0241 : WordRow := [([1, 9, 14], 1), ([3, 5, 14], -1)]

def node0241Raw : WordRow := multiplyRow 14 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0241_check :
    collect (scaleRow 1 node0241Raw ++ scaleRow (-(1 : ℤ)) node0241 ++
      ([])) = [] := by
  decide +kernel

theorem node0241_mem : rowEval varIndex node0241 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0241Raw node0241 ([])
    (1) (1) (by decide) node0241_check
  · rw [node0241Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · exact candidateIdeal.zero_mem

def node0243 : WordRow := [([1, 9, 16], 1), ([3, 5, 16], -1)]

def node0243Raw : WordRow := multiplyRow 16 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0243_check :
    collect (scaleRow 1 node0243Raw ++ scaleRow (-(1 : ℤ)) node0243 ++
      ([])) = [] := by
  decide +kernel

theorem node0243_mem : rowEval varIndex node0243 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0243Raw node0243 ([])
    (1) (1) (by decide) node0243_check
  · rw [node0243Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · exact candidateIdeal.zero_mem

def node0244 : WordRow := [([1, 9, 17], 1), ([3, 5, 17], -1)]

def node0244Raw : WordRow := multiplyRow 17 node0011

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0244_check :
    collect (scaleRow 1 node0244Raw ++ scaleRow (-(1 : ℤ)) node0244 ++
      ([])) = [] := by
  decide +kernel

theorem node0244_mem : rowEval varIndex node0244 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0244Raw node0244 ([])
    (1) (1) (by decide) node0244_check
  · rw [node0244Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0011_mem
  · exact candidateIdeal.zero_mem

def node0245 : WordRow := [([0, 0, 11], 1), ([0, 1, 10], 1), ([0, 2, 7], -1), ([0, 3, 6], -1)]

def node0245Raw : WordRow := multiplyRow 0 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0245_check :
    collect (scaleRow 1 node0245Raw ++ scaleRow (-(1 : ℤ)) node0245 ++
      ([])) = [] := by
  decide +kernel

theorem node0245_mem : rowEval varIndex node0245 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0245Raw node0245 ([])
    (1) (1) (by decide) node0245_check
  · rw [node0245Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0246 : WordRow := [([0, 2, 11], 1), ([1, 2, 10], 1), ([2, 2, 7], -1), ([2, 3, 6], -1)]

def node0246Raw : WordRow := multiplyRow 2 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0246_check :
    collect (scaleRow 1 node0246Raw ++ scaleRow (-(1 : ℤ)) node0246 ++
      ([])) = [] := by
  decide +kernel

theorem node0246_mem : rowEval varIndex node0246 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0246Raw node0246 ([])
    (1) (1) (by decide) node0246_check
  · rw [node0246Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0248 : WordRow := [([0, 4, 11], 1), ([1, 4, 10], 1), ([2, 4, 7], -1), ([3, 4, 6], -1)]

def node0248Raw : WordRow := multiplyRow 4 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0248_check :
    collect (scaleRow 1 node0248Raw ++ scaleRow (-(1 : ℤ)) node0248 ++
      ([])) = [] := by
  decide +kernel

theorem node0248_mem : rowEval varIndex node0248 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0248Raw node0248 ([])
    (1) (1) (by decide) node0248_check
  · rw [node0248Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0249 : WordRow := [([1, 4, 11], 1), ([1, 5, 10], -1), ([2, 5, 7], 1), ([3, 5, 6], 1)]

def node0249Raw : WordRow := multiplyRow 5 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0249_check :
    collect (scaleRow 1 node0249Raw ++ scaleRow (-(-1 : ℤ)) node0249 ++
      (scaleRow (-1) node0132)) = [] := by
  decide +kernel

theorem node0249_mem : rowEval varIndex node0249 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0249Raw node0249 (scaleRow (-1) node0132)
    (1) (-1) (by decide) node0249_check
  · rw [node0249Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0132 node0132_mem)

def node0250 : WordRow := [([0, 6, 11], 1), ([1, 6, 10], 1), ([2, 6, 7], -1), ([3, 6, 6], -1)]

def node0250Raw : WordRow := multiplyRow 6 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0250_check :
    collect (scaleRow 1 node0250Raw ++ scaleRow (-(1 : ℤ)) node0250 ++
      ([])) = [] := by
  decide +kernel

theorem node0250_mem : rowEval varIndex node0250 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0250Raw node0250 ([])
    (1) (1) (by decide) node0250_check
  · rw [node0250Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0252 : WordRow := [([0, 8, 11], 1), ([1, 8, 10], 1), ([2, 7, 8], -1), ([3, 6, 8], -1)]

def node0252Raw : WordRow := multiplyRow 8 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0252_check :
    collect (scaleRow 1 node0252Raw ++ scaleRow (-(1 : ℤ)) node0252 ++
      ([])) = [] := by
  decide +kernel

theorem node0252_mem : rowEval varIndex node0252 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0252Raw node0252 ([])
    (1) (1) (by decide) node0252_check
  · rw [node0252Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0253 : WordRow := [([1, 8, 11], 1), ([1, 9, 10], -1), ([2, 5, 11], -1), ([2, 7, 9], 1), ([3, 4, 11], -1), ([3, 6, 9], 1)]

def node0253Raw : WordRow := multiplyRow 9 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0253_check :
    collect (scaleRow 1 node0253Raw ++ scaleRow (-(-1 : ℤ)) node0253 ++
      (scaleRow (-1) node0224)) = [] := by
  decide +kernel

theorem node0253_mem : rowEval varIndex node0253 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0253Raw node0253 (scaleRow (-1) node0224)
    (1) (-1) (by decide) node0253_check
  · rw [node0253Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0224 node0224_mem)

def node0254 : WordRow := [([0, 10, 11], 1), ([1, 10, 10], 1), ([2, 7, 10], -1), ([3, 6, 10], -1)]

def node0254Raw : WordRow := multiplyRow 10 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0254_check :
    collect (scaleRow 1 node0254Raw ++ scaleRow (-(1 : ℤ)) node0254 ++
      ([])) = [] := by
  decide +kernel

theorem node0254_mem : rowEval varIndex node0254 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0254Raw node0254 ([])
    (1) (1) (by decide) node0254_check
  · rw [node0254Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0256 : WordRow := [([0, 11, 12], 1), ([1, 10, 12], 1), ([2, 7, 12], -1), ([3, 6, 12], -1)]

def node0256Raw : WordRow := multiplyRow 12 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0256_check :
    collect (scaleRow 1 node0256Raw ++ scaleRow (-(1 : ℤ)) node0256 ++
      ([])) = [] := by
  decide +kernel

theorem node0256_mem : rowEval varIndex node0256 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0256Raw node0256 ([])
    (1) (1) (by decide) node0256_check
  · rw [node0256Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0257 : WordRow := [([0, 11, 13], 1), ([1, 10, 13], 1), ([2, 7, 13], -1), ([3, 6, 13], -1)]

def node0257Raw : WordRow := multiplyRow 13 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0257_check :
    collect (scaleRow 1 node0257Raw ++ scaleRow (-(1 : ℤ)) node0257 ++
      ([])) = [] := by
  decide +kernel

theorem node0257_mem : rowEval varIndex node0257 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0257Raw node0257 ([])
    (1) (1) (by decide) node0257_check
  · rw [node0257Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0258 : WordRow := [([0, 11, 14], 1), ([1, 10, 14], 1), ([2, 7, 14], -1), ([3, 6, 14], -1)]

def node0258Raw : WordRow := multiplyRow 14 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0258_check :
    collect (scaleRow 1 node0258Raw ++ scaleRow (-(1 : ℤ)) node0258 ++
      ([])) = [] := by
  decide +kernel

theorem node0258_mem : rowEval varIndex node0258 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0258Raw node0258 ([])
    (1) (1) (by decide) node0258_check
  · rw [node0258Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0259 : WordRow := [([0, 11, 15], 1), ([1, 10, 15], 1), ([2, 7, 15], -1), ([3, 6, 15], -1)]

def node0259Raw : WordRow := multiplyRow 15 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0259_check :
    collect (scaleRow 1 node0259Raw ++ scaleRow (-(1 : ℤ)) node0259 ++
      ([])) = [] := by
  decide +kernel

theorem node0259_mem : rowEval varIndex node0259 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0259Raw node0259 ([])
    (1) (1) (by decide) node0259_check
  · rw [node0259Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0260 : WordRow := [([0, 11, 16], 1), ([1, 10, 16], 1), ([2, 7, 16], -1), ([3, 6, 16], -1)]

def node0260Raw : WordRow := multiplyRow 16 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0260_check :
    collect (scaleRow 1 node0260Raw ++ scaleRow (-(1 : ℤ)) node0260 ++
      ([])) = [] := by
  decide +kernel

theorem node0260_mem : rowEval varIndex node0260 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0260Raw node0260 ([])
    (1) (1) (by decide) node0260_check
  · rw [node0260Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0261 : WordRow := [([0, 11, 17], 1), ([1, 10, 17], 1), ([2, 7, 17], -1), ([3, 6, 17], -1)]

def node0261Raw : WordRow := multiplyRow 17 node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0261_check :
    collect (scaleRow 1 node0261Raw ++ scaleRow (-(1 : ℤ)) node0261 ++
      ([])) = [] := by
  decide +kernel

theorem node0261_mem : rowEval varIndex node0261 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0261Raw node0261 ([])
    (1) (1) (by decide) node0261_check
  · rw [node0261Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0264 : WordRow := [([2, 5, 11], 1), ([2, 7, 9], -1), ([3, 4, 11], 1), ([3, 5, 10], 1), ([3, 6, 9], -1), ([3, 7, 8], -1)]

def node0264Raw : WordRow := multiplyRow 8 node0013

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0264_check :
    collect (scaleRow 1 node0264Raw ++ scaleRow (-(1 : ℤ)) node0264 ++
      (scaleRow (-1) node0253 ++ scaleRow (-1) node0237)) = [] := by
  decide +kernel

theorem node0264_mem : rowEval varIndex node0264 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0264Raw node0264 (scaleRow (-1) node0253 ++ scaleRow (-1) node0237)
    (1) (1) (by decide) node0264_check
  · rw [node0264Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0013_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0253 node0253_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0237 node0237_mem))

def node0270 : WordRow := [([1, 11, 14], 1), ([3, 7, 14], -1)]

def node0270Raw : WordRow := multiplyRow 14 node0013

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0270_check :
    collect (scaleRow 1 node0270Raw ++ scaleRow (-(1 : ℤ)) node0270 ++
      ([])) = [] := by
  decide +kernel

theorem node0270_mem : rowEval varIndex node0270 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0270Raw node0270 ([])
    (1) (1) (by decide) node0270_check
  · rw [node0270Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0013_mem
  · exact candidateIdeal.zero_mem

def node0272 : WordRow := [([1, 11, 16], 1), ([3, 7, 16], -1)]

def node0272Raw : WordRow := multiplyRow 16 node0013

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0272_check :
    collect (scaleRow 1 node0272Raw ++ scaleRow (-(1 : ℤ)) node0272 ++
      ([])) = [] := by
  decide +kernel

theorem node0272_mem : rowEval varIndex node0272 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0272Raw node0272 ([])
    (1) (1) (by decide) node0272_check
  · rw [node0272Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0013_mem
  · exact candidateIdeal.zero_mem

def node0273 : WordRow := [([1, 11, 17], 1), ([3, 7, 17], -1)]

def node0273Raw : WordRow := multiplyRow 17 node0013

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0273_check :
    collect (scaleRow 1 node0273Raw ++ scaleRow (-(1 : ℤ)) node0273 ++
      ([])) = [] := by
  decide +kernel

theorem node0273_mem : rowEval varIndex node0273 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0273Raw node0273 ([])
    (1) (1) (by decide) node0273_check
  · rw [node0273Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0013_mem
  · exact candidateIdeal.zero_mem

def node0274 : WordRow := [([1, 4, 4], 1)]

def node0274Raw : WordRow := multiplyRow 0 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0274_check :
    collect (scaleRow 1 node0274Raw ++ scaleRow (-(-1 : ℤ)) node0274 ++
      (scaleRow (-1) node0125)) = [] := by
  decide +kernel

theorem node0274_mem : rowEval varIndex node0274 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0274Raw node0274 (scaleRow (-1) node0125)
    (1) (-1) (by decide) node0274_check
  · rw [node0274Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0125 node0125_mem)

def node0275 : WordRow := [([2, 4, 5], 1)]

def node0275Raw : WordRow := multiplyRow 2 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0275_check :
    collect (scaleRow 1 node0275Raw ++ scaleRow (-(1 : ℤ)) node0275 ++
      ([])) = [] := by
  decide +kernel

theorem node0275_mem : rowEval varIndex node0275 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0275Raw node0275 ([])
    (1) (1) (by decide) node0275_check
  · rw [node0275Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0276 : WordRow := [([3, 4, 5], 1)]

def node0276Raw : WordRow := multiplyRow 3 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0276_check :
    collect (scaleRow 1 node0276Raw ++ scaleRow (-(1 : ℤ)) node0276 ++
      ([])) = [] := by
  decide +kernel

theorem node0276_mem : rowEval varIndex node0276 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0276Raw node0276 ([])
    (1) (1) (by decide) node0276_check
  · rw [node0276Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0283 : WordRow := [([4, 5, 10], 1)]

def node0283Raw : WordRow := multiplyRow 10 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0283_check :
    collect (scaleRow 1 node0283Raw ++ scaleRow (-(1 : ℤ)) node0283 ++
      ([])) = [] := by
  decide +kernel

theorem node0283_mem : rowEval varIndex node0283 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0283Raw node0283 ([])
    (1) (1) (by decide) node0283_check
  · rw [node0283Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0284 : WordRow := [([4, 5, 11], 1)]

def node0284Raw : WordRow := multiplyRow 11 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0284_check :
    collect (scaleRow 1 node0284Raw ++ scaleRow (-(1 : ℤ)) node0284 ++
      ([])) = [] := by
  decide +kernel

theorem node0284_mem : rowEval varIndex node0284 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0284Raw node0284 ([])
    (1) (1) (by decide) node0284_check
  · rw [node0284Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0287 : WordRow := [([4, 5, 14], 1)]

def node0287Raw : WordRow := multiplyRow 14 node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0287_check :
    collect (scaleRow 1 node0287Raw ++ scaleRow (-(1 : ℤ)) node0287 ++
      ([])) = [] := by
  decide +kernel

theorem node0287_mem : rowEval varIndex node0287 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0287Raw node0287 ([])
    (1) (1) (by decide) node0287_check
  · rw [node0287Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0296 : WordRow := [([5, 5, 10], 1)]

def node0296Raw : WordRow := multiplyRow 10 node0015

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0296_check :
    collect (scaleRow 1 node0296Raw ++ scaleRow (-(1 : ℤ)) node0296 ++
      ([])) = [] := by
  decide +kernel

theorem node0296_mem : rowEval varIndex node0296 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0296Raw node0296 ([])
    (1) (1) (by decide) node0296_check
  · rw [node0296Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0015_mem
  · exact candidateIdeal.zero_mem

def node0304 : WordRow := [([0, 0, 13], 1), ([0, 1, 12], 1), ([0, 4, 7], -1), ([0, 5, 6], -1)]

def node0304Raw : WordRow := multiplyRow 0 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0304_check :
    collect (scaleRow 1 node0304Raw ++ scaleRow (-(1 : ℤ)) node0304 ++
      ([])) = [] := by
  decide +kernel

theorem node0304_mem : rowEval varIndex node0304 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0304Raw node0304 ([])
    (1) (1) (by decide) node0304_check
  · rw [node0304Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0305 : WordRow := [([0, 2, 13], 1), ([1, 2, 12], 1), ([2, 4, 7], -1), ([2, 5, 6], -1)]

def node0305Raw : WordRow := multiplyRow 2 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0305_check :
    collect (scaleRow 1 node0305Raw ++ scaleRow (-(1 : ℤ)) node0305 ++
      ([])) = [] := by
  decide +kernel

theorem node0305_mem : rowEval varIndex node0305 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0305Raw node0305 ([])
    (1) (1) (by decide) node0305_check
  · rw [node0305Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0307 : WordRow := [([0, 4, 13], 1), ([1, 4, 12], 1), ([4, 4, 7], -1), ([4, 5, 6], -1)]

def node0307Raw : WordRow := multiplyRow 4 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0307_check :
    collect (scaleRow 1 node0307Raw ++ scaleRow (-(1 : ℤ)) node0307 ++
      ([])) = [] := by
  decide +kernel

theorem node0307_mem : rowEval varIndex node0307 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0307Raw node0307 ([])
    (1) (1) (by decide) node0307_check
  · rw [node0307Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0309 : WordRow := [([0, 6, 13], 1), ([1, 6, 12], 1), ([4, 6, 7], -1), ([5, 6, 6], -1)]

def node0309Raw : WordRow := multiplyRow 6 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0309_check :
    collect (scaleRow 1 node0309Raw ++ scaleRow (-(1 : ℤ)) node0309 ++
      ([])) = [] := by
  decide +kernel

theorem node0309_mem : rowEval varIndex node0309 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0309Raw node0309 ([])
    (1) (1) (by decide) node0309_check
  · rw [node0309Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0311 : WordRow := [([0, 8, 13], 1), ([1, 8, 12], 1), ([4, 7, 8], -1), ([5, 6, 8], -1)]

def node0311Raw : WordRow := multiplyRow 8 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0311_check :
    collect (scaleRow 1 node0311Raw ++ scaleRow (-(1 : ℤ)) node0311 ++
      ([])) = [] := by
  decide +kernel

theorem node0311_mem : rowEval varIndex node0311 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0311Raw node0311 ([])
    (1) (1) (by decide) node0311_check
  · rw [node0311Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0312 : WordRow := [([1, 8, 13], 1), ([1, 9, 12], -1), ([2, 5, 13], -1), ([3, 4, 13], -1), ([4, 7, 9], 1), ([5, 6, 9], 1)]

def node0312Raw : WordRow := multiplyRow 9 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0312_check :
    collect (scaleRow 1 node0312Raw ++ scaleRow (-(-1 : ℤ)) node0312 ++
      (scaleRow (-1) node0226)) = [] := by
  decide +kernel

theorem node0312_mem : rowEval varIndex node0312 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0312Raw node0312 (scaleRow (-1) node0226)
    (1) (-1) (by decide) node0312_check
  · rw [node0312Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0226 node0226_mem)

def node0313 : WordRow := [([0, 10, 13], 1), ([1, 10, 12], 1), ([4, 7, 10], -1), ([5, 6, 10], -1)]

def node0313Raw : WordRow := multiplyRow 10 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0313_check :
    collect (scaleRow 1 node0313Raw ++ scaleRow (-(1 : ℤ)) node0313 ++
      ([])) = [] := by
  decide +kernel

theorem node0313_mem : rowEval varIndex node0313 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0313Raw node0313 ([])
    (1) (1) (by decide) node0313_check
  · rw [node0313Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0315 : WordRow := [([0, 12, 13], 1), ([1, 12, 12], 1), ([4, 7, 12], -1), ([5, 6, 12], -1)]

def node0315Raw : WordRow := multiplyRow 12 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0315_check :
    collect (scaleRow 1 node0315Raw ++ scaleRow (-(1 : ℤ)) node0315 ++
      ([])) = [] := by
  decide +kernel

theorem node0315_mem : rowEval varIndex node0315 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0315Raw node0315 ([])
    (1) (1) (by decide) node0315_check
  · rw [node0315Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0317 : WordRow := [([0, 13, 14], 1), ([1, 12, 14], 1), ([4, 7, 14], -1), ([5, 6, 14], -1)]

def node0317Raw : WordRow := multiplyRow 14 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0317_check :
    collect (scaleRow 1 node0317Raw ++ scaleRow (-(1 : ℤ)) node0317 ++
      ([])) = [] := by
  decide +kernel

theorem node0317_mem : rowEval varIndex node0317 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0317Raw node0317 ([])
    (1) (1) (by decide) node0317_check
  · rw [node0317Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0319 : WordRow := [([0, 13, 16], 1), ([1, 12, 16], 1), ([4, 7, 16], -1), ([5, 6, 16], -1)]

def node0319Raw : WordRow := multiplyRow 16 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0319_check :
    collect (scaleRow 1 node0319Raw ++ scaleRow (-(1 : ℤ)) node0319 ++
      ([])) = [] := by
  decide +kernel

theorem node0319_mem : rowEval varIndex node0319 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0319Raw node0319 ([])
    (1) (1) (by decide) node0319_check
  · rw [node0319Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0320 : WordRow := [([0, 13, 17], 1), ([1, 12, 17], 1), ([4, 7, 17], -1), ([5, 6, 17], -1)]

def node0320Raw : WordRow := multiplyRow 17 node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0320_check :
    collect (scaleRow 1 node0320Raw ++ scaleRow (-(1 : ℤ)) node0320 ++
      ([])) = [] := by
  decide +kernel

theorem node0320_mem : rowEval varIndex node0320 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0320Raw node0320 ([])
    (1) (1) (by decide) node0320_check
  · rw [node0320Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0323 : WordRow := [([2, 5, 13], 1), ([3, 4, 13], 1), ([3, 5, 12], 1), ([4, 7, 9], -1), ([5, 6, 9], -1), ([5, 7, 8], -1)]

def node0323Raw : WordRow := multiplyRow 8 node0017

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0323_check :
    collect (scaleRow 1 node0323Raw ++ scaleRow (-(1 : ℤ)) node0323 ++
      (scaleRow (-1) node0312 ++ scaleRow (-1) node0239)) = [] := by
  decide +kernel

theorem node0323_mem : rowEval varIndex node0323 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0323Raw node0323 (scaleRow (-1) node0312 ++ scaleRow (-1) node0239)
    (1) (1) (by decide) node0323_check
  · rw [node0323Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0017_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0312 node0312_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0239 node0239_mem))

def node0331 : WordRow := [([1, 13, 16], 1), ([5, 7, 16], -1)]

def node0331Raw : WordRow := multiplyRow 16 node0017

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0331_check :
    collect (scaleRow 1 node0331Raw ++ scaleRow (-(1 : ℤ)) node0331 ++
      ([])) = [] := by
  decide +kernel

theorem node0331_mem : rowEval varIndex node0331 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0331Raw node0331 ([])
    (1) (1) (by decide) node0331_check
  · rw [node0331Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0017_mem
  · exact candidateIdeal.zero_mem

def node0332 : WordRow := [([1, 13, 17], 1), ([5, 7, 17], -1)]

def node0332Raw : WordRow := multiplyRow 17 node0017

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0332_check :
    collect (scaleRow 1 node0332Raw ++ scaleRow (-(1 : ℤ)) node0332 ++
      ([])) = [] := by
  decide +kernel

theorem node0332_mem : rowEval varIndex node0332 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0332Raw node0332 ([])
    (1) (1) (by decide) node0332_check
  · rw [node0332Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0017_mem
  · exact candidateIdeal.zero_mem

def node0333 : WordRow := [([1, 6, 6], 1)]

def node0333Raw : WordRow := multiplyRow 0 node0018

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0333_check :
    collect (scaleRow 1 node0333Raw ++ scaleRow (-(-1 : ℤ)) node0333 ++
      (scaleRow (-1) node0158)) = [] := by
  decide +kernel

theorem node0333_mem : rowEval varIndex node0333 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0333Raw node0333 (scaleRow (-1) node0158)
    (1) (-1) (by decide) node0333_check
  · rw [node0333Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0018_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0158 node0158_mem)

def node0334 : WordRow := [([2, 6, 7], 1)]

def node0334Raw : WordRow := multiplyRow 2 node0018

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0334_check :
    collect (scaleRow 1 node0334Raw ++ scaleRow (-(1 : ℤ)) node0334 ++
      ([])) = [] := by
  decide +kernel

theorem node0334_mem : rowEval varIndex node0334 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0334Raw node0334 ([])
    (1) (1) (by decide) node0334_check
  · rw [node0334Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0018_mem
  · exact candidateIdeal.zero_mem

def node0336 : WordRow := [([4, 6, 7], 1)]

def node0336Raw : WordRow := multiplyRow 4 node0018

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0336_check :
    collect (scaleRow 1 node0336Raw ++ scaleRow (-(1 : ℤ)) node0336 ++
      ([])) = [] := by
  decide +kernel

theorem node0336_mem : rowEval varIndex node0336 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0336Raw node0336 ([])
    (1) (1) (by decide) node0336_check
  · rw [node0336Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0018_mem
  · exact candidateIdeal.zero_mem

def node0340 : WordRow := [([6, 7, 8], 1)]

def node0340Raw : WordRow := multiplyRow 8 node0018

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0340_check :
    collect (scaleRow 1 node0340Raw ++ scaleRow (-(1 : ℤ)) node0340 ++
      ([])) = [] := by
  decide +kernel

theorem node0340_mem : rowEval varIndex node0340 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0340Raw node0340 ([])
    (1) (1) (by decide) node0340_check
  · rw [node0340Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0018_mem
  · exact candidateIdeal.zero_mem

def node0346 : WordRow := [([6, 7, 14], 1)]

def node0346Raw : WordRow := multiplyRow 14 node0018

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0346_check :
    collect (scaleRow 1 node0346Raw ++ scaleRow (-(1 : ℤ)) node0346 ++
      ([])) = [] := by
  decide +kernel

theorem node0346_mem : rowEval varIndex node0346 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0346Raw node0346 ([])
    (1) (1) (by decide) node0346_check
  · rw [node0346Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0018_mem
  · exact candidateIdeal.zero_mem

def node0361 : WordRow := [([1, 2, 8], 2), ([2, 2, 5], -1), ([2, 3, 4], -1)]

def node0361Raw : WordRow := multiplyRow 0 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0361_check :
    collect (scaleRow 1 node0361Raw ++ scaleRow (-(-1 : ℤ)) node0361 ++
      (scaleRow (-1) node0215 ++ scaleRow (-1) node0096)) = [] := by
  decide +kernel

theorem node0361_mem : rowEval varIndex node0361 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0361Raw node0361 (scaleRow (-1) node0215 ++ scaleRow (-1) node0096)
    (1) (-1) (by decide) node0361_check
  · rw [node0361Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0215 node0215_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0096 node0096_mem))

def node0363 : WordRow := [([2, 4, 9], 1), ([3, 4, 8], 1)]

def node0363Raw : WordRow := multiplyRow 4 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0363_check :
    collect (scaleRow 1 node0363Raw ++ scaleRow (-(1 : ℤ)) node0363 ++
      ([])) = [] := by
  decide +kernel

theorem node0363_mem : rowEval varIndex node0363 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0363Raw node0363 ([])
    (1) (1) (by decide) node0363_check
  · rw [node0363Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0365 : WordRow := [([2, 6, 9], 1), ([3, 6, 8], 1)]

def node0365Raw : WordRow := multiplyRow 6 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0365_check :
    collect (scaleRow 1 node0365Raw ++ scaleRow (-(1 : ℤ)) node0365 ++
      ([])) = [] := by
  decide +kernel

theorem node0365_mem : rowEval varIndex node0365 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0365Raw node0365 ([])
    (1) (1) (by decide) node0365_check
  · rw [node0365Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0366 : WordRow := [([2, 7, 9], 1), ([3, 7, 8], 1)]

def node0366Raw : WordRow := multiplyRow 7 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0366_check :
    collect (scaleRow 1 node0366Raw ++ scaleRow (-(1 : ℤ)) node0366 ++
      ([])) = [] := by
  decide +kernel

theorem node0366_mem : rowEval varIndex node0366 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0366Raw node0366 ([])
    (1) (1) (by decide) node0366_check
  · rw [node0366Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0367 : WordRow := [([2, 8, 9], 1), ([3, 8, 8], 1)]

def node0367Raw : WordRow := multiplyRow 8 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0367_check :
    collect (scaleRow 1 node0367Raw ++ scaleRow (-(1 : ℤ)) node0367 ++
      ([])) = [] := by
  decide +kernel

theorem node0367_mem : rowEval varIndex node0367 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0367Raw node0367 ([])
    (1) (1) (by decide) node0367_check
  · rw [node0367Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0369 : WordRow := [([2, 9, 10], 1), ([3, 8, 10], 1)]

def node0369Raw : WordRow := multiplyRow 10 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0369_check :
    collect (scaleRow 1 node0369Raw ++ scaleRow (-(1 : ℤ)) node0369 ++
      ([])) = [] := by
  decide +kernel

theorem node0369_mem : rowEval varIndex node0369 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0369Raw node0369 ([])
    (1) (1) (by decide) node0369_check
  · rw [node0369Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0370 : WordRow := [([2, 9, 11], 1), ([3, 8, 11], 1)]

def node0370Raw : WordRow := multiplyRow 11 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0370_check :
    collect (scaleRow 1 node0370Raw ++ scaleRow (-(1 : ℤ)) node0370 ++
      ([])) = [] := by
  decide +kernel

theorem node0370_mem : rowEval varIndex node0370 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0370Raw node0370 ([])
    (1) (1) (by decide) node0370_check
  · rw [node0370Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0371 : WordRow := [([2, 9, 12], 1), ([3, 8, 12], 1)]

def node0371Raw : WordRow := multiplyRow 12 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0371_check :
    collect (scaleRow 1 node0371Raw ++ scaleRow (-(1 : ℤ)) node0371 ++
      ([])) = [] := by
  decide +kernel

theorem node0371_mem : rowEval varIndex node0371 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0371Raw node0371 ([])
    (1) (1) (by decide) node0371_check
  · rw [node0371Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0372 : WordRow := [([2, 9, 13], 1), ([3, 8, 13], 1)]

def node0372Raw : WordRow := multiplyRow 13 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0372_check :
    collect (scaleRow 1 node0372Raw ++ scaleRow (-(1 : ℤ)) node0372 ++
      ([])) = [] := by
  decide +kernel

theorem node0372_mem : rowEval varIndex node0372 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0372Raw node0372 ([])
    (1) (1) (by decide) node0372_check
  · rw [node0372Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0373 : WordRow := [([2, 9, 14], 1), ([3, 8, 14], 1)]

def node0373Raw : WordRow := multiplyRow 14 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0373_check :
    collect (scaleRow 1 node0373Raw ++ scaleRow (-(1 : ℤ)) node0373 ++
      ([])) = [] := by
  decide +kernel

theorem node0373_mem : rowEval varIndex node0373 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0373Raw node0373 ([])
    (1) (1) (by decide) node0373_check
  · rw [node0373Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0375 : WordRow := [([2, 9, 16], 1), ([3, 8, 16], 1)]

def node0375Raw : WordRow := multiplyRow 16 node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0375_check :
    collect (scaleRow 1 node0375Raw ++ scaleRow (-(1 : ℤ)) node0375 ++
      ([])) = [] := by
  decide +kernel

theorem node0375_mem : rowEval varIndex node0375 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0375Raw node0375 ([])
    (1) (1) (by decide) node0375_check
  · rw [node0375Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0377 : WordRow := [([3, 4, 9], 1)]

def node0377Raw : WordRow := multiplyRow 4 node0021

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0377_check :
    collect (scaleRow 1 node0377Raw ++ scaleRow (-(1 : ℤ)) node0377 ++
      ([])) = [] := by
  decide +kernel

theorem node0377_mem : rowEval varIndex node0377 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0377Raw node0377 ([])
    (1) (1) (by decide) node0377_check
  · rw [node0377Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0021_mem
  · exact candidateIdeal.zero_mem

def node0379 : WordRow := [([3, 6, 9], 1)]

def node0379Raw : WordRow := multiplyRow 6 node0021

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0379_check :
    collect (scaleRow 1 node0379Raw ++ scaleRow (-(1 : ℤ)) node0379 ++
      ([])) = [] := by
  decide +kernel

theorem node0379_mem : rowEval varIndex node0379 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0379Raw node0379 ([])
    (1) (1) (by decide) node0379_check
  · rw [node0379Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0021_mem
  · exact candidateIdeal.zero_mem

def node0385 : WordRow := [([3, 9, 12], 1)]

def node0385Raw : WordRow := multiplyRow 12 node0021

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0385_check :
    collect (scaleRow 1 node0385Raw ++ scaleRow (-(1 : ℤ)) node0385 ++
      ([])) = [] := by
  decide +kernel

theorem node0385_mem : rowEval varIndex node0385 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0385Raw node0385 ([])
    (1) (1) (by decide) node0385_check
  · rw [node0385Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0021_mem
  · exact candidateIdeal.zero_mem

def node0391 : WordRow := [([1, 2, 10], 2), ([2, 2, 7], -1), ([2, 3, 6], -1)]

def node0391Raw : WordRow := multiplyRow 0 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0391_check :
    collect (scaleRow 1 node0391Raw ++ scaleRow (-(-1 : ℤ)) node0391 ++
      (scaleRow (-1) node0246 ++ scaleRow (-1) node0098)) = [] := by
  decide +kernel

theorem node0391_mem : rowEval varIndex node0391 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0391Raw node0391 (scaleRow (-1) node0246 ++ scaleRow (-1) node0098)
    (1) (-1) (by decide) node0391_check
  · rw [node0391Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0246 node0246_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0098 node0098_mem))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0391_mem
