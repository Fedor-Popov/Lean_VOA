import VOA.DeligneAudit.D4FusionContactM2Dag02

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0393 : WordRow := [([2, 4, 11], 1), ([3, 4, 10], 1)]

def node0393Raw : WordRow := multiplyRow 4 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0393_check :
    collect (scaleRow 1 node0393Raw ++ scaleRow (-(1 : ℤ)) node0393 ++
      ([])) = [] := by
  decide +kernel

theorem node0393_mem : rowEval varIndex node0393 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0393Raw node0393 ([])
    (1) (1) (by decide) node0393_check
  · rw [node0393Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0394 : WordRow := [([3, 4, 11], 1), ([3, 6, 9], -1)]

def node0394Raw : WordRow := multiplyRow 5 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0394_check :
    collect (scaleRow 1 node0394Raw ++ scaleRow (-(-1 : ℤ)) node0394 ++
      (scaleRow (-1) node0264 ++ scaleRow (-1) node0366)) = [] := by
  decide +kernel

theorem node0394_mem : rowEval varIndex node0394 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0394Raw node0394 (scaleRow (-1) node0264 ++ scaleRow (-1) node0366)
    (1) (-1) (by decide) node0394_check
  · rw [node0394Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0264 node0264_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0366 node0366_mem))

def node0395 : WordRow := [([2, 6, 11], 1), ([3, 6, 10], 1)]

def node0395Raw : WordRow := multiplyRow 6 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0395_check :
    collect (scaleRow 1 node0395Raw ++ scaleRow (-(1 : ℤ)) node0395 ++
      ([])) = [] := by
  decide +kernel

theorem node0395_mem : rowEval varIndex node0395 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0395Raw node0395 ([])
    (1) (1) (by decide) node0395_check
  · rw [node0395Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0397 : WordRow := [([2, 8, 11], 1), ([3, 8, 10], 1)]

def node0397Raw : WordRow := multiplyRow 8 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0397_check :
    collect (scaleRow 1 node0397Raw ++ scaleRow (-(1 : ℤ)) node0397 ++
      ([])) = [] := by
  decide +kernel

theorem node0397_mem : rowEval varIndex node0397 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0397Raw node0397 ([])
    (1) (1) (by decide) node0397_check
  · rw [node0397Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0399 : WordRow := [([2, 10, 11], 1), ([3, 10, 10], 1)]

def node0399Raw : WordRow := multiplyRow 10 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0399_check :
    collect (scaleRow 1 node0399Raw ++ scaleRow (-(1 : ℤ)) node0399 ++
      ([])) = [] := by
  decide +kernel

theorem node0399_mem : rowEval varIndex node0399 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0399Raw node0399 ([])
    (1) (1) (by decide) node0399_check
  · rw [node0399Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0401 : WordRow := [([2, 11, 12], 1), ([3, 10, 12], 1)]

def node0401Raw : WordRow := multiplyRow 12 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0401_check :
    collect (scaleRow 1 node0401Raw ++ scaleRow (-(1 : ℤ)) node0401 ++
      ([])) = [] := by
  decide +kernel

theorem node0401_mem : rowEval varIndex node0401 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0401Raw node0401 ([])
    (1) (1) (by decide) node0401_check
  · rw [node0401Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0402 : WordRow := [([2, 11, 13], 1), ([3, 10, 13], 1)]

def node0402Raw : WordRow := multiplyRow 13 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0402_check :
    collect (scaleRow 1 node0402Raw ++ scaleRow (-(1 : ℤ)) node0402 ++
      ([])) = [] := by
  decide +kernel

theorem node0402_mem : rowEval varIndex node0402 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0402Raw node0402 ([])
    (1) (1) (by decide) node0402_check
  · rw [node0402Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0403 : WordRow := [([2, 11, 14], 1), ([3, 10, 14], 1)]

def node0403Raw : WordRow := multiplyRow 14 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0403_check :
    collect (scaleRow 1 node0403Raw ++ scaleRow (-(1 : ℤ)) node0403 ++
      ([])) = [] := by
  decide +kernel

theorem node0403_mem : rowEval varIndex node0403 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0403Raw node0403 ([])
    (1) (1) (by decide) node0403_check
  · rw [node0403Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0405 : WordRow := [([2, 11, 16], 1), ([3, 10, 16], 1)]

def node0405Raw : WordRow := multiplyRow 16 node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0405_check :
    collect (scaleRow 1 node0405Raw ++ scaleRow (-(1 : ℤ)) node0405 ++
      ([])) = [] := by
  decide +kernel

theorem node0405_mem : rowEval varIndex node0405 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0405Raw node0405 ([])
    (1) (1) (by decide) node0405_check
  · rw [node0405Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0407 : WordRow := [([3, 6, 11], 1)]

def node0407Raw : WordRow := multiplyRow 6 node0023

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0407_check :
    collect (scaleRow 1 node0407Raw ++ scaleRow (-(1 : ℤ)) node0407 ++
      ([])) = [] := by
  decide +kernel

theorem node0407_mem : rowEval varIndex node0407 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0407Raw node0407 ([])
    (1) (1) (by decide) node0407_check
  · rw [node0407Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0023_mem
  · exact candidateIdeal.zero_mem

def node0417 : WordRow := [([1, 4, 8], 2), ([2, 4, 5], -1), ([3, 4, 4], -1)]

def node0417Raw : WordRow := multiplyRow 0 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0417_check :
    collect (scaleRow 1 node0417Raw ++ scaleRow (-(-1 : ℤ)) node0417 ++
      (scaleRow (-1) node0217 ++ scaleRow (-1) node0129)) = [] := by
  decide +kernel

theorem node0417_mem : rowEval varIndex node0417 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0417Raw node0417 (scaleRow (-1) node0217 ++ scaleRow (-1) node0129)
    (1) (-1) (by decide) node0417_check
  · rw [node0417Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0217 node0217_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0129 node0129_mem))

def node0418 : WordRow := [([2, 5, 8], 1), ([3, 4, 8], -1)]

def node0418Raw : WordRow := multiplyRow 2 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0418_check :
    collect (scaleRow 1 node0418Raw ++ scaleRow (-(1 : ℤ)) node0418 ++
      (scaleRow (-1) node0363)) = [] := by
  decide +kernel

theorem node0418_mem : rowEval varIndex node0418 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0418Raw node0418 (scaleRow (-1) node0363)
    (1) (1) (by decide) node0418_check
  · rw [node0418Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0363 node0363_mem)

def node0419 : WordRow := [([3, 5, 8], 1)]

def node0419Raw : WordRow := multiplyRow 3 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0419_check :
    collect (scaleRow 1 node0419Raw ++ scaleRow (-(1 : ℤ)) node0419 ++
      (scaleRow (-1) node0377)) = [] := by
  decide +kernel

theorem node0419_mem : rowEval varIndex node0419 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0419Raw node0419 (scaleRow (-1) node0377)
    (1) (1) (by decide) node0419_check
  · rw [node0419Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0377 node0377_mem)

def node0421 : WordRow := [([4, 6, 9], 1), ([5, 6, 8], 1)]

def node0421Raw : WordRow := multiplyRow 6 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0421_check :
    collect (scaleRow 1 node0421Raw ++ scaleRow (-(1 : ℤ)) node0421 ++
      ([])) = [] := by
  decide +kernel

theorem node0421_mem : rowEval varIndex node0421 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0421Raw node0421 ([])
    (1) (1) (by decide) node0421_check
  · rw [node0421Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0422 : WordRow := [([4, 7, 9], 1), ([5, 7, 8], 1)]

def node0422Raw : WordRow := multiplyRow 7 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0422_check :
    collect (scaleRow 1 node0422Raw ++ scaleRow (-(1 : ℤ)) node0422 ++
      ([])) = [] := by
  decide +kernel

theorem node0422_mem : rowEval varIndex node0422 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0422Raw node0422 ([])
    (1) (1) (by decide) node0422_check
  · rw [node0422Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0423 : WordRow := [([4, 8, 9], 1), ([5, 8, 8], 1)]

def node0423Raw : WordRow := multiplyRow 8 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0423_check :
    collect (scaleRow 1 node0423Raw ++ scaleRow (-(1 : ℤ)) node0423 ++
      ([])) = [] := by
  decide +kernel

theorem node0423_mem : rowEval varIndex node0423 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0423Raw node0423 ([])
    (1) (1) (by decide) node0423_check
  · rw [node0423Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0425 : WordRow := [([4, 9, 10], 1), ([5, 8, 10], 1)]

def node0425Raw : WordRow := multiplyRow 10 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0425_check :
    collect (scaleRow 1 node0425Raw ++ scaleRow (-(1 : ℤ)) node0425 ++
      ([])) = [] := by
  decide +kernel

theorem node0425_mem : rowEval varIndex node0425 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0425Raw node0425 ([])
    (1) (1) (by decide) node0425_check
  · rw [node0425Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0426 : WordRow := [([4, 9, 11], 1), ([5, 8, 11], 1)]

def node0426Raw : WordRow := multiplyRow 11 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0426_check :
    collect (scaleRow 1 node0426Raw ++ scaleRow (-(1 : ℤ)) node0426 ++
      ([])) = [] := by
  decide +kernel

theorem node0426_mem : rowEval varIndex node0426 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0426Raw node0426 ([])
    (1) (1) (by decide) node0426_check
  · rw [node0426Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0427 : WordRow := [([4, 9, 12], 1), ([5, 8, 12], 1)]

def node0427Raw : WordRow := multiplyRow 12 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0427_check :
    collect (scaleRow 1 node0427Raw ++ scaleRow (-(1 : ℤ)) node0427 ++
      ([])) = [] := by
  decide +kernel

theorem node0427_mem : rowEval varIndex node0427 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0427Raw node0427 ([])
    (1) (1) (by decide) node0427_check
  · rw [node0427Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0428 : WordRow := [([4, 9, 13], 1), ([5, 8, 13], 1)]

def node0428Raw : WordRow := multiplyRow 13 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0428_check :
    collect (scaleRow 1 node0428Raw ++ scaleRow (-(1 : ℤ)) node0428 ++
      ([])) = [] := by
  decide +kernel

theorem node0428_mem : rowEval varIndex node0428 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0428Raw node0428 ([])
    (1) (1) (by decide) node0428_check
  · rw [node0428Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0429 : WordRow := [([4, 9, 14], 1), ([5, 8, 14], 1)]

def node0429Raw : WordRow := multiplyRow 14 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0429_check :
    collect (scaleRow 1 node0429Raw ++ scaleRow (-(1 : ℤ)) node0429 ++
      ([])) = [] := by
  decide +kernel

theorem node0429_mem : rowEval varIndex node0429 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0429Raw node0429 ([])
    (1) (1) (by decide) node0429_check
  · rw [node0429Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0431 : WordRow := [([4, 9, 16], 1), ([5, 8, 16], 1)]

def node0431Raw : WordRow := multiplyRow 16 node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0431_check :
    collect (scaleRow 1 node0431Raw ++ scaleRow (-(1 : ℤ)) node0431 ++
      ([])) = [] := by
  decide +kernel

theorem node0431_mem : rowEval varIndex node0431 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0431Raw node0431 ([])
    (1) (1) (by decide) node0431_check
  · rw [node0431Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0433 : WordRow := [([5, 6, 9], 1)]

def node0433Raw : WordRow := multiplyRow 6 node0025

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0433_check :
    collect (scaleRow 1 node0433Raw ++ scaleRow (-(1 : ℤ)) node0433 ++
      ([])) = [] := by
  decide +kernel

theorem node0433_mem : rowEval varIndex node0433 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0433Raw node0433 ([])
    (1) (1) (by decide) node0433_check
  · rw [node0433Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0025_mem
  · exact candidateIdeal.zero_mem

def node0445 : WordRow := [([0, 0, 15], 1), ([0, 1, 14], 1), ([0, 2, 13], -1), ([0, 3, 12], -1), ([0, 4, 11], -1), ([0, 5, 10], -1), ([0, 6, 9], -1), ([0, 7, 8], -1)]

def node0445Raw : WordRow := multiplyRow 0 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0445_check :
    collect (scaleRow 1 node0445Raw ++ scaleRow (-(1 : ℤ)) node0445 ++
      ([])) = [] := by
  decide +kernel

theorem node0445_mem : rowEval varIndex node0445 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0445Raw node0445 ([])
    (1) (1) (by decide) node0445_check
  · rw [node0445Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0446 : WordRow := [([0, 2, 15], 1), ([1, 2, 14], 1), ([2, 2, 13], -1), ([2, 3, 12], -1), ([2, 4, 11], -1), ([2, 5, 10], -1), ([2, 6, 9], -1), ([2, 7, 8], -1)]

def node0446Raw : WordRow := multiplyRow 2 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0446_check :
    collect (scaleRow 1 node0446Raw ++ scaleRow (-(1 : ℤ)) node0446 ++
      ([])) = [] := by
  decide +kernel

theorem node0446_mem : rowEval varIndex node0446 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0446Raw node0446 ([])
    (1) (1) (by decide) node0446_check
  · rw [node0446Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0448 : WordRow := [([0, 4, 15], 1), ([1, 4, 14], 1), ([2, 4, 13], -1), ([3, 4, 12], -1), ([4, 4, 11], -1), ([4, 5, 10], -1), ([4, 6, 9], -1), ([4, 7, 8], -1)]

def node0448Raw : WordRow := multiplyRow 4 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0448_check :
    collect (scaleRow 1 node0448Raw ++ scaleRow (-(1 : ℤ)) node0448 ++
      ([])) = [] := by
  decide +kernel

theorem node0448_mem : rowEval varIndex node0448 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0448Raw node0448 ([])
    (1) (1) (by decide) node0448_check
  · rw [node0448Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0449 : WordRow := [([1, 4, 15], 1), ([1, 5, 14], -1), ([2, 5, 13], 1), ([3, 5, 12], 1), ([4, 5, 11], 1), ([5, 5, 10], 1), ([5, 6, 9], 1), ([5, 7, 8], 1)]

def node0449Raw : WordRow := multiplyRow 5 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0449_check :
    collect (scaleRow 1 node0449Raw ++ scaleRow (-(-1 : ℤ)) node0449 ++
      (scaleRow (-1) node0136)) = [] := by
  decide +kernel

theorem node0449_mem : rowEval varIndex node0449 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0449Raw node0449 (scaleRow (-1) node0136)
    (1) (-1) (by decide) node0449_check
  · rw [node0449Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0136 node0136_mem)

def node0450 : WordRow := [([0, 6, 15], 1), ([1, 6, 14], 1), ([2, 6, 13], -1), ([3, 6, 12], -1), ([4, 6, 11], -1), ([5, 6, 10], -1), ([6, 6, 9], -1), ([6, 7, 8], -1)]

def node0450Raw : WordRow := multiplyRow 6 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0450_check :
    collect (scaleRow 1 node0450Raw ++ scaleRow (-(1 : ℤ)) node0450 ++
      ([])) = [] := by
  decide +kernel

theorem node0450_mem : rowEval varIndex node0450 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0450Raw node0450 ([])
    (1) (1) (by decide) node0450_check
  · rw [node0450Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0452 : WordRow := [([0, 8, 15], 1), ([1, 8, 14], 1), ([2, 8, 13], -1), ([3, 8, 12], -1), ([4, 8, 11], -1), ([5, 8, 10], -1), ([6, 8, 9], -1), ([7, 8, 8], -1)]

def node0452Raw : WordRow := multiplyRow 8 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0452_check :
    collect (scaleRow 1 node0452Raw ++ scaleRow (-(1 : ℤ)) node0452 ++
      ([])) = [] := by
  decide +kernel

theorem node0452_mem : rowEval varIndex node0452 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0452Raw node0452 ([])
    (1) (1) (by decide) node0452_check
  · rw [node0452Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0453 : WordRow := [([1, 8, 15], 1), ([1, 9, 14], -1), ([2, 5, 15], -1), ([2, 9, 13], 1), ([3, 4, 15], -1), ([3, 9, 12], 1), ([4, 9, 11], 1), ([5, 9, 10], 1), ([6, 9, 9], 1), ([7, 8, 9], 1)]

def node0453Raw : WordRow := multiplyRow 9 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0453_check :
    collect (scaleRow 1 node0453Raw ++ scaleRow (-(-1 : ℤ)) node0453 ++
      (scaleRow (-1) node0228)) = [] := by
  decide +kernel

theorem node0453_mem : rowEval varIndex node0453 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0453Raw node0453 (scaleRow (-1) node0228)
    (1) (-1) (by decide) node0453_check
  · rw [node0453Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0228 node0228_mem)

def node0454 : WordRow := [([0, 10, 15], 1), ([1, 10, 14], 1), ([2, 10, 13], -1), ([3, 10, 12], -1), ([4, 10, 11], -1), ([5, 10, 10], -1), ([6, 9, 10], -1), ([7, 8, 10], -1)]

def node0454Raw : WordRow := multiplyRow 10 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0454_check :
    collect (scaleRow 1 node0454Raw ++ scaleRow (-(1 : ℤ)) node0454 ++
      ([])) = [] := by
  decide +kernel

theorem node0454_mem : rowEval varIndex node0454 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0454Raw node0454 ([])
    (1) (1) (by decide) node0454_check
  · rw [node0454Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0455 : WordRow := [([1, 10, 15], 1), ([1, 11, 14], -1), ([2, 7, 15], -1), ([2, 11, 13], 1), ([3, 6, 15], -1), ([3, 11, 12], 1), ([4, 11, 11], 1), ([5, 10, 11], 1), ([6, 9, 11], 1), ([7, 8, 11], 1)]

def node0455Raw : WordRow := multiplyRow 11 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0455_check :
    collect (scaleRow 1 node0455Raw ++ scaleRow (-(-1 : ℤ)) node0455 ++
      (scaleRow (-1) node0259)) = [] := by
  decide +kernel

theorem node0455_mem : rowEval varIndex node0455 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0455Raw node0455 (scaleRow (-1) node0259)
    (1) (-1) (by decide) node0455_check
  · rw [node0455Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0259 node0259_mem)

def node0456 : WordRow := [([0, 12, 15], 1), ([1, 12, 14], 1), ([2, 12, 13], -1), ([3, 12, 12], -1), ([4, 11, 12], -1), ([5, 10, 12], -1), ([6, 9, 12], -1), ([7, 8, 12], -1)]

def node0456Raw : WordRow := multiplyRow 12 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0456_check :
    collect (scaleRow 1 node0456Raw ++ scaleRow (-(1 : ℤ)) node0456 ++
      ([])) = [] := by
  decide +kernel

theorem node0456_mem : rowEval varIndex node0456 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0456Raw node0456 ([])
    (1) (1) (by decide) node0456_check
  · rw [node0456Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0458 : WordRow := [([0, 14, 15], 1), ([1, 14, 14], 1), ([2, 13, 14], -1), ([3, 12, 14], -1), ([4, 11, 14], -1), ([5, 10, 14], -1), ([6, 9, 14], -1), ([7, 8, 14], -1)]

def node0458Raw : WordRow := multiplyRow 14 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0458_check :
    collect (scaleRow 1 node0458Raw ++ scaleRow (-(1 : ℤ)) node0458 ++
      ([])) = [] := by
  decide +kernel

theorem node0458_mem : rowEval varIndex node0458 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0458Raw node0458 ([])
    (1) (1) (by decide) node0458_check
  · rw [node0458Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0460 : WordRow := [([0, 15, 16], 1), ([1, 14, 16], 1), ([2, 13, 16], -1), ([3, 12, 16], -1), ([4, 11, 16], -1), ([5, 10, 16], -1), ([6, 9, 16], -1), ([7, 8, 16], -1)]

def node0460Raw : WordRow := multiplyRow 16 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0460_check :
    collect (scaleRow 1 node0460Raw ++ scaleRow (-(1 : ℤ)) node0460 ++
      ([])) = [] := by
  decide +kernel

theorem node0460_mem : rowEval varIndex node0460 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0460Raw node0460 ([])
    (1) (1) (by decide) node0460_check
  · rw [node0460Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0461 : WordRow := [([0, 15, 17], 1), ([1, 14, 17], 1), ([2, 13, 17], -1), ([3, 12, 17], -1), ([4, 11, 17], -1), ([5, 10, 17], -1), ([6, 9, 17], -1), ([7, 8, 17], -1)]

def node0461Raw : WordRow := multiplyRow 17 node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0461_check :
    collect (scaleRow 1 node0461Raw ++ scaleRow (-(1 : ℤ)) node0461 ++
      ([])) = [] := by
  decide +kernel

theorem node0461_mem : rowEval varIndex node0461 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0461Raw node0461 ([])
    (1) (1) (by decide) node0461_check
  · rw [node0461Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0464 : WordRow := [([2, 5, 15], 1), ([2, 9, 13], -1), ([3, 4, 15], 1), ([3, 5, 14], 1), ([3, 8, 13], -1), ([3, 9, 12], -1), ([4, 9, 11], -1), ([5, 8, 11], -1), ([5, 9, 10], -1), ([6, 9, 9], -1), ([7, 8, 9], -2)]

def node0464Raw : WordRow := multiplyRow 8 node0027

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0464_check :
    collect (scaleRow 1 node0464Raw ++ scaleRow (-(1 : ℤ)) node0464 ++
      (scaleRow (-1) node0453 ++ scaleRow (-1) node0241)) = [] := by
  decide +kernel

theorem node0464_mem : rowEval varIndex node0464 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0464Raw node0464 (scaleRow (-1) node0453 ++ scaleRow (-1) node0241)
    (1) (1) (by decide) node0464_check
  · rw [node0464Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0027_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0453 node0453_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0241 node0241_mem))

def node0466 : WordRow := [([2, 7, 15], 1), ([2, 11, 13], -1), ([3, 6, 15], 1), ([3, 7, 14], 1), ([3, 10, 13], -1), ([3, 11, 12], -1), ([4, 11, 11], -1), ([5, 10, 11], -2), ([6, 9, 11], -1), ([7, 8, 11], -1), ([7, 9, 10], -1)]

def node0466Raw : WordRow := multiplyRow 10 node0027

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0466_check :
    collect (scaleRow 1 node0466Raw ++ scaleRow (-(1 : ℤ)) node0466 ++
      (scaleRow (-1) node0455 ++ scaleRow (-1) node0270)) = [] := by
  decide +kernel

theorem node0466_mem : rowEval varIndex node0466 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0466Raw node0466 (scaleRow (-1) node0455 ++ scaleRow (-1) node0270)
    (1) (1) (by decide) node0466_check
  · rw [node0466Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0027_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0455 node0455_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0270 node0270_mem))

def node0472 : WordRow := [([1, 15, 16], 1), ([3, 13, 16], -1), ([5, 11, 16], -1), ([7, 9, 16], -1)]

def node0472Raw : WordRow := multiplyRow 16 node0027

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0472_check :
    collect (scaleRow 1 node0472Raw ++ scaleRow (-(1 : ℤ)) node0472 ++
      ([])) = [] := by
  decide +kernel

theorem node0472_mem : rowEval varIndex node0472 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0472Raw node0472 ([])
    (1) (1) (by decide) node0472_check
  · rw [node0472Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0027_mem
  · exact candidateIdeal.zero_mem

def node0473 : WordRow := [([1, 15, 17], 1), ([3, 13, 17], -1), ([5, 11, 17], -1), ([7, 9, 17], -1)]

def node0473Raw : WordRow := multiplyRow 17 node0027

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0473_check :
    collect (scaleRow 1 node0473Raw ++ scaleRow (-(1 : ℤ)) node0473 ++
      ([])) = [] := by
  decide +kernel

theorem node0473_mem : rowEval varIndex node0473 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0473Raw node0473 ([])
    (1) (1) (by decide) node0473_check
  · rw [node0473Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0027_mem
  · exact candidateIdeal.zero_mem

def node0474 : WordRow := [([1, 6, 10], 2), ([2, 6, 7], -1), ([3, 6, 6], -1)]

def node0474Raw : WordRow := multiplyRow 0 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0474_check :
    collect (scaleRow 1 node0474Raw ++ scaleRow (-(-1 : ℤ)) node0474 ++
      (scaleRow (-1) node0250 ++ scaleRow (-1) node0162)) = [] := by
  decide +kernel

theorem node0474_mem : rowEval varIndex node0474 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0474Raw node0474 (scaleRow (-1) node0250 ++ scaleRow (-1) node0162)
    (1) (-1) (by decide) node0474_check
  · rw [node0474Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0250 node0250_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0162 node0162_mem))

def node0475 : WordRow := [([2, 7, 10], 1), ([3, 6, 10], -1)]

def node0475Raw : WordRow := multiplyRow 2 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0475_check :
    collect (scaleRow 1 node0475Raw ++ scaleRow (-(1 : ℤ)) node0475 ++
      (scaleRow (-1) node0395)) = [] := by
  decide +kernel

theorem node0475_mem : rowEval varIndex node0475 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0475Raw node0475 (scaleRow (-1) node0395)
    (1) (1) (by decide) node0475_check
  · rw [node0475Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0395 node0395_mem)

def node0476 : WordRow := [([3, 7, 10], 1)]

def node0476Raw : WordRow := multiplyRow 3 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0476_check :
    collect (scaleRow 1 node0476Raw ++ scaleRow (-(1 : ℤ)) node0476 ++
      (scaleRow (-1) node0407)) = [] := by
  decide +kernel

theorem node0476_mem : rowEval varIndex node0476 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0476Raw node0476 (scaleRow (-1) node0407)
    (1) (1) (by decide) node0476_check
  · rw [node0476Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0407 node0407_mem)

def node0477 : WordRow := [([4, 6, 11], 1), ([4, 7, 10], 1)]

def node0477Raw : WordRow := multiplyRow 4 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0477_check :
    collect (scaleRow 1 node0477Raw ++ scaleRow (-(1 : ℤ)) node0477 ++
      ([])) = [] := by
  decide +kernel

theorem node0477_mem : rowEval varIndex node0477 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0477Raw node0477 ([])
    (1) (1) (by decide) node0477_check
  · rw [node0477Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0480 : WordRow := [([6, 8, 11], 1), ([7, 8, 10], 1)]

def node0480Raw : WordRow := multiplyRow 8 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0480_check :
    collect (scaleRow 1 node0480Raw ++ scaleRow (-(1 : ℤ)) node0480 ++
      ([])) = [] := by
  decide +kernel

theorem node0480_mem : rowEval varIndex node0480 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0480Raw node0480 ([])
    (1) (1) (by decide) node0480_check
  · rw [node0480Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0481 : WordRow := [([6, 9, 11], 1), ([7, 9, 10], 1)]

def node0481Raw : WordRow := multiplyRow 9 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0481_check :
    collect (scaleRow 1 node0481Raw ++ scaleRow (-(1 : ℤ)) node0481 ++
      ([])) = [] := by
  decide +kernel

theorem node0481_mem : rowEval varIndex node0481 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0481Raw node0481 ([])
    (1) (1) (by decide) node0481_check
  · rw [node0481Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0482 : WordRow := [([6, 10, 11], 1), ([7, 10, 10], 1)]

def node0482Raw : WordRow := multiplyRow 10 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0482_check :
    collect (scaleRow 1 node0482Raw ++ scaleRow (-(1 : ℤ)) node0482 ++
      ([])) = [] := by
  decide +kernel

theorem node0482_mem : rowEval varIndex node0482 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0482Raw node0482 ([])
    (1) (1) (by decide) node0482_check
  · rw [node0482Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0484 : WordRow := [([6, 11, 12], 1), ([7, 10, 12], 1)]

def node0484Raw : WordRow := multiplyRow 12 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0484_check :
    collect (scaleRow 1 node0484Raw ++ scaleRow (-(1 : ℤ)) node0484 ++
      ([])) = [] := by
  decide +kernel

theorem node0484_mem : rowEval varIndex node0484 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0484Raw node0484 ([])
    (1) (1) (by decide) node0484_check
  · rw [node0484Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0485 : WordRow := [([6, 11, 13], 1), ([7, 10, 13], 1)]

def node0485Raw : WordRow := multiplyRow 13 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0485_check :
    collect (scaleRow 1 node0485Raw ++ scaleRow (-(1 : ℤ)) node0485 ++
      ([])) = [] := by
  decide +kernel

theorem node0485_mem : rowEval varIndex node0485 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0485Raw node0485 ([])
    (1) (1) (by decide) node0485_check
  · rw [node0485Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0486 : WordRow := [([6, 11, 14], 1), ([7, 10, 14], 1)]

def node0486Raw : WordRow := multiplyRow 14 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0486_check :
    collect (scaleRow 1 node0486Raw ++ scaleRow (-(1 : ℤ)) node0486 ++
      ([])) = [] := by
  decide +kernel

theorem node0486_mem : rowEval varIndex node0486 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0486Raw node0486 ([])
    (1) (1) (by decide) node0486_check
  · rw [node0486Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0488 : WordRow := [([6, 11, 16], 1), ([7, 10, 16], 1)]

def node0488Raw : WordRow := multiplyRow 16 node0028

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0488_check :
    collect (scaleRow 1 node0488Raw ++ scaleRow (-(1 : ℤ)) node0488 ++
      ([])) = [] := by
  decide +kernel

theorem node0488_mem : rowEval varIndex node0488 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0488Raw node0488 ([])
    (1) (1) (by decide) node0488_check
  · rw [node0488Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0028_mem
  · exact candidateIdeal.zero_mem

def node0490 : WordRow := [([7, 8, 11], 1)]

def node0490Raw : WordRow := multiplyRow 8 node0029

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0490_check :
    collect (scaleRow 1 node0490Raw ++ scaleRow (-(1 : ℤ)) node0490 ++
      ([])) = [] := by
  decide +kernel

theorem node0490_mem : rowEval varIndex node0490 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0490Raw node0490 ([])
    (1) (1) (by decide) node0490_check
  · rw [node0490Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0029_mem
  · exact candidateIdeal.zero_mem

def node0500 : WordRow := [([1, 4, 12], 2), ([4, 4, 7], -1), ([4, 5, 6], -1)]

def node0500Raw : WordRow := multiplyRow 0 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0500_check :
    collect (scaleRow 1 node0500Raw ++ scaleRow (-(-1 : ℤ)) node0500 ++
      (scaleRow (-1) node0307 ++ scaleRow (-1) node0133)) = [] := by
  decide +kernel

theorem node0500_mem : rowEval varIndex node0500 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0500Raw node0500 (scaleRow (-1) node0307 ++ scaleRow (-1) node0133)
    (1) (-1) (by decide) node0500_check
  · rw [node0500Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0307 node0307_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0133 node0133_mem))

def node0501 : WordRow := [([2, 4, 13], 1), ([2, 5, 12], 1)]

def node0501Raw : WordRow := multiplyRow 2 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0501_check :
    collect (scaleRow 1 node0501Raw ++ scaleRow (-(1 : ℤ)) node0501 ++
      ([])) = [] := by
  decide +kernel

theorem node0501_mem : rowEval varIndex node0501 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0501Raw node0501 ([])
    (1) (1) (by decide) node0501_check
  · rw [node0501Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0502 : WordRow := [([3, 4, 13], 1), ([3, 5, 12], 1)]

def node0502Raw : WordRow := multiplyRow 3 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0502_check :
    collect (scaleRow 1 node0502Raw ++ scaleRow (-(1 : ℤ)) node0502 ++
      ([])) = [] := by
  decide +kernel

theorem node0502_mem : rowEval varIndex node0502 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0502Raw node0502 ([])
    (1) (1) (by decide) node0502_check
  · rw [node0502Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0504 : WordRow := [([4, 6, 13], 1), ([5, 6, 12], 1)]

def node0504Raw : WordRow := multiplyRow 6 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0504_check :
    collect (scaleRow 1 node0504Raw ++ scaleRow (-(1 : ℤ)) node0504 ++
      ([])) = [] := by
  decide +kernel

theorem node0504_mem : rowEval varIndex node0504 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0504Raw node0504 ([])
    (1) (1) (by decide) node0504_check
  · rw [node0504Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0506 : WordRow := [([4, 8, 13], 1), ([5, 8, 12], 1)]

def node0506Raw : WordRow := multiplyRow 8 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0506_check :
    collect (scaleRow 1 node0506Raw ++ scaleRow (-(1 : ℤ)) node0506 ++
      ([])) = [] := by
  decide +kernel

theorem node0506_mem : rowEval varIndex node0506 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0506Raw node0506 ([])
    (1) (1) (by decide) node0506_check
  · rw [node0506Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0508 : WordRow := [([4, 10, 13], 1), ([5, 10, 12], 1)]

def node0508Raw : WordRow := multiplyRow 10 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0508_check :
    collect (scaleRow 1 node0508Raw ++ scaleRow (-(1 : ℤ)) node0508 ++
      ([])) = [] := by
  decide +kernel

theorem node0508_mem : rowEval varIndex node0508 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0508Raw node0508 ([])
    (1) (1) (by decide) node0508_check
  · rw [node0508Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0509 : WordRow := [([4, 11, 13], 1), ([5, 11, 12], 1)]

def node0509Raw : WordRow := multiplyRow 11 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0509_check :
    collect (scaleRow 1 node0509Raw ++ scaleRow (-(1 : ℤ)) node0509 ++
      ([])) = [] := by
  decide +kernel

theorem node0509_mem : rowEval varIndex node0509 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0509Raw node0509 ([])
    (1) (1) (by decide) node0509_check
  · rw [node0509Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0510 : WordRow := [([4, 12, 13], 1), ([5, 12, 12], 1)]

def node0510Raw : WordRow := multiplyRow 12 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0510_check :
    collect (scaleRow 1 node0510Raw ++ scaleRow (-(1 : ℤ)) node0510 ++
      ([])) = [] := by
  decide +kernel

theorem node0510_mem : rowEval varIndex node0510 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0510Raw node0510 ([])
    (1) (1) (by decide) node0510_check
  · rw [node0510Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0512 : WordRow := [([4, 13, 14], 1), ([5, 12, 14], 1)]

def node0512Raw : WordRow := multiplyRow 14 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0512_check :
    collect (scaleRow 1 node0512Raw ++ scaleRow (-(1 : ℤ)) node0512 ++
      ([])) = [] := by
  decide +kernel

theorem node0512_mem : rowEval varIndex node0512 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0512Raw node0512 ([])
    (1) (1) (by decide) node0512_check
  · rw [node0512Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0514 : WordRow := [([4, 13, 16], 1), ([5, 12, 16], 1)]

def node0514Raw : WordRow := multiplyRow 16 node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0514_check :
    collect (scaleRow 1 node0514Raw ++ scaleRow (-(1 : ℤ)) node0514 ++
      ([])) = [] := by
  decide +kernel

theorem node0514_mem : rowEval varIndex node0514 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0514Raw node0514 ([])
    (1) (1) (by decide) node0514_check
  · rw [node0514Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0516 : WordRow := [([5, 6, 13], 1)]

def node0516Raw : WordRow := multiplyRow 6 node0031

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0516_check :
    collect (scaleRow 1 node0516Raw ++ scaleRow (-(1 : ℤ)) node0516 ++
      ([])) = [] := by
  decide +kernel

theorem node0516_mem : rowEval varIndex node0516 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0516Raw node0516 ([])
    (1) (1) (by decide) node0516_check
  · rw [node0516Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0031_mem
  · exact candidateIdeal.zero_mem

def node0518 : WordRow := [([5, 10, 13], 1)]

def node0518Raw : WordRow := multiplyRow 10 node0031

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0518_check :
    collect (scaleRow 1 node0518Raw ++ scaleRow (-(1 : ℤ)) node0518 ++
      ([])) = [] := by
  decide +kernel

theorem node0518_mem : rowEval varIndex node0518 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0518Raw node0518 ([])
    (1) (1) (by decide) node0518_check
  · rw [node0518Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0031_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0518_mem
