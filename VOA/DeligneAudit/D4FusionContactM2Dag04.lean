import VOA.DeligneAudit.D4FusionContactM2Dag03

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0526 : WordRow := [([1, 6, 12], 2), ([4, 6, 7], -1), ([5, 6, 6], -1)]

def node0526Raw : WordRow := multiplyRow 0 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0526_check :
    collect (scaleRow 1 node0526Raw ++ scaleRow (-(-1 : ℤ)) node0526 ++
      (scaleRow (-1) node0309 ++ scaleRow (-1) node0164)) = [] := by
  decide +kernel

theorem node0526_mem : rowEval varIndex node0526 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0526Raw node0526 (scaleRow (-1) node0309 ++ scaleRow (-1) node0164)
    (1) (-1) (by decide) node0526_check
  · rw [node0526Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0309 node0309_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0164 node0164_mem))

def node0527 : WordRow := [([2, 6, 13], 1), ([2, 7, 12], 1)]

def node0527Raw : WordRow := multiplyRow 2 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0527_check :
    collect (scaleRow 1 node0527Raw ++ scaleRow (-(1 : ℤ)) node0527 ++
      ([])) = [] := by
  decide +kernel

theorem node0527_mem : rowEval varIndex node0527 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0527Raw node0527 ([])
    (1) (1) (by decide) node0527_check
  · rw [node0527Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0529 : WordRow := [([4, 7, 12], 1), ([5, 6, 12], -1)]

def node0529Raw : WordRow := multiplyRow 4 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0529_check :
    collect (scaleRow 1 node0529Raw ++ scaleRow (-(1 : ℤ)) node0529 ++
      (scaleRow (-1) node0504)) = [] := by
  decide +kernel

theorem node0529_mem : rowEval varIndex node0529 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0529Raw node0529 (scaleRow (-1) node0504)
    (1) (1) (by decide) node0529_check
  · rw [node0529Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0504 node0504_mem)

def node0530 : WordRow := [([5, 7, 12], 1)]

def node0530Raw : WordRow := multiplyRow 5 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0530_check :
    collect (scaleRow 1 node0530Raw ++ scaleRow (-(1 : ℤ)) node0530 ++
      (scaleRow (-1) node0516)) = [] := by
  decide +kernel

theorem node0530_mem : rowEval varIndex node0530 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0530Raw node0530 (scaleRow (-1) node0516)
    (1) (1) (by decide) node0530_check
  · rw [node0530Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0516 node0516_mem)

def node0532 : WordRow := [([6, 8, 13], 1), ([7, 8, 12], 1)]

def node0532Raw : WordRow := multiplyRow 8 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0532_check :
    collect (scaleRow 1 node0532Raw ++ scaleRow (-(1 : ℤ)) node0532 ++
      ([])) = [] := by
  decide +kernel

theorem node0532_mem : rowEval varIndex node0532 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0532Raw node0532 ([])
    (1) (1) (by decide) node0532_check
  · rw [node0532Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0533 : WordRow := [([6, 9, 13], 1), ([7, 9, 12], 1)]

def node0533Raw : WordRow := multiplyRow 9 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0533_check :
    collect (scaleRow 1 node0533Raw ++ scaleRow (-(1 : ℤ)) node0533 ++
      ([])) = [] := by
  decide +kernel

theorem node0533_mem : rowEval varIndex node0533 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0533Raw node0533 ([])
    (1) (1) (by decide) node0533_check
  · rw [node0533Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0534 : WordRow := [([6, 10, 13], 1), ([7, 10, 12], 1)]

def node0534Raw : WordRow := multiplyRow 10 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0534_check :
    collect (scaleRow 1 node0534Raw ++ scaleRow (-(1 : ℤ)) node0534 ++
      ([])) = [] := by
  decide +kernel

theorem node0534_mem : rowEval varIndex node0534 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0534Raw node0534 ([])
    (1) (1) (by decide) node0534_check
  · rw [node0534Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0536 : WordRow := [([6, 12, 13], 1), ([7, 12, 12], 1)]

def node0536Raw : WordRow := multiplyRow 12 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0536_check :
    collect (scaleRow 1 node0536Raw ++ scaleRow (-(1 : ℤ)) node0536 ++
      ([])) = [] := by
  decide +kernel

theorem node0536_mem : rowEval varIndex node0536 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0536Raw node0536 ([])
    (1) (1) (by decide) node0536_check
  · rw [node0536Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0538 : WordRow := [([6, 13, 14], 1), ([7, 12, 14], 1)]

def node0538Raw : WordRow := multiplyRow 14 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0538_check :
    collect (scaleRow 1 node0538Raw ++ scaleRow (-(1 : ℤ)) node0538 ++
      ([])) = [] := by
  decide +kernel

theorem node0538_mem : rowEval varIndex node0538 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0538Raw node0538 ([])
    (1) (1) (by decide) node0538_check
  · rw [node0538Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0540 : WordRow := [([6, 13, 16], 1), ([7, 12, 16], 1)]

def node0540Raw : WordRow := multiplyRow 16 node0032

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0540_check :
    collect (scaleRow 1 node0540Raw ++ scaleRow (-(1 : ℤ)) node0540 ++
      ([])) = [] := by
  decide +kernel

theorem node0540_mem : rowEval varIndex node0540 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0540Raw node0540 ([])
    (1) (1) (by decide) node0540_check
  · rw [node0540Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0032_mem
  · exact candidateIdeal.zero_mem

def node0542 : WordRow := [([7, 8, 13], 1)]

def node0542Raw : WordRow := multiplyRow 8 node0033

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0542_check :
    collect (scaleRow 1 node0542Raw ++ scaleRow (-(1 : ℤ)) node0542 ++
      ([])) = [] := by
  decide +kernel

theorem node0542_mem : rowEval varIndex node0542 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0542Raw node0542 ([])
    (1) (1) (by decide) node0542_check
  · rw [node0542Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0033_mem
  · exact candidateIdeal.zero_mem

def node0550 : WordRow := [([1, 8, 8], 1), ([2, 5, 8], -1), ([3, 4, 8], -1)]

def node0550Raw : WordRow := multiplyRow 0 node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0550_check :
    collect (scaleRow 1 node0550Raw ++ scaleRow (-(-1 : ℤ)) node0550 ++
      (scaleRow (-1) node0221)) = [] := by
  decide +kernel

theorem node0550_mem : rowEval varIndex node0550 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0550Raw node0550 (scaleRow (-1) node0221)
    (1) (-1) (by decide) node0550_check
  · rw [node0550Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0034_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0221 node0221_mem)

def node0551 : WordRow := [([3, 8, 8], 1)]

def node0551Raw : WordRow := multiplyRow 2 node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0551_check :
    collect (scaleRow 1 node0551Raw ++ scaleRow (-(-1 : ℤ)) node0551 ++
      (scaleRow (-1) node0367)) = [] := by
  decide +kernel

theorem node0551_mem : rowEval varIndex node0551 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0551Raw node0551 (scaleRow (-1) node0367)
    (1) (-1) (by decide) node0551_check
  · rw [node0551Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0034_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0367 node0367_mem)

def node0552 : WordRow := [([5, 8, 8], 1)]

def node0552Raw : WordRow := multiplyRow 4 node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0552_check :
    collect (scaleRow 1 node0552Raw ++ scaleRow (-(-1 : ℤ)) node0552 ++
      (scaleRow (-1) node0423)) = [] := by
  decide +kernel

theorem node0552_mem : rowEval varIndex node0552 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0552Raw node0552 (scaleRow (-1) node0423)
    (1) (-1) (by decide) node0552_check
  · rw [node0552Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0034_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0423 node0423_mem)

def node0553 : WordRow := [([6, 8, 9], 1)]

def node0553Raw : WordRow := multiplyRow 6 node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0553_check :
    collect (scaleRow 1 node0553Raw ++ scaleRow (-(1 : ℤ)) node0553 ++
      ([])) = [] := by
  decide +kernel

theorem node0553_mem : rowEval varIndex node0553 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0553Raw node0553 ([])
    (1) (1) (by decide) node0553_check
  · rw [node0553Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0034_mem
  · exact candidateIdeal.zero_mem

def node0576 : WordRow := [([1, 2, 14], 2), ([1, 8, 10], 2), ([2, 2, 13], -1), ([2, 3, 12], -1), ([2, 4, 11], -1), ([2, 5, 10], -2), ([2, 6, 9], -1), ([2, 7, 8], -2), ([3, 4, 10], -1), ([3, 6, 8], -1)]

def node0576Raw : WordRow := multiplyRow 0 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0576_check :
    collect (scaleRow 1 node0576Raw ++ scaleRow (-(-1 : ℤ)) node0576 ++
      (scaleRow (-1) node0446 ++ scaleRow (-1) node0102 ++ scaleRow (-1) node0252 ++ scaleRow (-1) node0223)) = [] := by
  decide +kernel

theorem node0576_mem : rowEval varIndex node0576 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0576Raw node0576 (scaleRow (-1) node0446 ++ scaleRow (-1) node0102 ++ scaleRow (-1) node0252 ++ scaleRow (-1) node0223)
    (1) (-1) (by decide) node0576_check
  · rw [node0576Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0446 node0446_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0102 node0102_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0252 node0252_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0223 node0223_mem))))

def node0577 : WordRow := [([2, 2, 15], 1), ([2, 3, 14], 1), ([2, 8, 11], 1), ([2, 9, 10], 1)]

def node0577Raw : WordRow := multiplyRow 2 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0577_check :
    collect (scaleRow 1 node0577Raw ++ scaleRow (-(1 : ℤ)) node0577 ++
      ([])) = [] := by
  decide +kernel

theorem node0577_mem : rowEval varIndex node0577 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0577Raw node0577 ([])
    (1) (1) (by decide) node0577_check
  · rw [node0577Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0578 : WordRow := [([2, 4, 15], 1), ([3, 4, 14], 1), ([4, 8, 11], 1), ([4, 9, 10], 1)]

def node0578Raw : WordRow := multiplyRow 4 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0578_check :
    collect (scaleRow 1 node0578Raw ++ scaleRow (-(1 : ℤ)) node0578 ++
      ([])) = [] := by
  decide +kernel

theorem node0578_mem : rowEval varIndex node0578 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0578Raw node0578 ([])
    (1) (1) (by decide) node0578_check
  · rw [node0578Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0579 : WordRow := [([3, 4, 15], 1), ([3, 9, 12], -1), ([4, 9, 11], -1), ([5, 8, 11], -2), ([5, 9, 10], -2), ([6, 9, 9], -1), ([7, 8, 9], -2)]

def node0579Raw : WordRow := multiplyRow 5 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0579_check :
    collect (scaleRow 1 node0579Raw ++ scaleRow (-(-1 : ℤ)) node0579 ++
      (scaleRow (-1) node0464 ++ scaleRow (-1) node0372)) = [] := by
  decide +kernel

theorem node0579_mem : rowEval varIndex node0579 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0579Raw node0579 (scaleRow (-1) node0464 ++ scaleRow (-1) node0372)
    (1) (-1) (by decide) node0579_check
  · rw [node0579Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0464 node0464_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0372 node0372_mem))

def node0580 : WordRow := [([2, 6, 15], 1), ([3, 6, 14], 1), ([6, 8, 11], 1), ([6, 9, 10], 1)]

def node0580Raw : WordRow := multiplyRow 6 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0580_check :
    collect (scaleRow 1 node0580Raw ++ scaleRow (-(1 : ℤ)) node0580 ++
      ([])) = [] := by
  decide +kernel

theorem node0580_mem : rowEval varIndex node0580 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0580Raw node0580 ([])
    (1) (1) (by decide) node0580_check
  · rw [node0580Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0581 : WordRow := [([3, 6, 15], 1), ([3, 11, 12], -1), ([4, 11, 11], -1), ([5, 10, 11], -2), ([6, 9, 11], -1), ([7, 8, 11], -2), ([7, 9, 10], -2)]

def node0581Raw : WordRow := multiplyRow 7 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0581_check :
    collect (scaleRow 1 node0581Raw ++ scaleRow (-(-1 : ℤ)) node0581 ++
      (scaleRow (-1) node0466 ++ scaleRow (-1) node0402)) = [] := by
  decide +kernel

theorem node0581_mem : rowEval varIndex node0581 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0581Raw node0581 (scaleRow (-1) node0466 ++ scaleRow (-1) node0402)
    (1) (-1) (by decide) node0581_check
  · rw [node0581Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0466 node0466_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0402 node0402_mem))

def node0582 : WordRow := [([2, 8, 15], 1), ([3, 8, 14], 1), ([8, 8, 11], 1), ([8, 9, 10], 1)]

def node0582Raw : WordRow := multiplyRow 8 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0582_check :
    collect (scaleRow 1 node0582Raw ++ scaleRow (-(1 : ℤ)) node0582 ++
      ([])) = [] := by
  decide +kernel

theorem node0582_mem : rowEval varIndex node0582 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0582Raw node0582 ([])
    (1) (1) (by decide) node0582_check
  · rw [node0582Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0584 : WordRow := [([2, 10, 15], 1), ([3, 10, 14], 1), ([8, 10, 11], 1), ([9, 10, 10], 1)]

def node0584Raw : WordRow := multiplyRow 10 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0584_check :
    collect (scaleRow 1 node0584Raw ++ scaleRow (-(1 : ℤ)) node0584 ++
      ([])) = [] := by
  decide +kernel

theorem node0584_mem : rowEval varIndex node0584 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0584Raw node0584 ([])
    (1) (1) (by decide) node0584_check
  · rw [node0584Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0586 : WordRow := [([2, 12, 15], 1), ([3, 12, 14], 1), ([8, 11, 12], 1), ([9, 10, 12], 1)]

def node0586Raw : WordRow := multiplyRow 12 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0586_check :
    collect (scaleRow 1 node0586Raw ++ scaleRow (-(1 : ℤ)) node0586 ++
      ([])) = [] := by
  decide +kernel

theorem node0586_mem : rowEval varIndex node0586 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0586Raw node0586 ([])
    (1) (1) (by decide) node0586_check
  · rw [node0586Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0588 : WordRow := [([2, 14, 15], 1), ([3, 14, 14], 1), ([8, 11, 14], 1), ([9, 10, 14], 1)]

def node0588Raw : WordRow := multiplyRow 14 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0588_check :
    collect (scaleRow 1 node0588Raw ++ scaleRow (-(1 : ℤ)) node0588 ++
      ([])) = [] := by
  decide +kernel

theorem node0588_mem : rowEval varIndex node0588 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0588Raw node0588 ([])
    (1) (1) (by decide) node0588_check
  · rw [node0588Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0590 : WordRow := [([2, 15, 16], 1), ([3, 14, 16], 1), ([8, 11, 16], 1), ([9, 10, 16], 1)]

def node0590Raw : WordRow := multiplyRow 16 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0590_check :
    collect (scaleRow 1 node0590Raw ++ scaleRow (-(1 : ℤ)) node0590 ++
      ([])) = [] := by
  decide +kernel

theorem node0590_mem : rowEval varIndex node0590 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0590Raw node0590 ([])
    (1) (1) (by decide) node0590_check
  · rw [node0590Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0591 : WordRow := [([2, 15, 17], 1), ([3, 14, 17], 1), ([8, 11, 17], 1), ([9, 10, 17], 1)]

def node0591Raw : WordRow := multiplyRow 17 node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0591_check :
    collect (scaleRow 1 node0591Raw ++ scaleRow (-(1 : ℤ)) node0591 ++
      ([])) = [] := by
  decide +kernel

theorem node0591_mem : rowEval varIndex node0591 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0591Raw node0591 ([])
    (1) (1) (by decide) node0591_check
  · rw [node0591Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0596 : WordRow := [([3, 12, 15], 1), ([9, 11, 12], 1)]

def node0596Raw : WordRow := multiplyRow 12 node0037

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0596_check :
    collect (scaleRow 1 node0596Raw ++ scaleRow (-(1 : ℤ)) node0596 ++
      ([])) = [] := by
  decide +kernel

theorem node0596_mem : rowEval varIndex node0596 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0596Raw node0596 ([])
    (1) (1) (by decide) node0596_check
  · rw [node0596Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0037_mem
  · exact candidateIdeal.zero_mem

def node0600 : WordRow := [([3, 15, 16], 1), ([9, 11, 16], 1)]

def node0600Raw : WordRow := multiplyRow 16 node0037

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0600_check :
    collect (scaleRow 1 node0600Raw ++ scaleRow (-(1 : ℤ)) node0600 ++
      ([])) = [] := by
  decide +kernel

theorem node0600_mem : rowEval varIndex node0600 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0600Raw node0600 ([])
    (1) (1) (by decide) node0600_check
  · rw [node0600Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0037_mem
  · exact candidateIdeal.zero_mem

def node0601 : WordRow := [([3, 15, 17], 1), ([9, 11, 17], 1)]

def node0601Raw : WordRow := multiplyRow 17 node0037

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0601_check :
    collect (scaleRow 1 node0601Raw ++ scaleRow (-(1 : ℤ)) node0601 ++
      ([])) = [] := by
  decide +kernel

theorem node0601_mem : rowEval varIndex node0601 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0601Raw node0601 ([])
    (1) (1) (by decide) node0601_check
  · rw [node0601Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0037_mem
  · exact candidateIdeal.zero_mem

def node0602 : WordRow := [([1, 10, 10], 1), ([2, 7, 10], -1), ([3, 6, 10], -1)]

def node0602Raw : WordRow := multiplyRow 0 node0038

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0602_check :
    collect (scaleRow 1 node0602Raw ++ scaleRow (-(-1 : ℤ)) node0602 ++
      (scaleRow (-1) node0254)) = [] := by
  decide +kernel

theorem node0602_mem : rowEval varIndex node0602 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0602Raw node0602 (scaleRow (-1) node0254)
    (1) (-1) (by decide) node0602_check
  · rw [node0602Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0038_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0254 node0254_mem)

def node0603 : WordRow := [([3, 10, 10], 1)]

def node0603Raw : WordRow := multiplyRow 2 node0038

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0603_check :
    collect (scaleRow 1 node0603Raw ++ scaleRow (-(-1 : ℤ)) node0603 ++
      (scaleRow (-1) node0399)) = [] := by
  decide +kernel

theorem node0603_mem : rowEval varIndex node0603 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0603Raw node0603 (scaleRow (-1) node0399)
    (1) (-1) (by decide) node0603_check
  · rw [node0603Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0038_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0399 node0399_mem)

def node0604 : WordRow := [([4, 10, 11], 1)]

def node0604Raw : WordRow := multiplyRow 4 node0038

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0604_check :
    collect (scaleRow 1 node0604Raw ++ scaleRow (-(1 : ℤ)) node0604 ++
      ([])) = [] := by
  decide +kernel

theorem node0604_mem : rowEval varIndex node0604 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0604Raw node0604 ([])
    (1) (1) (by decide) node0604_check
  · rw [node0604Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0038_mem
  · exact candidateIdeal.zero_mem

def node0606 : WordRow := [([7, 10, 10], 1)]

def node0606Raw : WordRow := multiplyRow 6 node0038

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0606_check :
    collect (scaleRow 1 node0606Raw ++ scaleRow (-(-1 : ℤ)) node0606 ++
      (scaleRow (-1) node0482)) = [] := by
  decide +kernel

theorem node0606_mem : rowEval varIndex node0606 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0606Raw node0606 (scaleRow (-1) node0482)
    (1) (-1) (by decide) node0606_check
  · rw [node0606Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0038_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0482 node0482_mem)

def node0607 : WordRow := [([8, 10, 11], 1)]

def node0607Raw : WordRow := multiplyRow 8 node0038

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0607_check :
    collect (scaleRow 1 node0607Raw ++ scaleRow (-(1 : ℤ)) node0607 ++
      ([])) = [] := by
  decide +kernel

theorem node0607_mem : rowEval varIndex node0607 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0607Raw node0607 ([])
    (1) (1) (by decide) node0607_check
  · rw [node0607Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0038_mem
  · exact candidateIdeal.zero_mem

def node0624 : WordRow := [([1, 4, 14], 2), ([1, 8, 12], 2), ([2, 4, 13], -1), ([2, 5, 12], -1), ([3, 4, 12], -2), ([4, 4, 11], -1), ([4, 5, 10], -1), ([4, 6, 9], -1), ([4, 7, 8], -2), ([5, 6, 8], -1)]

def node0624Raw : WordRow := multiplyRow 0 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0624_check :
    collect (scaleRow 1 node0624Raw ++ scaleRow (-(-1 : ℤ)) node0624 ++
      (scaleRow (-1) node0448 ++ scaleRow (-1) node0135 ++ scaleRow (-1) node0311 ++ scaleRow (-1) node0225)) = [] := by
  decide +kernel

theorem node0624_mem : rowEval varIndex node0624 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0624Raw node0624 (scaleRow (-1) node0448 ++ scaleRow (-1) node0135 ++ scaleRow (-1) node0311 ++ scaleRow (-1) node0225)
    (1) (-1) (by decide) node0624_check
  · rw [node0624Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0448 node0448_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0135 node0135_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0311 node0311_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0225 node0225_mem))))

def node0625 : WordRow := [([2, 5, 14], 1), ([2, 8, 13], 1), ([2, 9, 12], 1), ([3, 4, 14], -1), ([4, 8, 11], -1), ([4, 9, 10], -1)]

def node0625Raw : WordRow := multiplyRow 2 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0625_check :
    collect (scaleRow 1 node0625Raw ++ scaleRow (-(1 : ℤ)) node0625 ++
      (scaleRow (-1) node0578)) = [] := by
  decide +kernel

theorem node0625_mem : rowEval varIndex node0625 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0625Raw node0625 (scaleRow (-1) node0578)
    (1) (1) (by decide) node0625_check
  · rw [node0625Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0578 node0578_mem)

def node0626 : WordRow := [([3, 5, 14], 1), ([3, 8, 13], 1), ([3, 9, 12], 2), ([4, 9, 11], 1), ([5, 8, 11], 2), ([5, 9, 10], 2), ([6, 9, 9], 1), ([7, 8, 9], 2)]

def node0626Raw : WordRow := multiplyRow 3 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0626_check :
    collect (scaleRow 1 node0626Raw ++ scaleRow (-(1 : ℤ)) node0626 ++
      (scaleRow (-1) node0579)) = [] := by
  decide +kernel

theorem node0626_mem : rowEval varIndex node0626 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0626Raw node0626 (scaleRow (-1) node0579)
    (1) (1) (by decide) node0626_check
  · rw [node0626Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0579 node0579_mem)

def node0627 : WordRow := [([4, 4, 15], 1), ([4, 5, 14], 1), ([4, 8, 13], 1), ([4, 9, 12], 1)]

def node0627Raw : WordRow := multiplyRow 4 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0627_check :
    collect (scaleRow 1 node0627Raw ++ scaleRow (-(1 : ℤ)) node0627 ++
      ([])) = [] := by
  decide +kernel

theorem node0627_mem : rowEval varIndex node0627 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0627Raw node0627 ([])
    (1) (1) (by decide) node0627_check
  · rw [node0627Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0628 : WordRow := [([4, 6, 15], 1), ([5, 6, 14], 1), ([6, 8, 13], 1), ([6, 9, 12], 1)]

def node0628Raw : WordRow := multiplyRow 6 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0628_check :
    collect (scaleRow 1 node0628Raw ++ scaleRow (-(1 : ℤ)) node0628 ++
      ([])) = [] := by
  decide +kernel

theorem node0628_mem : rowEval varIndex node0628 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0628Raw node0628 ([])
    (1) (1) (by decide) node0628_check
  · rw [node0628Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0630 : WordRow := [([4, 8, 15], 1), ([5, 8, 14], 1), ([8, 8, 13], 1), ([8, 9, 12], 1)]

def node0630Raw : WordRow := multiplyRow 8 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0630_check :
    collect (scaleRow 1 node0630Raw ++ scaleRow (-(1 : ℤ)) node0630 ++
      ([])) = [] := by
  decide +kernel

theorem node0630_mem : rowEval varIndex node0630 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0630Raw node0630 ([])
    (1) (1) (by decide) node0630_check
  · rw [node0630Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0632 : WordRow := [([4, 10, 15], 1), ([5, 10, 14], 1), ([8, 10, 13], 1), ([9, 10, 12], 1)]

def node0632Raw : WordRow := multiplyRow 10 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0632_check :
    collect (scaleRow 1 node0632Raw ++ scaleRow (-(1 : ℤ)) node0632 ++
      ([])) = [] := by
  decide +kernel

theorem node0632_mem : rowEval varIndex node0632 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0632Raw node0632 ([])
    (1) (1) (by decide) node0632_check
  · rw [node0632Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0634 : WordRow := [([4, 12, 15], 1), ([5, 12, 14], 1), ([8, 12, 13], 1), ([9, 12, 12], 1)]

def node0634Raw : WordRow := multiplyRow 12 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0634_check :
    collect (scaleRow 1 node0634Raw ++ scaleRow (-(1 : ℤ)) node0634 ++
      ([])) = [] := by
  decide +kernel

theorem node0634_mem : rowEval varIndex node0634 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0634Raw node0634 ([])
    (1) (1) (by decide) node0634_check
  · rw [node0634Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0636 : WordRow := [([4, 14, 15], 1), ([5, 14, 14], 1), ([8, 13, 14], 1), ([9, 12, 14], 1)]

def node0636Raw : WordRow := multiplyRow 14 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0636_check :
    collect (scaleRow 1 node0636Raw ++ scaleRow (-(1 : ℤ)) node0636 ++
      ([])) = [] := by
  decide +kernel

theorem node0636_mem : rowEval varIndex node0636 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0636Raw node0636 ([])
    (1) (1) (by decide) node0636_check
  · rw [node0636Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0638 : WordRow := [([4, 15, 16], 1), ([5, 14, 16], 1), ([8, 13, 16], 1), ([9, 12, 16], 1)]

def node0638Raw : WordRow := multiplyRow 16 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0638_check :
    collect (scaleRow 1 node0638Raw ++ scaleRow (-(1 : ℤ)) node0638 ++
      ([])) = [] := by
  decide +kernel

theorem node0638_mem : rowEval varIndex node0638 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0638Raw node0638 ([])
    (1) (1) (by decide) node0638_check
  · rw [node0638Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0639 : WordRow := [([4, 15, 17], 1), ([5, 14, 17], 1), ([8, 13, 17], 1), ([9, 12, 17], 1)]

def node0639Raw : WordRow := multiplyRow 17 node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0639_check :
    collect (scaleRow 1 node0639Raw ++ scaleRow (-(1 : ℤ)) node0639 ++
      ([])) = [] := by
  decide +kernel

theorem node0639_mem : rowEval varIndex node0639 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0639Raw node0639 ([])
    (1) (1) (by decide) node0639_check
  · rw [node0639Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0640 : WordRow := [([5, 6, 15], 1), ([6, 9, 13], 1)]

def node0640Raw : WordRow := multiplyRow 6 node0041

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0640_check :
    collect (scaleRow 1 node0640Raw ++ scaleRow (-(1 : ℤ)) node0640 ++
      ([])) = [] := by
  decide +kernel

theorem node0640_mem : rowEval varIndex node0640 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0640Raw node0640 ([])
    (1) (1) (by decide) node0640_check
  · rw [node0640Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0041_mem
  · exact candidateIdeal.zero_mem

def node0642 : WordRow := [([5, 10, 15], 1), ([9, 10, 13], 1)]

def node0642Raw : WordRow := multiplyRow 10 node0041

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0642_check :
    collect (scaleRow 1 node0642Raw ++ scaleRow (-(1 : ℤ)) node0642 ++
      ([])) = [] := by
  decide +kernel

theorem node0642_mem : rowEval varIndex node0642 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0642Raw node0642 ([])
    (1) (1) (by decide) node0642_check
  · rw [node0642Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0041_mem
  · exact candidateIdeal.zero_mem

def node0648 : WordRow := [([5, 15, 16], 1), ([9, 13, 16], 1)]

def node0648Raw : WordRow := multiplyRow 16 node0041

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0648_check :
    collect (scaleRow 1 node0648Raw ++ scaleRow (-(1 : ℤ)) node0648 ++
      ([])) = [] := by
  decide +kernel

theorem node0648_mem : rowEval varIndex node0648 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0648Raw node0648 ([])
    (1) (1) (by decide) node0648_check
  · rw [node0648Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0041_mem
  · exact candidateIdeal.zero_mem

def node0649 : WordRow := [([5, 15, 17], 1), ([9, 13, 17], 1)]

def node0649Raw : WordRow := multiplyRow 17 node0041

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0649_check :
    collect (scaleRow 1 node0649Raw ++ scaleRow (-(1 : ℤ)) node0649 ++
      ([])) = [] := by
  decide +kernel

theorem node0649_mem : rowEval varIndex node0649 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0649Raw node0649 ([])
    (1) (1) (by decide) node0649_check
  · rw [node0649Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0041_mem
  · exact candidateIdeal.zero_mem

def node0650 : WordRow := [([1, 6, 14], 2), ([1, 10, 12], 2), ([2, 6, 13], -1), ([2, 7, 12], -1), ([3, 6, 12], -2), ([4, 6, 11], -1), ([4, 7, 10], -1), ([5, 6, 10], -2), ([6, 6, 9], -1), ([6, 7, 8], -1)]

def node0650Raw : WordRow := multiplyRow 0 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0650_check :
    collect (scaleRow 1 node0650Raw ++ scaleRow (-(-1 : ℤ)) node0650 ++
      (scaleRow (-1) node0450 ++ scaleRow (-1) node0166 ++ scaleRow (-1) node0313 ++ scaleRow (-1) node0256)) = [] := by
  decide +kernel

theorem node0650_mem : rowEval varIndex node0650 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0650Raw node0650 (scaleRow (-1) node0450 ++ scaleRow (-1) node0166 ++ scaleRow (-1) node0313 ++ scaleRow (-1) node0256)
    (1) (-1) (by decide) node0650_check
  · rw [node0650Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0450 node0450_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0166 node0166_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0313 node0313_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0256 node0256_mem))))

def node0651 : WordRow := [([2, 7, 14], 1), ([2, 10, 13], 1), ([2, 11, 12], 1), ([3, 6, 14], -1), ([6, 8, 11], -1), ([6, 9, 10], -1)]

def node0651Raw : WordRow := multiplyRow 2 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0651_check :
    collect (scaleRow 1 node0651Raw ++ scaleRow (-(1 : ℤ)) node0651 ++
      (scaleRow (-1) node0580)) = [] := by
  decide +kernel

theorem node0651_mem : rowEval varIndex node0651 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0651Raw node0651 (scaleRow (-1) node0580)
    (1) (1) (by decide) node0651_check
  · rw [node0651Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0580 node0580_mem)

def node0652 : WordRow := [([3, 7, 14], 1), ([3, 10, 13], 1), ([3, 11, 12], 2), ([4, 11, 11], 1), ([5, 10, 11], 2), ([6, 9, 11], 1), ([7, 8, 11], 2), ([7, 9, 10], 2)]

def node0652Raw : WordRow := multiplyRow 3 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0652_check :
    collect (scaleRow 1 node0652Raw ++ scaleRow (-(1 : ℤ)) node0652 ++
      (scaleRow (-1) node0581)) = [] := by
  decide +kernel

theorem node0652_mem : rowEval varIndex node0652 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0652Raw node0652 (scaleRow (-1) node0581)
    (1) (1) (by decide) node0652_check
  · rw [node0652Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0581 node0581_mem)

def node0653 : WordRow := [([4, 7, 14], 1), ([4, 10, 13], 1), ([4, 11, 12], 1), ([5, 6, 14], -1), ([6, 8, 13], -1), ([6, 9, 12], -1)]

def node0653Raw : WordRow := multiplyRow 4 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0653_check :
    collect (scaleRow 1 node0653Raw ++ scaleRow (-(1 : ℤ)) node0653 ++
      (scaleRow (-1) node0628)) = [] := by
  decide +kernel

theorem node0653_mem : rowEval varIndex node0653 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0653Raw node0653 (scaleRow (-1) node0628)
    (1) (1) (by decide) node0653_check
  · rw [node0653Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0628 node0628_mem)

def node0654 : WordRow := [([5, 7, 14], 1), ([5, 10, 13], 1), ([5, 11, 12], 1), ([6, 9, 13], -1)]

def node0654Raw : WordRow := multiplyRow 5 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0654_check :
    collect (scaleRow 1 node0654Raw ++ scaleRow (-(1 : ℤ)) node0654 ++
      (scaleRow (-1) node0640)) = [] := by
  decide +kernel

theorem node0654_mem : rowEval varIndex node0654 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0654Raw node0654 (scaleRow (-1) node0640)
    (1) (1) (by decide) node0654_check
  · rw [node0654Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0640 node0640_mem)

def node0655 : WordRow := [([6, 6, 15], 1), ([6, 7, 14], 1), ([6, 10, 13], 1), ([6, 11, 12], 1)]

def node0655Raw : WordRow := multiplyRow 6 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0655_check :
    collect (scaleRow 1 node0655Raw ++ scaleRow (-(1 : ℤ)) node0655 ++
      ([])) = [] := by
  decide +kernel

theorem node0655_mem : rowEval varIndex node0655 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0655Raw node0655 ([])
    (1) (1) (by decide) node0655_check
  · rw [node0655Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0656 : WordRow := [([6, 8, 15], 1), ([7, 8, 14], 1), ([8, 10, 13], 1), ([8, 11, 12], 1)]

def node0656Raw : WordRow := multiplyRow 8 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0656_check :
    collect (scaleRow 1 node0656Raw ++ scaleRow (-(1 : ℤ)) node0656 ++
      ([])) = [] := by
  decide +kernel

theorem node0656_mem : rowEval varIndex node0656 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0656Raw node0656 ([])
    (1) (1) (by decide) node0656_check
  · rw [node0656Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0657 : WordRow := [([6, 9, 15], 1), ([7, 9, 14], 1), ([9, 10, 13], 1), ([9, 11, 12], 1)]

def node0657Raw : WordRow := multiplyRow 9 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0657_check :
    collect (scaleRow 1 node0657Raw ++ scaleRow (-(1 : ℤ)) node0657 ++
      ([])) = [] := by
  decide +kernel

theorem node0657_mem : rowEval varIndex node0657 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0657Raw node0657 ([])
    (1) (1) (by decide) node0657_check
  · rw [node0657Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0658 : WordRow := [([6, 10, 15], 1), ([7, 10, 14], 1), ([10, 10, 13], 1), ([10, 11, 12], 1)]

def node0658Raw : WordRow := multiplyRow 10 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0658_check :
    collect (scaleRow 1 node0658Raw ++ scaleRow (-(1 : ℤ)) node0658 ++
      ([])) = [] := by
  decide +kernel

theorem node0658_mem : rowEval varIndex node0658 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0658Raw node0658 ([])
    (1) (1) (by decide) node0658_check
  · rw [node0658Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0660 : WordRow := [([6, 12, 15], 1), ([7, 12, 14], 1), ([10, 12, 13], 1), ([11, 12, 12], 1)]

def node0660Raw : WordRow := multiplyRow 12 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0660_check :
    collect (scaleRow 1 node0660Raw ++ scaleRow (-(1 : ℤ)) node0660 ++
      ([])) = [] := by
  decide +kernel

theorem node0660_mem : rowEval varIndex node0660 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0660Raw node0660 ([])
    (1) (1) (by decide) node0660_check
  · rw [node0660Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0662 : WordRow := [([6, 14, 15], 1), ([7, 14, 14], 1), ([10, 13, 14], 1), ([11, 12, 14], 1)]

def node0662Raw : WordRow := multiplyRow 14 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0662_check :
    collect (scaleRow 1 node0662Raw ++ scaleRow (-(1 : ℤ)) node0662 ++
      ([])) = [] := by
  decide +kernel

theorem node0662_mem : rowEval varIndex node0662 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0662Raw node0662 ([])
    (1) (1) (by decide) node0662_check
  · rw [node0662Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0664 : WordRow := [([6, 15, 16], 1), ([7, 14, 16], 1), ([10, 13, 16], 1), ([11, 12, 16], 1)]

def node0664Raw : WordRow := multiplyRow 16 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0664_check :
    collect (scaleRow 1 node0664Raw ++ scaleRow (-(1 : ℤ)) node0664 ++
      ([])) = [] := by
  decide +kernel

theorem node0664_mem : rowEval varIndex node0664 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0664Raw node0664 ([])
    (1) (1) (by decide) node0664_check
  · rw [node0664Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0665 : WordRow := [([6, 15, 17], 1), ([7, 14, 17], 1), ([10, 13, 17], 1), ([11, 12, 17], 1)]

def node0665Raw : WordRow := multiplyRow 17 node0042

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0665_check :
    collect (scaleRow 1 node0665Raw ++ scaleRow (-(1 : ℤ)) node0665 ++
      ([])) = [] := by
  decide +kernel

theorem node0665_mem : rowEval varIndex node0665 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0665Raw node0665 ([])
    (1) (1) (by decide) node0665_check
  · rw [node0665Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0042_mem
  · exact candidateIdeal.zero_mem

def node0666 : WordRow := [([7, 8, 15], 1), ([8, 11, 13], 1)]

def node0666Raw : WordRow := multiplyRow 8 node0043

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0666_check :
    collect (scaleRow 1 node0666Raw ++ scaleRow (-(1 : ℤ)) node0666 ++
      ([])) = [] := by
  decide +kernel

theorem node0666_mem : rowEval varIndex node0666 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0666Raw node0666 ([])
    (1) (1) (by decide) node0666_check
  · rw [node0666Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0043_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0666_mem
