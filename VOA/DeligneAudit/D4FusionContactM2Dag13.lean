import VOA.DeligneAudit.D4FusionContactM2Dag12

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node4478 : WordRow := [([2, 2, 6, 13], 1), ([2, 2, 7, 12], 1)]

def node4478Raw : WordRow := multiplyRow 2 node0527

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4478_check :
    collect (scaleRow 1 node4478Raw ++ scaleRow (-(1 : ℤ)) node4478 ++
      ([])) = [] := by
  decide +kernel

theorem node4478_mem : rowEval varIndex node4478 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4478Raw node4478 ([])
    (1) (1) (by decide) node4478_check
  · rw [node4478Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0527_mem
  · exact candidateIdeal.zero_mem

def node4486 : WordRow := [([2, 6, 13, 14], 1), ([2, 7, 12, 14], 1)]

def node4486Raw : WordRow := multiplyRow 14 node0527

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4486_check :
    collect (scaleRow 1 node4486Raw ++ scaleRow (-(1 : ℤ)) node4486 ++
      ([])) = [] := by
  decide +kernel

theorem node4486_mem : rowEval varIndex node4486 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4486Raw node4486 ([])
    (1) (1) (by decide) node4486_check
  · rw [node4486Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0527_mem
  · exact candidateIdeal.zero_mem

def node4488 : WordRow := [([2, 6, 13, 16], 1), ([2, 7, 12, 16], 1)]

def node4488Raw : WordRow := multiplyRow 16 node0527

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4488_check :
    collect (scaleRow 1 node4488Raw ++ scaleRow (-(1 : ℤ)) node4488 ++
      ([])) = [] := by
  decide +kernel

theorem node4488_mem : rowEval varIndex node4488 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4488Raw node4488 ([])
    (1) (1) (by decide) node4488_check
  · rw [node4488Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0527_mem
  · exact candidateIdeal.zero_mem

def node4489 : WordRow := [([2, 6, 13, 17], 1), ([2, 7, 12, 17], 1)]

def node4489Raw : WordRow := multiplyRow 17 node0527

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4489_check :
    collect (scaleRow 1 node4489Raw ++ scaleRow (-(1 : ℤ)) node4489 ++
      ([])) = [] := by
  decide +kernel

theorem node4489_mem : rowEval varIndex node4489 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4489Raw node4489 ([])
    (1) (1) (by decide) node4489_check
  · rw [node4489Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0527_mem
  · exact candidateIdeal.zero_mem

def node4506 : WordRow := [([4, 7, 12, 17], 1), ([5, 6, 12, 17], -1)]

def node4506Raw : WordRow := multiplyRow 17 node0529

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4506_check :
    collect (scaleRow 1 node4506Raw ++ scaleRow (-(1 : ℤ)) node4506 ++
      ([])) = [] := by
  decide +kernel

theorem node4506_mem : rowEval varIndex node4506 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4506Raw node4506 ([])
    (1) (1) (by decide) node4506_check
  · rw [node4506Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0529_mem
  · exact candidateIdeal.zero_mem

def node4522 : WordRow := [([6, 8, 10, 13], 1), ([7, 8, 10, 12], 1)]

def node4522Raw : WordRow := multiplyRow 10 node0532

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4522_check :
    collect (scaleRow 1 node4522Raw ++ scaleRow (-(1 : ℤ)) node4522 ++
      ([])) = [] := by
  decide +kernel

theorem node4522_mem : rowEval varIndex node4522 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4522Raw node4522 ([])
    (1) (1) (by decide) node4522_check
  · rw [node4522Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0532_mem
  · exact candidateIdeal.zero_mem

def node4523 : WordRow := [([7, 8, 10, 13], 1), ([7, 8, 11, 12], -1)]

def node4523Raw : WordRow := multiplyRow 11 node0532

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4523_check :
    collect (scaleRow 1 node4523Raw ++ scaleRow (-(-1 : ℤ)) node4523 ++
      (scaleRow (-1) node4203)) = [] := by
  decide +kernel

theorem node4523_mem : rowEval varIndex node4523 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4523Raw node4523 (scaleRow (-1) node4203)
    (1) (-1) (by decide) node4523_check
  · rw [node4523Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0532_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4203 node4203_mem)

def node4526 : WordRow := [([6, 8, 13, 14], 1), ([7, 8, 12, 14], 1)]

def node4526Raw : WordRow := multiplyRow 14 node0532

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4526_check :
    collect (scaleRow 1 node4526Raw ++ scaleRow (-(1 : ℤ)) node4526 ++
      ([])) = [] := by
  decide +kernel

theorem node4526_mem : rowEval varIndex node4526 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4526Raw node4526 ([])
    (1) (1) (by decide) node4526_check
  · rw [node4526Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0532_mem
  · exact candidateIdeal.zero_mem

def node4527 : WordRow := [([6, 8, 13, 15], 1), ([7, 8, 12, 15], 1)]

def node4527Raw : WordRow := multiplyRow 15 node0532

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4527_check :
    collect (scaleRow 1 node4527Raw ++ scaleRow (-(1 : ℤ)) node4527 ++
      ([])) = [] := by
  decide +kernel

theorem node4527_mem : rowEval varIndex node4527 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4527Raw node4527 ([])
    (1) (1) (by decide) node4527_check
  · rw [node4527Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0532_mem
  · exact candidateIdeal.zero_mem

def node4529 : WordRow := [([6, 8, 13, 17], 1), ([7, 8, 12, 17], 1)]

def node4529Raw : WordRow := multiplyRow 17 node0532

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4529_check :
    collect (scaleRow 1 node4529Raw ++ scaleRow (-(1 : ℤ)) node4529 ++
      ([])) = [] := by
  decide +kernel

theorem node4529_mem : rowEval varIndex node4529 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4529Raw node4529 ([])
    (1) (1) (by decide) node4529_check
  · rw [node4529Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0532_mem
  · exact candidateIdeal.zero_mem

def node4531 : WordRow := [([6, 9, 10, 13], 1), ([7, 9, 10, 12], 1)]

def node4531Raw : WordRow := multiplyRow 10 node0533

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4531_check :
    collect (scaleRow 1 node4531Raw ++ scaleRow (-(1 : ℤ)) node4531 ++
      ([])) = [] := by
  decide +kernel

theorem node4531_mem : rowEval varIndex node4531 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4531Raw node4531 ([])
    (1) (1) (by decide) node4531_check
  · rw [node4531Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0533_mem
  · exact candidateIdeal.zero_mem

def node4537 : WordRow := [([6, 9, 13, 16], 1), ([7, 9, 12, 16], 1)]

def node4537Raw : WordRow := multiplyRow 16 node0533

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4537_check :
    collect (scaleRow 1 node4537Raw ++ scaleRow (-(1 : ℤ)) node4537 ++
      ([])) = [] := by
  decide +kernel

theorem node4537_mem : rowEval varIndex node4537 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4537Raw node4537 ([])
    (1) (1) (by decide) node4537_check
  · rw [node4537Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0533_mem
  · exact candidateIdeal.zero_mem

def node4546 : WordRow := [([6, 10, 13, 17], 1), ([7, 10, 12, 17], 1)]

def node4546Raw : WordRow := multiplyRow 17 node0534

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4546_check :
    collect (scaleRow 1 node4546Raw ++ scaleRow (-(1 : ℤ)) node4546 ++
      ([])) = [] := by
  decide +kernel

theorem node4546_mem : rowEval varIndex node4546 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4546Raw node4546 ([])
    (1) (1) (by decide) node4546_check
  · rw [node4546Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0534_mem
  · exact candidateIdeal.zero_mem

def node4566 : WordRow := [([6, 13, 14, 16], 1), ([7, 12, 14, 16], 1)]

def node4566Raw : WordRow := multiplyRow 16 node0538

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4566_check :
    collect (scaleRow 1 node4566Raw ++ scaleRow (-(1 : ℤ)) node4566 ++
      ([])) = [] := by
  decide +kernel

theorem node4566_mem : rowEval varIndex node4566 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4566Raw node4566 ([])
    (1) (1) (by decide) node4566_check
  · rw [node4566Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0538_mem
  · exact candidateIdeal.zero_mem

def node4572 : WordRow := [([6, 13, 16, 17], 1), ([7, 12, 16, 17], 1)]

def node4572Raw : WordRow := multiplyRow 17 node0540

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4572_check :
    collect (scaleRow 1 node4572Raw ++ scaleRow (-(1 : ℤ)) node4572 ++
      ([])) = [] := by
  decide +kernel

theorem node4572_mem : rowEval varIndex node4572 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4572Raw node4572 ([])
    (1) (1) (by decide) node4572_check
  · rw [node4572Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0540_mem
  · exact candidateIdeal.zero_mem

def node4577 : WordRow := [([7, 8, 13, 14], 1)]

def node4577Raw : WordRow := multiplyRow 14 node0542

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4577_check :
    collect (scaleRow 1 node4577Raw ++ scaleRow (-(1 : ℤ)) node4577 ++
      ([])) = [] := by
  decide +kernel

theorem node4577_mem : rowEval varIndex node4577 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4577Raw node4577 ([])
    (1) (1) (by decide) node4577_check
  · rw [node4577Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0542_mem
  · exact candidateIdeal.zero_mem

def node4608 : WordRow := [([1, 6, 8, 8], 1), ([2, 5, 6, 8], -1), ([3, 4, 6, 8], -1)]

def node4608Raw : WordRow := multiplyRow 6 node0550

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4608_check :
    collect (scaleRow 1 node4608Raw ++ scaleRow (-(1 : ℤ)) node4608 ++
      ([])) = [] := by
  decide +kernel

theorem node4608_mem : rowEval varIndex node4608 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4608Raw node4608 ([])
    (1) (1) (by decide) node4608_check
  · rw [node4608Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0550_mem
  · exact candidateIdeal.zero_mem

def node4616 : WordRow := [([1, 8, 8, 16], 1), ([2, 5, 8, 16], -1), ([3, 4, 8, 16], -1)]

def node4616Raw : WordRow := multiplyRow 16 node0550

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4616_check :
    collect (scaleRow 1 node4616Raw ++ scaleRow (-(1 : ℤ)) node4616 ++
      ([])) = [] := by
  decide +kernel

theorem node4616_mem : rowEval varIndex node4616 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4616Raw node4616 ([])
    (1) (1) (by decide) node4616_check
  · rw [node4616Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0550_mem
  · exact candidateIdeal.zero_mem

def node4644 : WordRow := [([6, 8, 9, 14], 1)]

def node4644Raw : WordRow := multiplyRow 14 node0553

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4644_check :
    collect (scaleRow 1 node4644Raw ++ scaleRow (-(1 : ℤ)) node4644 ++
      ([])) = [] := by
  decide +kernel

theorem node4644_mem : rowEval varIndex node4644 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4644Raw node4644 ([])
    (1) (1) (by decide) node4644_check
  · rw [node4644Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0553_mem
  · exact candidateIdeal.zero_mem

def node4647 : WordRow := [([6, 8, 9, 17], 1)]

def node4647Raw : WordRow := multiplyRow 17 node0553

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4647_check :
    collect (scaleRow 1 node4647Raw ++ scaleRow (-(1 : ℤ)) node4647 ++
      ([])) = [] := by
  decide +kernel

theorem node4647_mem : rowEval varIndex node4647 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4647Raw node4647 ([])
    (1) (1) (by decide) node4647_check
  · rw [node4647Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0553_mem
  · exact candidateIdeal.zero_mem

def node4766 : WordRow := [([1, 2, 4, 14], 2), ([1, 4, 8, 10], 2), ([2, 2, 4, 13], -1), ([2, 3, 4, 12], -1), ([2, 4, 4, 11], -1), ([2, 4, 5, 10], -2), ([2, 4, 6, 9], -1), ([2, 4, 7, 8], -2), ([3, 4, 4, 10], -1), ([3, 4, 6, 8], -1)]

def node4766Raw : WordRow := multiplyRow 4 node0576

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4766_check :
    collect (scaleRow 1 node4766Raw ++ scaleRow (-(1 : ℤ)) node4766 ++
      ([])) = [] := by
  decide +kernel

theorem node4766_mem : rowEval varIndex node4766 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4766Raw node4766 ([])
    (1) (1) (by decide) node4766_check
  · rw [node4766Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0576_mem
  · exact candidateIdeal.zero_mem

def node4767 : WordRow := [([1, 2, 6, 14], 2), ([1, 6, 8, 10], 2), ([2, 2, 6, 13], -1), ([2, 3, 6, 12], -1), ([2, 4, 6, 11], -1), ([2, 5, 6, 10], -2), ([2, 6, 6, 9], -1), ([2, 6, 7, 8], -2), ([3, 4, 6, 10], -1), ([3, 6, 6, 8], -1)]

def node4767Raw : WordRow := multiplyRow 6 node0576

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4767_check :
    collect (scaleRow 1 node4767Raw ++ scaleRow (-(1 : ℤ)) node4767 ++
      ([])) = [] := by
  decide +kernel

theorem node4767_mem : rowEval varIndex node4767 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4767Raw node4767 ([])
    (1) (1) (by decide) node4767_check
  · rw [node4767Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0576_mem
  · exact candidateIdeal.zero_mem

def node4773 : WordRow := [([1, 2, 14, 14], 2), ([1, 8, 10, 14], 2), ([2, 2, 13, 14], -1), ([2, 3, 12, 14], -1), ([2, 4, 11, 14], -1), ([2, 5, 10, 14], -2), ([2, 6, 9, 14], -1), ([2, 7, 8, 14], -2), ([3, 4, 10, 14], -1), ([3, 6, 8, 14], -1)]

def node4773Raw : WordRow := multiplyRow 14 node0576

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4773_check :
    collect (scaleRow 1 node4773Raw ++ scaleRow (-(1 : ℤ)) node4773 ++
      ([])) = [] := by
  decide +kernel

theorem node4773_mem : rowEval varIndex node4773 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4773Raw node4773 ([])
    (1) (1) (by decide) node4773_check
  · rw [node4773Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0576_mem
  · exact candidateIdeal.zero_mem

def node4775 : WordRow := [([1, 2, 14, 16], 2), ([1, 8, 10, 16], 2), ([2, 2, 13, 16], -1), ([2, 3, 12, 16], -1), ([2, 4, 11, 16], -1), ([2, 5, 10, 16], -2), ([2, 6, 9, 16], -1), ([2, 7, 8, 16], -2), ([3, 4, 10, 16], -1), ([3, 6, 8, 16], -1)]

def node4775Raw : WordRow := multiplyRow 16 node0576

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4775_check :
    collect (scaleRow 1 node4775Raw ++ scaleRow (-(1 : ℤ)) node4775 ++
      ([])) = [] := by
  decide +kernel

theorem node4775_mem : rowEval varIndex node4775 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4775Raw node4775 ([])
    (1) (1) (by decide) node4775_check
  · rw [node4775Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0576_mem
  · exact candidateIdeal.zero_mem

def node4782 : WordRow := [([2, 2, 12, 15], 1), ([2, 3, 12, 14], 1), ([2, 8, 11, 12], 1), ([2, 9, 10, 12], 1)]

def node4782Raw : WordRow := multiplyRow 12 node0577

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4782_check :
    collect (scaleRow 1 node4782Raw ++ scaleRow (-(1 : ℤ)) node4782 ++
      ([])) = [] := by
  decide +kernel

theorem node4782_mem : rowEval varIndex node4782 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4782Raw node4782 ([])
    (1) (1) (by decide) node4782_check
  · rw [node4782Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0577_mem
  · exact candidateIdeal.zero_mem

def node4786 : WordRow := [([2, 2, 15, 16], 1), ([2, 3, 14, 16], 1), ([2, 8, 11, 16], 1), ([2, 9, 10, 16], 1)]

def node4786Raw : WordRow := multiplyRow 16 node0577

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4786_check :
    collect (scaleRow 1 node4786Raw ++ scaleRow (-(1 : ℤ)) node4786 ++
      ([])) = [] := by
  decide +kernel

theorem node4786_mem : rowEval varIndex node4786 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4786Raw node4786 ([])
    (1) (1) (by decide) node4786_check
  · rw [node4786Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0577_mem
  · exact candidateIdeal.zero_mem

def node4789 : WordRow := [([2, 4, 6, 15], 1), ([3, 4, 6, 14], 1), ([4, 6, 8, 11], 1), ([4, 6, 9, 10], 1)]

def node4789Raw : WordRow := multiplyRow 6 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4789_check :
    collect (scaleRow 1 node4789Raw ++ scaleRow (-(1 : ℤ)) node4789 ++
      ([])) = [] := by
  decide +kernel

theorem node4789_mem : rowEval varIndex node4789 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4789Raw node4789 ([])
    (1) (1) (by decide) node4789_check
  · rw [node4789Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · exact candidateIdeal.zero_mem

def node4792 : WordRow := [([2, 4, 10, 15], 1), ([3, 4, 10, 14], 1), ([4, 8, 10, 11], 1), ([4, 9, 10, 10], 1)]

def node4792Raw : WordRow := multiplyRow 10 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4792_check :
    collect (scaleRow 1 node4792Raw ++ scaleRow (-(1 : ℤ)) node4792 ++
      ([])) = [] := by
  decide +kernel

theorem node4792_mem : rowEval varIndex node4792 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4792Raw node4792 ([])
    (1) (1) (by decide) node4792_check
  · rw [node4792Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · exact candidateIdeal.zero_mem

def node4794 : WordRow := [([2, 4, 12, 15], 1), ([3, 4, 12, 14], 1), ([4, 8, 11, 12], 1), ([4, 9, 10, 12], 1)]

def node4794Raw : WordRow := multiplyRow 12 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4794_check :
    collect (scaleRow 1 node4794Raw ++ scaleRow (-(1 : ℤ)) node4794 ++
      ([])) = [] := by
  decide +kernel

theorem node4794_mem : rowEval varIndex node4794 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4794Raw node4794 ([])
    (1) (1) (by decide) node4794_check
  · rw [node4794Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · exact candidateIdeal.zero_mem

def node4795 : WordRow := [([3, 4, 12, 15], 1), ([3, 4, 13, 14], 1), ([3, 5, 12, 14], 1), ([3, 9, 12, 12], -1), ([4, 8, 11, 13], 1), ([4, 9, 10, 13], 1), ([4, 9, 11, 12], -1), ([5, 8, 11, 12], -1), ([5, 9, 10, 12], -1), ([6, 9, 9, 12], -1), ([7, 8, 9, 12], -2)]

def node4795Raw : WordRow := multiplyRow 13 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4795_check :
    collect (scaleRow 1 node4795Raw ++ scaleRow (-(1 : ℤ)) node4795 ++
      (scaleRow (-1) node4328 ++ scaleRow (1) node4027 ++ scaleRow (1) node3105 ++ scaleRow (-1) node4090 ++ scaleRow (1) node3460)) = [] := by
  decide +kernel

theorem node4795_mem : rowEval varIndex node4795 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4795Raw node4795 (scaleRow (-1) node4328 ++ scaleRow (1) node4027 ++ scaleRow (1) node3105 ++ scaleRow (-1) node4090 ++ scaleRow (1) node3460)
    (1) (1) (by decide) node4795_check
  · rw [node4795Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4328 node4328_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4027 node4027_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3105 node3105_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4090 node4090_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3460 node3460_mem)))))

def node4796 : WordRow := [([2, 4, 14, 15], 1), ([3, 4, 14, 14], 1), ([4, 8, 11, 14], 1), ([4, 9, 10, 14], 1)]

def node4796Raw : WordRow := multiplyRow 14 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4796_check :
    collect (scaleRow 1 node4796Raw ++ scaleRow (-(1 : ℤ)) node4796 ++
      ([])) = [] := by
  decide +kernel

theorem node4796_mem : rowEval varIndex node4796 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4796Raw node4796 ([])
    (1) (1) (by decide) node4796_check
  · rw [node4796Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · exact candidateIdeal.zero_mem

def node4798 : WordRow := [([2, 4, 15, 16], 1), ([3, 4, 14, 16], 1), ([4, 8, 11, 16], 1), ([4, 9, 10, 16], 1)]

def node4798Raw : WordRow := multiplyRow 16 node0578

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4798_check :
    collect (scaleRow 1 node4798Raw ++ scaleRow (-(1 : ℤ)) node4798 ++
      ([])) = [] := by
  decide +kernel

theorem node4798_mem : rowEval varIndex node4798 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4798Raw node4798 ([])
    (1) (1) (by decide) node4798_check
  · rw [node4798Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0578_mem
  · exact candidateIdeal.zero_mem

def node4807 : WordRow := [([2, 6, 8, 15], 1), ([3, 6, 8, 14], 1), ([6, 8, 8, 11], 1), ([6, 8, 9, 10], 1)]

def node4807Raw : WordRow := multiplyRow 8 node0580

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4807_check :
    collect (scaleRow 1 node4807Raw ++ scaleRow (-(1 : ℤ)) node4807 ++
      ([])) = [] := by
  decide +kernel

theorem node4807_mem : rowEval varIndex node4807 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4807Raw node4807 ([])
    (1) (1) (by decide) node4807_check
  · rw [node4807Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0580_mem
  · exact candidateIdeal.zero_mem

def node4811 : WordRow := [([2, 6, 12, 15], 1), ([3, 6, 12, 14], 1), ([6, 8, 11, 12], 1), ([6, 9, 10, 12], 1)]

def node4811Raw : WordRow := multiplyRow 12 node0580

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4811_check :
    collect (scaleRow 1 node4811Raw ++ scaleRow (-(1 : ℤ)) node4811 ++
      ([])) = [] := by
  decide +kernel

theorem node4811_mem : rowEval varIndex node4811 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4811Raw node4811 ([])
    (1) (1) (by decide) node4811_check
  · rw [node4811Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0580_mem
  · exact candidateIdeal.zero_mem

def node4813 : WordRow := [([2, 6, 14, 15], 1), ([3, 6, 14, 14], 1), ([6, 8, 11, 14], 1), ([6, 9, 10, 14], 1)]

def node4813Raw : WordRow := multiplyRow 14 node0580

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4813_check :
    collect (scaleRow 1 node4813Raw ++ scaleRow (-(1 : ℤ)) node4813 ++
      ([])) = [] := by
  decide +kernel

theorem node4813_mem : rowEval varIndex node4813 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4813Raw node4813 ([])
    (1) (1) (by decide) node4813_check
  · rw [node4813Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0580_mem
  · exact candidateIdeal.zero_mem

def node4815 : WordRow := [([2, 6, 15, 16], 1), ([3, 6, 14, 16], 1), ([6, 8, 11, 16], 1), ([6, 9, 10, 16], 1)]

def node4815Raw : WordRow := multiplyRow 16 node0580

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4815_check :
    collect (scaleRow 1 node4815Raw ++ scaleRow (-(1 : ℤ)) node4815 ++
      ([])) = [] := by
  decide +kernel

theorem node4815_mem : rowEval varIndex node4815 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4815Raw node4815 ([])
    (1) (1) (by decide) node4815_check
  · rw [node4815Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0580_mem
  · exact candidateIdeal.zero_mem

def node4824 : WordRow := [([2, 8, 12, 15], 1), ([3, 8, 12, 14], 1), ([8, 8, 11, 12], 1), ([8, 9, 10, 12], 1)]

def node4824Raw : WordRow := multiplyRow 12 node0582

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4824_check :
    collect (scaleRow 1 node4824Raw ++ scaleRow (-(1 : ℤ)) node4824 ++
      ([])) = [] := by
  decide +kernel

theorem node4824_mem : rowEval varIndex node4824 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4824Raw node4824 ([])
    (1) (1) (by decide) node4824_check
  · rw [node4824Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0582_mem
  · exact candidateIdeal.zero_mem

def node4828 : WordRow := [([2, 8, 15, 16], 1), ([3, 8, 14, 16], 1), ([8, 8, 11, 16], 1), ([8, 9, 10, 16], 1)]

def node4828Raw : WordRow := multiplyRow 16 node0582

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4828_check :
    collect (scaleRow 1 node4828Raw ++ scaleRow (-(1 : ℤ)) node4828 ++
      ([])) = [] := by
  decide +kernel

theorem node4828_mem : rowEval varIndex node4828 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4828Raw node4828 ([])
    (1) (1) (by decide) node4828_check
  · rw [node4828Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0582_mem
  · exact candidateIdeal.zero_mem

def node4839 : WordRow := [([2, 10, 12, 15], 1), ([3, 10, 12, 14], 1), ([8, 10, 11, 12], 1), ([9, 10, 10, 12], 1)]

def node4839Raw : WordRow := multiplyRow 12 node0584

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4839_check :
    collect (scaleRow 1 node4839Raw ++ scaleRow (-(1 : ℤ)) node4839 ++
      ([])) = [] := by
  decide +kernel

theorem node4839_mem : rowEval varIndex node4839 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4839Raw node4839 ([])
    (1) (1) (by decide) node4839_check
  · rw [node4839Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0584_mem
  · exact candidateIdeal.zero_mem

def node4843 : WordRow := [([2, 10, 15, 16], 1), ([3, 10, 14, 16], 1), ([8, 10, 11, 16], 1), ([9, 10, 10, 16], 1)]

def node4843Raw : WordRow := multiplyRow 16 node0584

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4843_check :
    collect (scaleRow 1 node4843Raw ++ scaleRow (-(1 : ℤ)) node4843 ++
      ([])) = [] := by
  decide +kernel

theorem node4843_mem : rowEval varIndex node4843 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4843Raw node4843 ([])
    (1) (1) (by decide) node4843_check
  · rw [node4843Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0584_mem
  · exact candidateIdeal.zero_mem

def node4852 : WordRow := [([2, 12, 12, 15], 1), ([3, 12, 12, 14], 1), ([8, 11, 12, 12], 1), ([9, 10, 12, 12], 1)]

def node4852Raw : WordRow := multiplyRow 12 node0586

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4852_check :
    collect (scaleRow 1 node4852Raw ++ scaleRow (-(1 : ℤ)) node4852 ++
      ([])) = [] := by
  decide +kernel

theorem node4852_mem : rowEval varIndex node4852 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4852Raw node4852 ([])
    (1) (1) (by decide) node4852_check
  · rw [node4852Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0586_mem
  · exact candidateIdeal.zero_mem

def node4853 : WordRow := [([2, 12, 13, 15], 1), ([3, 12, 13, 14], 1), ([8, 11, 12, 13], 1), ([9, 10, 12, 13], 1)]

def node4853Raw : WordRow := multiplyRow 13 node0586

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4853_check :
    collect (scaleRow 1 node4853Raw ++ scaleRow (-(1 : ℤ)) node4853 ++
      ([])) = [] := by
  decide +kernel

theorem node4853_mem : rowEval varIndex node4853 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4853Raw node4853 ([])
    (1) (1) (by decide) node4853_check
  · rw [node4853Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0586_mem
  · exact candidateIdeal.zero_mem

def node4854 : WordRow := [([2, 12, 14, 15], 1), ([3, 12, 14, 14], 1), ([8, 11, 12, 14], 1), ([9, 10, 12, 14], 1)]

def node4854Raw : WordRow := multiplyRow 14 node0586

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4854_check :
    collect (scaleRow 1 node4854Raw ++ scaleRow (-(1 : ℤ)) node4854 ++
      ([])) = [] := by
  decide +kernel

theorem node4854_mem : rowEval varIndex node4854 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4854Raw node4854 ([])
    (1) (1) (by decide) node4854_check
  · rw [node4854Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0586_mem
  · exact candidateIdeal.zero_mem

def node4856 : WordRow := [([2, 12, 15, 16], 1), ([3, 12, 14, 16], 1), ([8, 11, 12, 16], 1), ([9, 10, 12, 16], 1)]

def node4856Raw : WordRow := multiplyRow 16 node0586

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4856_check :
    collect (scaleRow 1 node4856Raw ++ scaleRow (-(1 : ℤ)) node4856 ++
      ([])) = [] := by
  decide +kernel

theorem node4856_mem : rowEval varIndex node4856 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4856Raw node4856 ([])
    (1) (1) (by decide) node4856_check
  · rw [node4856Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0586_mem
  · exact candidateIdeal.zero_mem

def node4865 : WordRow := [([2, 14, 15, 16], 1), ([3, 14, 14, 16], 1), ([8, 11, 14, 16], 1), ([9, 10, 14, 16], 1)]

def node4865Raw : WordRow := multiplyRow 16 node0588

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4865_check :
    collect (scaleRow 1 node4865Raw ++ scaleRow (-(1 : ℤ)) node4865 ++
      ([])) = [] := by
  decide +kernel

theorem node4865_mem : rowEval varIndex node4865 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4865Raw node4865 ([])
    (1) (1) (by decide) node4865_check
  · rw [node4865Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0588_mem
  · exact candidateIdeal.zero_mem

def node4871 : WordRow := [([2, 15, 16, 17], 1), ([3, 14, 16, 17], 1), ([8, 11, 16, 17], 1), ([9, 10, 16, 17], 1)]

def node4871Raw : WordRow := multiplyRow 17 node0590

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4871_check :
    collect (scaleRow 1 node4871Raw ++ scaleRow (-(1 : ℤ)) node4871 ++
      ([])) = [] := by
  decide +kernel

theorem node4871_mem : rowEval varIndex node4871 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4871Raw node4871 ([])
    (1) (1) (by decide) node4871_check
  · rw [node4871Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0590_mem
  · exact candidateIdeal.zero_mem

def node4921 : WordRow := [([1, 4, 10, 10], 1), ([2, 4, 7, 10], -1), ([3, 4, 6, 10], -1)]

def node4921Raw : WordRow := multiplyRow 4 node0602

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4921_check :
    collect (scaleRow 1 node4921Raw ++ scaleRow (-(1 : ℤ)) node4921 ++
      ([])) = [] := by
  decide +kernel

theorem node4921_mem : rowEval varIndex node4921 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4921Raw node4921 ([])
    (1) (1) (by decide) node4921_check
  · rw [node4921Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0602_mem
  · exact candidateIdeal.zero_mem

def node4927 : WordRow := [([1, 10, 10, 16], 1), ([2, 7, 10, 16], -1), ([3, 6, 10, 16], -1)]

def node4927Raw : WordRow := multiplyRow 16 node0602

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4927_check :
    collect (scaleRow 1 node4927Raw ++ scaleRow (-(1 : ℤ)) node4927 ++
      ([])) = [] := by
  decide +kernel

theorem node4927_mem : rowEval varIndex node4927 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4927Raw node4927 ([])
    (1) (1) (by decide) node4927_check
  · rw [node4927Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0602_mem
  · exact candidateIdeal.zero_mem

def node4943 : WordRow := [([4, 10, 11, 12], 1)]

def node4943Raw : WordRow := multiplyRow 12 node0604

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4943_check :
    collect (scaleRow 1 node4943Raw ++ scaleRow (-(1 : ℤ)) node4943 ++
      ([])) = [] := by
  decide +kernel

theorem node4943_mem : rowEval varIndex node4943 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4943Raw node4943 ([])
    (1) (1) (by decide) node4943_check
  · rw [node4943Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0604_mem
  · exact candidateIdeal.zero_mem

def node4945 : WordRow := [([4, 10, 11, 14], 1)]

def node4945Raw : WordRow := multiplyRow 14 node0604

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4945_check :
    collect (scaleRow 1 node4945Raw ++ scaleRow (-(1 : ℤ)) node4945 ++
      ([])) = [] := by
  decide +kernel

theorem node4945_mem : rowEval varIndex node4945 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4945Raw node4945 ([])
    (1) (1) (by decide) node4945_check
  · rw [node4945Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0604_mem
  · exact candidateIdeal.zero_mem

def node4947 : WordRow := [([4, 10, 11, 16], 1)]

def node4947Raw : WordRow := multiplyRow 16 node0604

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4947_check :
    collect (scaleRow 1 node4947Raw ++ scaleRow (-(1 : ℤ)) node4947 ++
      ([])) = [] := by
  decide +kernel

theorem node4947_mem : rowEval varIndex node4947 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4947Raw node4947 ([])
    (1) (1) (by decide) node4947_check
  · rw [node4947Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0604_mem
  · exact candidateIdeal.zero_mem

def node4948 : WordRow := [([4, 10, 11, 17], 1)]

def node4948Raw : WordRow := multiplyRow 17 node0604

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4948_check :
    collect (scaleRow 1 node4948Raw ++ scaleRow (-(1 : ℤ)) node4948 ++
      ([])) = [] := by
  decide +kernel

theorem node4948_mem : rowEval varIndex node4948 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4948Raw node4948 ([])
    (1) (1) (by decide) node4948_check
  · rw [node4948Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0604_mem
  · exact candidateIdeal.zero_mem

def node4963 : WordRow := [([8, 10, 11, 13], 1)]

def node4963Raw : WordRow := multiplyRow 13 node0607

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4963_check :
    collect (scaleRow 1 node4963Raw ++ scaleRow (-(1 : ℤ)) node4963 ++
      ([])) = [] := by
  decide +kernel

theorem node4963_mem : rowEval varIndex node4963 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4963Raw node4963 ([])
    (1) (1) (by decide) node4963_check
  · rw [node4963Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0607_mem
  · exact candidateIdeal.zero_mem

def node4967 : WordRow := [([8, 10, 11, 17], 1)]

def node4967Raw : WordRow := multiplyRow 17 node0607

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node4967_check :
    collect (scaleRow 1 node4967Raw ++ scaleRow (-(1 : ℤ)) node4967 ++
      ([])) = [] := by
  decide +kernel

theorem node4967_mem : rowEval varIndex node4967 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node4967Raw node4967 ([])
    (1) (1) (by decide) node4967_check
  · rw [node4967Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0607_mem
  · exact candidateIdeal.zero_mem

def node5039 : WordRow := [([1, 4, 6, 14], 2), ([1, 6, 8, 12], 2), ([2, 4, 6, 13], -1), ([2, 5, 6, 12], -1), ([3, 4, 6, 12], -2), ([4, 4, 6, 11], -1), ([4, 5, 6, 10], -1), ([4, 6, 6, 9], -1), ([4, 6, 7, 8], -2), ([5, 6, 6, 8], -1)]

def node5039Raw : WordRow := multiplyRow 6 node0624

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5039_check :
    collect (scaleRow 1 node5039Raw ++ scaleRow (-(1 : ℤ)) node5039 ++
      ([])) = [] := by
  decide +kernel

theorem node5039_mem : rowEval varIndex node5039 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5039Raw node5039 ([])
    (1) (1) (by decide) node5039_check
  · rw [node5039Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0624_mem
  · exact candidateIdeal.zero_mem

def node5042 : WordRow := [([3, 4, 7, 14], 2), ([3, 4, 10, 13], 1), ([3, 4, 11, 12], -1), ([3, 5, 10, 12], 1), ([3, 6, 9, 12], -1), ([3, 7, 8, 12], 2), ([4, 4, 11, 11], -1), ([4, 5, 10, 11], -1), ([4, 6, 9, 11], -1), ([4, 7, 8, 11], -2), ([5, 6, 8, 11], -1)]

def node5042Raw : WordRow := multiplyRow 11 node0624

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5042_check :
    collect (scaleRow 1 node5042Raw ++ scaleRow (-(1 : ℤ)) node5042 ++
      (scaleRow (-2) node2544 ++ scaleRow (-2) node1707 ++ scaleRow (-2) node2584 ++ scaleRow (-2) node2450 ++ scaleRow (1) node3608 ++ scaleRow (2) node2414 ++ scaleRow (-1) node2653 ++ scaleRow (1) node3419)) = [] := by
  decide +kernel

theorem node5042_mem : rowEval varIndex node5042 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5042Raw node5042 (scaleRow (-2) node2544 ++ scaleRow (-2) node1707 ++ scaleRow (-2) node2584 ++ scaleRow (-2) node2450 ++ scaleRow (1) node3608 ++ scaleRow (2) node2414 ++ scaleRow (-1) node2653 ++ scaleRow (1) node3419)
    (1) (1) (by decide) node5042_check
  · rw [node5042Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0624_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2544 node2544_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1707 node1707_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2584 node2584_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2450 node2450_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3608 node3608_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2414 node2414_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2653 node2653_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3419 node3419_mem))))))))

def node5045 : WordRow := [([1, 4, 14, 14], 2), ([1, 8, 12, 14], 2), ([2, 4, 13, 14], -1), ([2, 5, 12, 14], -1), ([3, 4, 12, 14], -2), ([4, 4, 11, 14], -1), ([4, 5, 10, 14], -1), ([4, 6, 9, 14], -1), ([4, 7, 8, 14], -2), ([5, 6, 8, 14], -1)]

def node5045Raw : WordRow := multiplyRow 14 node0624

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5045_check :
    collect (scaleRow 1 node5045Raw ++ scaleRow (-(1 : ℤ)) node5045 ++
      ([])) = [] := by
  decide +kernel

theorem node5045_mem : rowEval varIndex node5045 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5045Raw node5045 ([])
    (1) (1) (by decide) node5045_check
  · rw [node5045Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0624_mem
  · exact candidateIdeal.zero_mem

def node5046 : WordRow := [([3, 5, 12, 14], 2), ([3, 8, 12, 13], -2), ([3, 9, 12, 12], 2), ([4, 4, 11, 15], 1), ([4, 5, 10, 15], 1), ([4, 5, 11, 14], 2), ([4, 6, 9, 15], 1), ([4, 7, 8, 15], 2), ([4, 7, 9, 14], 2), ([4, 8, 11, 13], -2), ([4, 9, 10, 13], -2), ([4, 9, 11, 12], 2), ([5, 5, 10, 14], 2), ([5, 6, 8, 15], 1), ([5, 6, 9, 14], 4), ([5, 7, 8, 14], 4), ([5, 9, 10, 12], 2), ([6, 9, 9, 12], 2), ([7, 8, 9, 12], 2)]

def node5046Raw : WordRow := multiplyRow 15 node0624

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5046_check :
    collect (scaleRow 1 node5046Raw ++ scaleRow (-(-1 : ℤ)) node5046 ++
      (scaleRow (-2) node3990 ++ scaleRow (-2) node1729 ++ scaleRow (-2) node4019 ++ scaleRow (-2) node3036 ++ scaleRow (-2) node2465 ++ scaleRow (1) node4328 ++ scaleRow (2) node4090 ++ scaleRow (2) node4795 ++ scaleRow (-4) node4333)) = [] := by
  decide +kernel

theorem node5046_mem : rowEval varIndex node5046 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5046Raw node5046 (scaleRow (-2) node3990 ++ scaleRow (-2) node1729 ++ scaleRow (-2) node4019 ++ scaleRow (-2) node3036 ++ scaleRow (-2) node2465 ++ scaleRow (1) node4328 ++ scaleRow (2) node4090 ++ scaleRow (2) node4795 ++ scaleRow (-4) node4333)
    (1) (-1) (by decide) node5046_check
  · rw [node5046Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0624_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3990 node3990_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1729 node1729_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4019 node4019_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3036 node3036_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2465 node2465_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4328 node4328_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4090 node4090_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4795 node4795_mem) (rowEval_scale_mem varIndex candidateIdeal (-4) node4333 node4333_mem)))))))))

def node5047 : WordRow := [([1, 4, 14, 16], 2), ([1, 8, 12, 16], 2), ([2, 4, 13, 16], -1), ([2, 5, 12, 16], -1), ([3, 4, 12, 16], -2), ([4, 4, 11, 16], -1), ([4, 5, 10, 16], -1), ([4, 6, 9, 16], -1), ([4, 7, 8, 16], -2), ([5, 6, 8, 16], -1)]

def node5047Raw : WordRow := multiplyRow 16 node0624

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5047_check :
    collect (scaleRow 1 node5047Raw ++ scaleRow (-(1 : ℤ)) node5047 ++
      ([])) = [] := by
  decide +kernel

theorem node5047_mem : rowEval varIndex node5047 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5047Raw node5047 ([])
    (1) (1) (by decide) node5047_check
  · rw [node5047Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0624_mem
  · exact candidateIdeal.zero_mem

def node5051 : WordRow := [([2, 5, 6, 14], 1), ([2, 6, 8, 13], 1), ([2, 6, 9, 12], 1), ([3, 4, 6, 14], -1), ([4, 6, 8, 11], -1), ([4, 6, 9, 10], -1)]

def node5051Raw : WordRow := multiplyRow 6 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5051_check :
    collect (scaleRow 1 node5051Raw ++ scaleRow (-(1 : ℤ)) node5051 ++
      ([])) = [] := by
  decide +kernel

theorem node5051_mem : rowEval varIndex node5051 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5051Raw node5051 ([])
    (1) (1) (by decide) node5051_check
  · rw [node5051Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · exact candidateIdeal.zero_mem

def node5052 : WordRow := [([3, 5, 6, 14], 1), ([3, 6, 8, 13], 1), ([3, 6, 9, 12], 2), ([4, 4, 11, 11], 1), ([4, 5, 10, 11], 1), ([4, 6, 9, 11], 1), ([4, 7, 8, 11], 2), ([4, 7, 9, 10], 1), ([5, 7, 8, 10], -1)]

def node5052Raw : WordRow := multiplyRow 7 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5052_check :
    collect (scaleRow 1 node5052Raw ++ scaleRow (-(-1 : ℤ)) node5052 ++
      (scaleRow (-1) node2414 ++ scaleRow (-1) node3101 ++ scaleRow (-1) node3419 ++ scaleRow (1) node5042 ++ scaleRow (-1) node4324 ++ scaleRow (2) node3615)) = [] := by
  decide +kernel

theorem node5052_mem : rowEval varIndex node5052 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5052Raw node5052 (scaleRow (-1) node2414 ++ scaleRow (-1) node3101 ++ scaleRow (-1) node3419 ++ scaleRow (1) node5042 ++ scaleRow (-1) node4324 ++ scaleRow (2) node3615)
    (1) (-1) (by decide) node5052_check
  · rw [node5052Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2414 node2414_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3101 node3101_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3419 node3419_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node5042 node5042_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4324 node4324_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node3615 node3615_mem))))))

def node5055 : WordRow := [([3, 5, 10, 14], 1), ([3, 6, 9, 14], 1), ([3, 8, 10, 13], 1), ([3, 8, 11, 12], 1), ([4, 8, 11, 11], 1), ([4, 9, 10, 11], 1)]

def node5055Raw : WordRow := multiplyRow 11 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5055_check :
    collect (scaleRow 1 node5055Raw ++ scaleRow (-(-1 : ℤ)) node5055 ++
      (scaleRow (-1) node2655 ++ scaleRow (-1) node3421 ++ scaleRow (-1) node3647 ++ scaleRow (-1) node3453 ++ scaleRow (2) node3617)) = [] := by
  decide +kernel

theorem node5055_mem : rowEval varIndex node5055 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5055Raw node5055 (scaleRow (-1) node2655 ++ scaleRow (-1) node3421 ++ scaleRow (-1) node3647 ++ scaleRow (-1) node3453 ++ scaleRow (2) node3617)
    (1) (-1) (by decide) node5055_check
  · rw [node5055Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2655 node2655_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3421 node3421_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3647 node3647_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3453 node3453_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node3617 node3617_mem)))))

def node5056 : WordRow := [([2, 5, 12, 14], 1), ([2, 8, 12, 13], 1), ([2, 9, 12, 12], 1), ([3, 4, 12, 14], -1), ([4, 8, 11, 12], -1), ([4, 9, 10, 12], -1)]

def node5056Raw : WordRow := multiplyRow 12 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5056_check :
    collect (scaleRow 1 node5056Raw ++ scaleRow (-(1 : ℤ)) node5056 ++
      ([])) = [] := by
  decide +kernel

theorem node5056_mem : rowEval varIndex node5056 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5056Raw node5056 ([])
    (1) (1) (by decide) node5056_check
  · rw [node5056Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · exact candidateIdeal.zero_mem

def node5057 : WordRow := [([3, 8, 12, 13], 4), ([3, 9, 12, 12], 2), ([4, 4, 11, 15], 1), ([4, 5, 10, 15], 1), ([4, 5, 11, 14], 2), ([4, 6, 9, 15], 1), ([4, 8, 11, 13], 2), ([4, 9, 11, 12], 2), ([5, 5, 10, 14], 2), ([5, 6, 8, 15], -1), ([5, 6, 9, 14], 2), ([5, 8, 10, 13], 2), ([5, 8, 11, 12], 2), ([5, 9, 10, 12], 2), ([6, 8, 9, 13], 2), ([6, 9, 9, 12], 2), ([7, 8, 8, 13], 2), ([7, 8, 9, 12], 4)]

def node5057Raw : WordRow := multiplyRow 13 node0625

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5057_check :
    collect (scaleRow 2 node5057Raw ++ scaleRow (-(-1 : ℤ)) node5057 ++
      (scaleRow (-2) node3105 ++ scaleRow (-2) node4090 ++ scaleRow (-2) node3460 ++ scaleRow (4) node4333 ++ scaleRow (-1) node5046)) = [] := by
  decide +kernel

theorem node5057_mem : rowEval varIndex node5057 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5057Raw node5057 (scaleRow (-2) node3105 ++ scaleRow (-2) node4090 ++ scaleRow (-2) node3460 ++ scaleRow (4) node4333 ++ scaleRow (-1) node5046)
    (2) (-1) (by decide) node5057_check
  · rw [node5057Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0625_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3105 node3105_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4090 node4090_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3460 node3460_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (4) node4333 node4333_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5046 node5046_mem)))))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node5057_mem
