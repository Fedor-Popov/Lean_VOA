import VOA.DeligneAudit.D4FusionContactM2Dag10

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node3509 : WordRow := [([3, 6, 9, 14], 1)]

def node3509Raw : WordRow := multiplyRow 14 node0379

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3509_check :
    collect (scaleRow 1 node3509Raw ++ scaleRow (-(1 : ℤ)) node3509 ++
      ([])) = [] := by
  decide +kernel

theorem node3509_mem : rowEval varIndex node3509 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3509Raw node3509 ([])
    (1) (1) (by decide) node3509_check
  · rw [node3509Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0379_mem
  · exact candidateIdeal.zero_mem

def node3555 : WordRow := [([3, 9, 12, 12], 1)]

def node3555Raw : WordRow := multiplyRow 12 node0385

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3555_check :
    collect (scaleRow 1 node3555Raw ++ scaleRow (-(1 : ℤ)) node3555 ++
      ([])) = [] := by
  decide +kernel

theorem node3555_mem : rowEval varIndex node3555 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3555Raw node3555 ([])
    (1) (1) (by decide) node3555_check
  · rw [node3555Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0385_mem
  · exact candidateIdeal.zero_mem

def node3577 : WordRow := [([1, 2, 4, 10], 2), ([2, 2, 4, 7], -1), ([2, 3, 4, 6], -1)]

def node3577Raw : WordRow := multiplyRow 4 node0391

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3577_check :
    collect (scaleRow 1 node3577Raw ++ scaleRow (-(1 : ℤ)) node3577 ++
      ([])) = [] := by
  decide +kernel

theorem node3577_mem : rowEval varIndex node3577 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3577Raw node3577 ([])
    (1) (1) (by decide) node3577_check
  · rw [node3577Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0391_mem
  · exact candidateIdeal.zero_mem

def node3582 : WordRow := [([1, 2, 10, 12], 2), ([2, 2, 7, 12], -1), ([2, 3, 6, 12], -1)]

def node3582Raw : WordRow := multiplyRow 12 node0391

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3582_check :
    collect (scaleRow 1 node3582Raw ++ scaleRow (-(1 : ℤ)) node3582 ++
      ([])) = [] := by
  decide +kernel

theorem node3582_mem : rowEval varIndex node3582 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3582Raw node3582 ([])
    (1) (1) (by decide) node3582_check
  · rw [node3582Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0391_mem
  · exact candidateIdeal.zero_mem

def node3586 : WordRow := [([1, 2, 10, 16], 2), ([2, 2, 7, 16], -1), ([2, 3, 6, 16], -1)]

def node3586Raw : WordRow := multiplyRow 16 node0391

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3586_check :
    collect (scaleRow 1 node3586Raw ++ scaleRow (-(1 : ℤ)) node3586 ++
      ([])) = [] := by
  decide +kernel

theorem node3586_mem : rowEval varIndex node3586 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3586Raw node3586 ([])
    (1) (1) (by decide) node3586_check
  · rw [node3586Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0391_mem
  · exact candidateIdeal.zero_mem

def node3600 : WordRow := [([2, 4, 4, 11], 1), ([3, 4, 4, 10], 1)]

def node3600Raw : WordRow := multiplyRow 4 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3600_check :
    collect (scaleRow 1 node3600Raw ++ scaleRow (-(1 : ℤ)) node3600 ++
      ([])) = [] := by
  decide +kernel

theorem node3600_mem : rowEval varIndex node3600 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3600Raw node3600 ([])
    (1) (1) (by decide) node3600_check
  · rw [node3600Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3601 : WordRow := [([2, 4, 6, 11], 1), ([3, 4, 6, 10], 1)]

def node3601Raw : WordRow := multiplyRow 6 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3601_check :
    collect (scaleRow 1 node3601Raw ++ scaleRow (-(1 : ℤ)) node3601 ++
      ([])) = [] := by
  decide +kernel

theorem node3601_mem : rowEval varIndex node3601 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3601Raw node3601 ([])
    (1) (1) (by decide) node3601_check
  · rw [node3601Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3607 : WordRow := [([2, 4, 11, 12], 1), ([3, 4, 10, 12], 1)]

def node3607Raw : WordRow := multiplyRow 12 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3607_check :
    collect (scaleRow 1 node3607Raw ++ scaleRow (-(1 : ℤ)) node3607 ++
      ([])) = [] := by
  decide +kernel

theorem node3607_mem : rowEval varIndex node3607 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3607Raw node3607 ([])
    (1) (1) (by decide) node3607_check
  · rw [node3607Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3608 : WordRow := [([2, 4, 11, 13], 1), ([3, 4, 10, 13], 1)]

def node3608Raw : WordRow := multiplyRow 13 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3608_check :
    collect (scaleRow 1 node3608Raw ++ scaleRow (-(1 : ℤ)) node3608 ++
      ([])) = [] := by
  decide +kernel

theorem node3608_mem : rowEval varIndex node3608 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3608Raw node3608 ([])
    (1) (1) (by decide) node3608_check
  · rw [node3608Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3609 : WordRow := [([2, 4, 11, 14], 1), ([3, 4, 10, 14], 1)]

def node3609Raw : WordRow := multiplyRow 14 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3609_check :
    collect (scaleRow 1 node3609Raw ++ scaleRow (-(1 : ℤ)) node3609 ++
      ([])) = [] := by
  decide +kernel

theorem node3609_mem : rowEval varIndex node3609 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3609Raw node3609 ([])
    (1) (1) (by decide) node3609_check
  · rw [node3609Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3611 : WordRow := [([2, 4, 11, 16], 1), ([3, 4, 10, 16], 1)]

def node3611Raw : WordRow := multiplyRow 16 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3611_check :
    collect (scaleRow 1 node3611Raw ++ scaleRow (-(1 : ℤ)) node3611 ++
      ([])) = [] := by
  decide +kernel

theorem node3611_mem : rowEval varIndex node3611 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3611Raw node3611 ([])
    (1) (1) (by decide) node3611_check
  · rw [node3611Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3612 : WordRow := [([2, 4, 11, 17], 1), ([3, 4, 10, 17], 1)]

def node3612Raw : WordRow := multiplyRow 17 node0393

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3612_check :
    collect (scaleRow 1 node3612Raw ++ scaleRow (-(1 : ℤ)) node3612 ++
      ([])) = [] := by
  decide +kernel

theorem node3612_mem : rowEval varIndex node3612 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3612Raw node3612 ([])
    (1) (1) (by decide) node3612_check
  · rw [node3612Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0393_mem
  · exact candidateIdeal.zero_mem

def node3615 : WordRow := [([3, 4, 11, 12], 1), ([3, 6, 9, 12], -1)]

def node3615Raw : WordRow := multiplyRow 12 node0394

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3615_check :
    collect (scaleRow 1 node3615Raw ++ scaleRow (-(1 : ℤ)) node3615 ++
      ([])) = [] := by
  decide +kernel

theorem node3615_mem : rowEval varIndex node3615 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3615Raw node3615 ([])
    (1) (1) (by decide) node3615_check
  · rw [node3615Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0394_mem
  · exact candidateIdeal.zero_mem

def node3617 : WordRow := [([3, 4, 11, 14], 1), ([3, 6, 9, 14], -1)]

def node3617Raw : WordRow := multiplyRow 14 node0394

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3617_check :
    collect (scaleRow 1 node3617Raw ++ scaleRow (-(1 : ℤ)) node3617 ++
      ([])) = [] := by
  decide +kernel

theorem node3617_mem : rowEval varIndex node3617 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3617Raw node3617 ([])
    (1) (1) (by decide) node3617_check
  · rw [node3617Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0394_mem
  · exact candidateIdeal.zero_mem

def node3647 : WordRow := [([2, 8, 11, 13], 1), ([3, 8, 10, 13], 1)]

def node3647Raw : WordRow := multiplyRow 13 node0397

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3647_check :
    collect (scaleRow 1 node3647Raw ++ scaleRow (-(1 : ℤ)) node3647 ++
      ([])) = [] := by
  decide +kernel

theorem node3647_mem : rowEval varIndex node3647 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3647Raw node3647 ([])
    (1) (1) (by decide) node3647_check
  · rw [node3647Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0397_mem
  · exact candidateIdeal.zero_mem

def node3651 : WordRow := [([2, 8, 11, 17], 1), ([3, 8, 10, 17], 1)]

def node3651Raw : WordRow := multiplyRow 17 node0397

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3651_check :
    collect (scaleRow 1 node3651Raw ++ scaleRow (-(1 : ℤ)) node3651 ++
      ([])) = [] := by
  decide +kernel

theorem node3651_mem : rowEval varIndex node3651 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3651Raw node3651 ([])
    (1) (1) (by decide) node3651_check
  · rw [node3651Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0397_mem
  · exact candidateIdeal.zero_mem

def node3675 : WordRow := [([2, 11, 12, 12], 1), ([3, 10, 12, 12], 1)]

def node3675Raw : WordRow := multiplyRow 12 node0401

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3675_check :
    collect (scaleRow 1 node3675Raw ++ scaleRow (-(1 : ℤ)) node3675 ++
      ([])) = [] := by
  decide +kernel

theorem node3675_mem : rowEval varIndex node3675 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3675Raw node3675 ([])
    (1) (1) (by decide) node3675_check
  · rw [node3675Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0401_mem
  · exact candidateIdeal.zero_mem

def node3677 : WordRow := [([2, 11, 12, 14], 1), ([3, 10, 12, 14], 1)]

def node3677Raw : WordRow := multiplyRow 14 node0401

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3677_check :
    collect (scaleRow 1 node3677Raw ++ scaleRow (-(1 : ℤ)) node3677 ++
      ([])) = [] := by
  decide +kernel

theorem node3677_mem : rowEval varIndex node3677 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3677Raw node3677 ([])
    (1) (1) (by decide) node3677_check
  · rw [node3677Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0401_mem
  · exact candidateIdeal.zero_mem

def node3679 : WordRow := [([2, 11, 12, 16], 1), ([3, 10, 12, 16], 1)]

def node3679Raw : WordRow := multiplyRow 16 node0401

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3679_check :
    collect (scaleRow 1 node3679Raw ++ scaleRow (-(1 : ℤ)) node3679 ++
      ([])) = [] := by
  decide +kernel

theorem node3679_mem : rowEval varIndex node3679 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3679Raw node3679 ([])
    (1) (1) (by decide) node3679_check
  · rw [node3679Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0401_mem
  · exact candidateIdeal.zero_mem

def node3680 : WordRow := [([2, 11, 12, 17], 1), ([3, 10, 12, 17], 1)]

def node3680Raw : WordRow := multiplyRow 17 node0401

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3680_check :
    collect (scaleRow 1 node3680Raw ++ scaleRow (-(1 : ℤ)) node3680 ++
      ([])) = [] := by
  decide +kernel

theorem node3680_mem : rowEval varIndex node3680 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3680Raw node3680 ([])
    (1) (1) (by decide) node3680_check
  · rw [node3680Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0401_mem
  · exact candidateIdeal.zero_mem

def node3684 : WordRow := [([2, 11, 13, 16], 1), ([3, 10, 13, 16], 1)]

def node3684Raw : WordRow := multiplyRow 16 node0402

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3684_check :
    collect (scaleRow 1 node3684Raw ++ scaleRow (-(1 : ℤ)) node3684 ++
      ([])) = [] := by
  decide +kernel

theorem node3684_mem : rowEval varIndex node3684 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3684Raw node3684 ([])
    (1) (1) (by decide) node3684_check
  · rw [node3684Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0402_mem
  · exact candidateIdeal.zero_mem

def node3688 : WordRow := [([2, 11, 14, 16], 1), ([3, 10, 14, 16], 1)]

def node3688Raw : WordRow := multiplyRow 16 node0403

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3688_check :
    collect (scaleRow 1 node3688Raw ++ scaleRow (-(1 : ℤ)) node3688 ++
      ([])) = [] := by
  decide +kernel

theorem node3688_mem : rowEval varIndex node3688 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3688Raw node3688 ([])
    (1) (1) (by decide) node3688_check
  · rw [node3688Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0403_mem
  · exact candidateIdeal.zero_mem

def node3694 : WordRow := [([2, 11, 16, 17], 1), ([3, 10, 16, 17], 1)]

def node3694Raw : WordRow := multiplyRow 17 node0405

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3694_check :
    collect (scaleRow 1 node3694Raw ++ scaleRow (-(1 : ℤ)) node3694 ++
      ([])) = [] := by
  decide +kernel

theorem node3694_mem : rowEval varIndex node3694 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3694Raw node3694 ([])
    (1) (1) (by decide) node3694_check
  · rw [node3694Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0405_mem
  · exact candidateIdeal.zero_mem

def node3750 : WordRow := [([1, 4, 6, 8], 2), ([2, 4, 5, 6], -1), ([3, 4, 4, 6], -1)]

def node3750Raw : WordRow := multiplyRow 6 node0417

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3750_check :
    collect (scaleRow 1 node3750Raw ++ scaleRow (-(1 : ℤ)) node3750 ++
      ([])) = [] := by
  decide +kernel

theorem node3750_mem : rowEval varIndex node3750 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3750Raw node3750 ([])
    (1) (1) (by decide) node3750_check
  · rw [node3750Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0417_mem
  · exact candidateIdeal.zero_mem

def node3752 : WordRow := [([1, 4, 8, 10], 2), ([2, 4, 5, 10], -1), ([3, 4, 4, 10], -1)]

def node3752Raw : WordRow := multiplyRow 10 node0417

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3752_check :
    collect (scaleRow 1 node3752Raw ++ scaleRow (-(1 : ℤ)) node3752 ++
      ([])) = [] := by
  decide +kernel

theorem node3752_mem : rowEval varIndex node3752 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3752Raw node3752 ([])
    (1) (1) (by decide) node3752_check
  · rw [node3752Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0417_mem
  · exact candidateIdeal.zero_mem

def node3753 : WordRow := [([3, 4, 7, 8], 1)]

def node3753Raw : WordRow := multiplyRow 11 node0417

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3753_check :
    collect (scaleRow 1 node3753Raw ++ scaleRow (-(2 : ℤ)) node3753 ++
      (scaleRow (-2) node2527 ++ scaleRow (-2) node2293 ++ scaleRow (-2) node1686 ++ scaleRow (-1) node2538 ++ scaleRow (1) node2724 ++ scaleRow (2) node2408 ++ scaleRow (1) node3383 ++ scaleRow (-1) node2733 ++ scaleRow (1) node3481)) = [] := by
  decide +kernel

theorem node3753_mem : rowEval varIndex node3753 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3753Raw node3753 (scaleRow (-2) node2527 ++ scaleRow (-2) node2293 ++ scaleRow (-2) node1686 ++ scaleRow (-1) node2538 ++ scaleRow (1) node2724 ++ scaleRow (2) node2408 ++ scaleRow (1) node3383 ++ scaleRow (-1) node2733 ++ scaleRow (1) node3481)
    (1) (2) (by decide) node3753_check
  · rw [node3753Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0417_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2527 node2527_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2293 node2293_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1686 node1686_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2538 node2538_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node2724 node2724_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2408 node2408_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3383 node3383_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2733 node2733_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3481 node3481_mem)))))))))

def node3758 : WordRow := [([1, 4, 8, 16], 2), ([2, 4, 5, 16], -1), ([3, 4, 4, 16], -1)]

def node3758Raw : WordRow := multiplyRow 16 node0417

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3758_check :
    collect (scaleRow 1 node3758Raw ++ scaleRow (-(1 : ℤ)) node3758 ++
      ([])) = [] := by
  decide +kernel

theorem node3758_mem : rowEval varIndex node3758 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3758Raw node3758 ([])
    (1) (1) (by decide) node3758_check
  · rw [node3758Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0417_mem
  · exact candidateIdeal.zero_mem

def node3773 : WordRow := [([2, 5, 8, 17], 1), ([3, 4, 8, 17], -1)]

def node3773Raw : WordRow := multiplyRow 17 node0418

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3773_check :
    collect (scaleRow 1 node3773Raw ++ scaleRow (-(1 : ℤ)) node3773 ++
      ([])) = [] := by
  decide +kernel

theorem node3773_mem : rowEval varIndex node3773 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3773Raw node3773 ([])
    (1) (1) (by decide) node3773_check
  · rw [node3773Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0418_mem
  · exact candidateIdeal.zero_mem

def node3799 : WordRow := [([4, 6, 9, 14], 1), ([5, 6, 8, 14], 1)]

def node3799Raw : WordRow := multiplyRow 14 node0421

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3799_check :
    collect (scaleRow 1 node3799Raw ++ scaleRow (-(1 : ℤ)) node3799 ++
      ([])) = [] := by
  decide +kernel

theorem node3799_mem : rowEval varIndex node3799 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3799Raw node3799 ([])
    (1) (1) (by decide) node3799_check
  · rw [node3799Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0421_mem
  · exact candidateIdeal.zero_mem

def node3800 : WordRow := [([4, 6, 9, 15], 1), ([5, 6, 8, 15], 1)]

def node3800Raw : WordRow := multiplyRow 15 node0421

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3800_check :
    collect (scaleRow 1 node3800Raw ++ scaleRow (-(1 : ℤ)) node3800 ++
      ([])) = [] := by
  decide +kernel

theorem node3800_mem : rowEval varIndex node3800 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3800Raw node3800 ([])
    (1) (1) (by decide) node3800_check
  · rw [node3800Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0421_mem
  · exact candidateIdeal.zero_mem

def node3802 : WordRow := [([4, 6, 9, 17], 1), ([5, 6, 8, 17], 1)]

def node3802Raw : WordRow := multiplyRow 17 node0421

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3802_check :
    collect (scaleRow 1 node3802Raw ++ scaleRow (-(1 : ℤ)) node3802 ++
      ([])) = [] := by
  decide +kernel

theorem node3802_mem : rowEval varIndex node3802 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3802Raw node3802 ([])
    (1) (1) (by decide) node3802_check
  · rw [node3802Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0421_mem
  · exact candidateIdeal.zero_mem

def node3809 : WordRow := [([4, 7, 9, 14], 1), ([5, 7, 8, 14], 1)]

def node3809Raw : WordRow := multiplyRow 14 node0422

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3809_check :
    collect (scaleRow 1 node3809Raw ++ scaleRow (-(1 : ℤ)) node3809 ++
      ([])) = [] := by
  decide +kernel

theorem node3809_mem : rowEval varIndex node3809 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3809Raw node3809 ([])
    (1) (1) (by decide) node3809_check
  · rw [node3809Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0422_mem
  · exact candidateIdeal.zero_mem

def node3811 : WordRow := [([4, 7, 9, 16], 1), ([5, 7, 8, 16], 1)]

def node3811Raw : WordRow := multiplyRow 16 node0422

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3811_check :
    collect (scaleRow 1 node3811Raw ++ scaleRow (-(1 : ℤ)) node3811 ++
      ([])) = [] := by
  decide +kernel

theorem node3811_mem : rowEval varIndex node3811 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3811Raw node3811 ([])
    (1) (1) (by decide) node3811_check
  · rw [node3811Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0422_mem
  · exact candidateIdeal.zero_mem

def node3835 : WordRow := [([4, 9, 10, 13], 1), ([5, 8, 10, 13], 1)]

def node3835Raw : WordRow := multiplyRow 13 node0425

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3835_check :
    collect (scaleRow 1 node3835Raw ++ scaleRow (-(1 : ℤ)) node3835 ++
      ([])) = [] := by
  decide +kernel

theorem node3835_mem : rowEval varIndex node3835 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3835Raw node3835 ([])
    (1) (1) (by decide) node3835_check
  · rw [node3835Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0425_mem
  · exact candidateIdeal.zero_mem

def node3836 : WordRow := [([4, 9, 10, 14], 1), ([5, 8, 10, 14], 1)]

def node3836Raw : WordRow := multiplyRow 14 node0425

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3836_check :
    collect (scaleRow 1 node3836Raw ++ scaleRow (-(1 : ℤ)) node3836 ++
      ([])) = [] := by
  decide +kernel

theorem node3836_mem : rowEval varIndex node3836 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3836Raw node3836 ([])
    (1) (1) (by decide) node3836_check
  · rw [node3836Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0425_mem
  · exact candidateIdeal.zero_mem

def node3838 : WordRow := [([4, 9, 10, 16], 1), ([5, 8, 10, 16], 1)]

def node3838Raw : WordRow := multiplyRow 16 node0425

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3838_check :
    collect (scaleRow 1 node3838Raw ++ scaleRow (-(1 : ℤ)) node3838 ++
      ([])) = [] := by
  decide +kernel

theorem node3838_mem : rowEval varIndex node3838 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3838Raw node3838 ([])
    (1) (1) (by decide) node3838_check
  · rw [node3838Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0425_mem
  · exact candidateIdeal.zero_mem

def node3839 : WordRow := [([4, 9, 10, 17], 1), ([5, 8, 10, 17], 1)]

def node3839Raw : WordRow := multiplyRow 17 node0425

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3839_check :
    collect (scaleRow 1 node3839Raw ++ scaleRow (-(1 : ℤ)) node3839 ++
      ([])) = [] := by
  decide +kernel

theorem node3839_mem : rowEval varIndex node3839 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3839Raw node3839 ([])
    (1) (1) (by decide) node3839_check
  · rw [node3839Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0425_mem
  · exact candidateIdeal.zero_mem

def node3841 : WordRow := [([4, 9, 11, 12], 1), ([5, 8, 11, 12], 1)]

def node3841Raw : WordRow := multiplyRow 12 node0426

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3841_check :
    collect (scaleRow 1 node3841Raw ++ scaleRow (-(1 : ℤ)) node3841 ++
      ([])) = [] := by
  decide +kernel

theorem node3841_mem : rowEval varIndex node3841 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3841Raw node3841 ([])
    (1) (1) (by decide) node3841_check
  · rw [node3841Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0426_mem
  · exact candidateIdeal.zero_mem

def node3845 : WordRow := [([4, 9, 11, 16], 1), ([5, 8, 11, 16], 1)]

def node3845Raw : WordRow := multiplyRow 16 node0426

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3845_check :
    collect (scaleRow 1 node3845Raw ++ scaleRow (-(1 : ℤ)) node3845 ++
      ([])) = [] := by
  decide +kernel

theorem node3845_mem : rowEval varIndex node3845 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3845Raw node3845 ([])
    (1) (1) (by decide) node3845_check
  · rw [node3845Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0426_mem
  · exact candidateIdeal.zero_mem

def node3852 : WordRow := [([4, 9, 12, 17], 1), ([5, 8, 12, 17], 1)]

def node3852Raw : WordRow := multiplyRow 17 node0427

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3852_check :
    collect (scaleRow 1 node3852Raw ++ scaleRow (-(1 : ℤ)) node3852 ++
      ([])) = [] := by
  decide +kernel

theorem node3852_mem : rowEval varIndex node3852 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3852Raw node3852 ([])
    (1) (1) (by decide) node3852_check
  · rw [node3852Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0427_mem
  · exact candidateIdeal.zero_mem

def node3856 : WordRow := [([4, 9, 13, 16], 1), ([5, 8, 13, 16], 1)]

def node3856Raw : WordRow := multiplyRow 16 node0428

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3856_check :
    collect (scaleRow 1 node3856Raw ++ scaleRow (-(1 : ℤ)) node3856 ++
      ([])) = [] := by
  decide +kernel

theorem node3856_mem : rowEval varIndex node3856 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3856Raw node3856 ([])
    (1) (1) (by decide) node3856_check
  · rw [node3856Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0428_mem
  · exact candidateIdeal.zero_mem

def node3860 : WordRow := [([4, 9, 14, 16], 1), ([5, 8, 14, 16], 1)]

def node3860Raw : WordRow := multiplyRow 16 node0429

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3860_check :
    collect (scaleRow 1 node3860Raw ++ scaleRow (-(1 : ℤ)) node3860 ++
      ([])) = [] := by
  decide +kernel

theorem node3860_mem : rowEval varIndex node3860 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3860Raw node3860 ([])
    (1) (1) (by decide) node3860_check
  · rw [node3860Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0429_mem
  · exact candidateIdeal.zero_mem

def node3866 : WordRow := [([4, 9, 16, 17], 1), ([5, 8, 16, 17], 1)]

def node3866Raw : WordRow := multiplyRow 17 node0431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3866_check :
    collect (scaleRow 1 node3866Raw ++ scaleRow (-(1 : ℤ)) node3866 ++
      ([])) = [] := by
  decide +kernel

theorem node3866_mem : rowEval varIndex node3866 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3866Raw node3866 ([])
    (1) (1) (by decide) node3866_check
  · rw [node3866Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0431_mem
  · exact candidateIdeal.zero_mem

def node3874 : WordRow := [([5, 6, 9, 14], 1)]

def node3874Raw : WordRow := multiplyRow 14 node0433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3874_check :
    collect (scaleRow 1 node3874Raw ++ scaleRow (-(1 : ℤ)) node3874 ++
      ([])) = [] := by
  decide +kernel

theorem node3874_mem : rowEval varIndex node3874 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3874Raw node3874 ([])
    (1) (1) (by decide) node3874_check
  · rw [node3874Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0433_mem
  · exact candidateIdeal.zero_mem

def node3939 : WordRow := [([0, 0, 0, 15], 1), ([0, 0, 1, 14], 1), ([0, 0, 2, 13], -1), ([0, 0, 3, 12], -1), ([0, 0, 4, 11], -1), ([0, 0, 5, 10], -1), ([0, 0, 6, 9], -1), ([0, 0, 7, 8], -1)]

def node3939Raw : WordRow := multiplyRow 0 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3939_check :
    collect (scaleRow 1 node3939Raw ++ scaleRow (-(1 : ℤ)) node3939 ++
      ([])) = [] := by
  decide +kernel

theorem node3939_mem : rowEval varIndex node3939 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3939Raw node3939 ([])
    (1) (1) (by decide) node3939_check
  · rw [node3939Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3940 : WordRow := [([0, 0, 2, 15], 1), ([0, 1, 2, 14], 1), ([0, 2, 2, 13], -1), ([0, 2, 3, 12], -1), ([0, 2, 4, 11], -1), ([0, 2, 5, 10], -1), ([0, 2, 6, 9], -1), ([0, 2, 7, 8], -1)]

def node3940Raw : WordRow := multiplyRow 2 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3940_check :
    collect (scaleRow 1 node3940Raw ++ scaleRow (-(1 : ℤ)) node3940 ++
      ([])) = [] := by
  decide +kernel

theorem node3940_mem : rowEval varIndex node3940 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3940Raw node3940 ([])
    (1) (1) (by decide) node3940_check
  · rw [node3940Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3941 : WordRow := [([0, 0, 4, 15], 1), ([0, 1, 4, 14], 1), ([0, 2, 4, 13], -1), ([0, 3, 4, 12], -1), ([0, 4, 4, 11], -1), ([0, 4, 5, 10], -1), ([0, 4, 6, 9], -1), ([0, 4, 7, 8], -1)]

def node3941Raw : WordRow := multiplyRow 4 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3941_check :
    collect (scaleRow 1 node3941Raw ++ scaleRow (-(1 : ℤ)) node3941 ++
      ([])) = [] := by
  decide +kernel

theorem node3941_mem : rowEval varIndex node3941 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3941Raw node3941 ([])
    (1) (1) (by decide) node3941_check
  · rw [node3941Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3942 : WordRow := [([0, 0, 6, 15], 1), ([0, 1, 6, 14], 1), ([0, 2, 6, 13], -1), ([0, 3, 6, 12], -1), ([0, 4, 6, 11], -1), ([0, 5, 6, 10], -1), ([0, 6, 6, 9], -1), ([0, 6, 7, 8], -1)]

def node3942Raw : WordRow := multiplyRow 6 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3942_check :
    collect (scaleRow 1 node3942Raw ++ scaleRow (-(1 : ℤ)) node3942 ++
      ([])) = [] := by
  decide +kernel

theorem node3942_mem : rowEval varIndex node3942 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3942Raw node3942 ([])
    (1) (1) (by decide) node3942_check
  · rw [node3942Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3943 : WordRow := [([0, 0, 8, 15], 1), ([0, 1, 8, 14], 1), ([0, 2, 8, 13], -1), ([0, 3, 8, 12], -1), ([0, 4, 8, 11], -1), ([0, 5, 8, 10], -1), ([0, 6, 8, 9], -1), ([0, 7, 8, 8], -1)]

def node3943Raw : WordRow := multiplyRow 8 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3943_check :
    collect (scaleRow 1 node3943Raw ++ scaleRow (-(1 : ℤ)) node3943 ++
      ([])) = [] := by
  decide +kernel

theorem node3943_mem : rowEval varIndex node3943 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3943Raw node3943 ([])
    (1) (1) (by decide) node3943_check
  · rw [node3943Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3945 : WordRow := [([0, 0, 10, 15], 1), ([0, 1, 10, 14], 1), ([0, 2, 10, 13], -1), ([0, 3, 10, 12], -1), ([0, 4, 10, 11], -1), ([0, 5, 10, 10], -1), ([0, 6, 9, 10], -1), ([0, 7, 8, 10], -1)]

def node3945Raw : WordRow := multiplyRow 10 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3945_check :
    collect (scaleRow 1 node3945Raw ++ scaleRow (-(1 : ℤ)) node3945 ++
      ([])) = [] := by
  decide +kernel

theorem node3945_mem : rowEval varIndex node3945 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3945Raw node3945 ([])
    (1) (1) (by decide) node3945_check
  · rw [node3945Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3947 : WordRow := [([0, 0, 12, 15], 1), ([0, 1, 12, 14], 1), ([0, 2, 12, 13], -1), ([0, 3, 12, 12], -1), ([0, 4, 11, 12], -1), ([0, 5, 10, 12], -1), ([0, 6, 9, 12], -1), ([0, 7, 8, 12], -1)]

def node3947Raw : WordRow := multiplyRow 12 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3947_check :
    collect (scaleRow 1 node3947Raw ++ scaleRow (-(1 : ℤ)) node3947 ++
      ([])) = [] := by
  decide +kernel

theorem node3947_mem : rowEval varIndex node3947 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3947Raw node3947 ([])
    (1) (1) (by decide) node3947_check
  · rw [node3947Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3949 : WordRow := [([0, 0, 14, 15], 1), ([0, 1, 14, 14], 1), ([0, 2, 13, 14], -1), ([0, 3, 12, 14], -1), ([0, 4, 11, 14], -1), ([0, 5, 10, 14], -1), ([0, 6, 9, 14], -1), ([0, 7, 8, 14], -1)]

def node3949Raw : WordRow := multiplyRow 14 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3949_check :
    collect (scaleRow 1 node3949Raw ++ scaleRow (-(1 : ℤ)) node3949 ++
      ([])) = [] := by
  decide +kernel

theorem node3949_mem : rowEval varIndex node3949 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3949Raw node3949 ([])
    (1) (1) (by decide) node3949_check
  · rw [node3949Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3951 : WordRow := [([0, 0, 15, 16], 1), ([0, 1, 14, 16], 1), ([0, 2, 13, 16], -1), ([0, 3, 12, 16], -1), ([0, 4, 11, 16], -1), ([0, 5, 10, 16], -1), ([0, 6, 9, 16], -1), ([0, 7, 8, 16], -1)]

def node3951Raw : WordRow := multiplyRow 16 node0445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3951_check :
    collect (scaleRow 1 node3951Raw ++ scaleRow (-(1 : ℤ)) node3951 ++
      ([])) = [] := by
  decide +kernel

theorem node3951_mem : rowEval varIndex node3951 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3951Raw node3951 ([])
    (1) (1) (by decide) node3951_check
  · rw [node3951Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0445_mem
  · exact candidateIdeal.zero_mem

def node3954 : WordRow := [([0, 2, 4, 15], 1), ([1, 2, 4, 14], 1), ([2, 2, 4, 13], -1), ([2, 3, 4, 12], -1), ([2, 4, 4, 11], -1), ([2, 4, 5, 10], -1), ([2, 4, 6, 9], -1), ([2, 4, 7, 8], -1)]

def node3954Raw : WordRow := multiplyRow 4 node0446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3954_check :
    collect (scaleRow 1 node3954Raw ++ scaleRow (-(1 : ℤ)) node3954 ++
      ([])) = [] := by
  decide +kernel

theorem node3954_mem : rowEval varIndex node3954 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3954Raw node3954 ([])
    (1) (1) (by decide) node3954_check
  · rw [node3954Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0446_mem
  · exact candidateIdeal.zero_mem

def node3955 : WordRow := [([0, 2, 6, 15], 1), ([1, 2, 6, 14], 1), ([2, 2, 6, 13], -1), ([2, 3, 6, 12], -1), ([2, 4, 6, 11], -1), ([2, 5, 6, 10], -1), ([2, 6, 6, 9], -1), ([2, 6, 7, 8], -1)]

def node3955Raw : WordRow := multiplyRow 6 node0446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3955_check :
    collect (scaleRow 1 node3955Raw ++ scaleRow (-(1 : ℤ)) node3955 ++
      ([])) = [] := by
  decide +kernel

theorem node3955_mem : rowEval varIndex node3955 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3955Raw node3955 ([])
    (1) (1) (by decide) node3955_check
  · rw [node3955Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0446_mem
  · exact candidateIdeal.zero_mem

def node3961 : WordRow := [([0, 2, 12, 15], 1), ([1, 2, 12, 14], 1), ([2, 2, 12, 13], -1), ([2, 3, 12, 12], -1), ([2, 4, 11, 12], -1), ([2, 5, 10, 12], -1), ([2, 6, 9, 12], -1), ([2, 7, 8, 12], -1)]

def node3961Raw : WordRow := multiplyRow 12 node0446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3961_check :
    collect (scaleRow 1 node3961Raw ++ scaleRow (-(1 : ℤ)) node3961 ++
      ([])) = [] := by
  decide +kernel

theorem node3961_mem : rowEval varIndex node3961 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3961Raw node3961 ([])
    (1) (1) (by decide) node3961_check
  · rw [node3961Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0446_mem
  · exact candidateIdeal.zero_mem

def node3963 : WordRow := [([0, 2, 14, 15], 1), ([1, 2, 14, 14], 1), ([2, 2, 13, 14], -1), ([2, 3, 12, 14], -1), ([2, 4, 11, 14], -1), ([2, 5, 10, 14], -1), ([2, 6, 9, 14], -1), ([2, 7, 8, 14], -1)]

def node3963Raw : WordRow := multiplyRow 14 node0446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3963_check :
    collect (scaleRow 1 node3963Raw ++ scaleRow (-(1 : ℤ)) node3963 ++
      ([])) = [] := by
  decide +kernel

theorem node3963_mem : rowEval varIndex node3963 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3963Raw node3963 ([])
    (1) (1) (by decide) node3963_check
  · rw [node3963Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0446_mem
  · exact candidateIdeal.zero_mem

def node3965 : WordRow := [([0, 2, 15, 16], 1), ([1, 2, 14, 16], 1), ([2, 2, 13, 16], -1), ([2, 3, 12, 16], -1), ([2, 4, 11, 16], -1), ([2, 5, 10, 16], -1), ([2, 6, 9, 16], -1), ([2, 7, 8, 16], -1)]

def node3965Raw : WordRow := multiplyRow 16 node0446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3965_check :
    collect (scaleRow 1 node3965Raw ++ scaleRow (-(1 : ℤ)) node3965 ++
      ([])) = [] := by
  decide +kernel

theorem node3965_mem : rowEval varIndex node3965 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3965Raw node3965 ([])
    (1) (1) (by decide) node3965_check
  · rw [node3965Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0446_mem
  · exact candidateIdeal.zero_mem

def node3974 : WordRow := [([0, 4, 6, 15], 1), ([1, 4, 6, 14], 1), ([2, 4, 6, 13], -1), ([3, 4, 6, 12], -1), ([4, 4, 6, 11], -1), ([4, 5, 6, 10], -1), ([4, 6, 6, 9], -1), ([4, 6, 7, 8], -1)]

def node3974Raw : WordRow := multiplyRow 6 node0448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3974_check :
    collect (scaleRow 1 node3974Raw ++ scaleRow (-(1 : ℤ)) node3974 ++
      ([])) = [] := by
  decide +kernel

theorem node3974_mem : rowEval varIndex node3974 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3974Raw node3974 ([])
    (1) (1) (by decide) node3974_check
  · rw [node3974Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0448_mem
  · exact candidateIdeal.zero_mem

def node3978 : WordRow := [([0, 4, 10, 15], 1), ([1, 4, 10, 14], 1), ([2, 4, 10, 13], -1), ([3, 4, 10, 12], -1), ([4, 4, 10, 11], -1), ([4, 5, 10, 10], -1), ([4, 6, 9, 10], -1), ([4, 7, 8, 10], -1)]

def node3978Raw : WordRow := multiplyRow 10 node0448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3978_check :
    collect (scaleRow 1 node3978Raw ++ scaleRow (-(1 : ℤ)) node3978 ++
      ([])) = [] := by
  decide +kernel

theorem node3978_mem : rowEval varIndex node3978 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3978Raw node3978 ([])
    (1) (1) (by decide) node3978_check
  · rw [node3978Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0448_mem
  · exact candidateIdeal.zero_mem

def node3982 : WordRow := [([0, 4, 14, 15], 1), ([1, 4, 14, 14], 1), ([2, 4, 13, 14], -1), ([3, 4, 12, 14], -1), ([4, 4, 11, 14], -1), ([4, 5, 10, 14], -1), ([4, 6, 9, 14], -1), ([4, 7, 8, 14], -1)]

def node3982Raw : WordRow := multiplyRow 14 node0448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3982_check :
    collect (scaleRow 1 node3982Raw ++ scaleRow (-(1 : ℤ)) node3982 ++
      ([])) = [] := by
  decide +kernel

theorem node3982_mem : rowEval varIndex node3982 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3982Raw node3982 ([])
    (1) (1) (by decide) node3982_check
  · rw [node3982Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0448_mem
  · exact candidateIdeal.zero_mem

def node3984 : WordRow := [([0, 4, 15, 16], 1), ([1, 4, 14, 16], 1), ([2, 4, 13, 16], -1), ([3, 4, 12, 16], -1), ([4, 4, 11, 16], -1), ([4, 5, 10, 16], -1), ([4, 6, 9, 16], -1), ([4, 7, 8, 16], -1)]

def node3984Raw : WordRow := multiplyRow 16 node0448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3984_check :
    collect (scaleRow 1 node3984Raw ++ scaleRow (-(1 : ℤ)) node3984 ++
      ([])) = [] := by
  decide +kernel

theorem node3984_mem : rowEval varIndex node3984 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3984Raw node3984 ([])
    (1) (1) (by decide) node3984_check
  · rw [node3984Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0448_mem
  · exact candidateIdeal.zero_mem

def node3990 : WordRow := [([1, 4, 14, 15], 1), ([1, 5, 14, 14], -1), ([2, 5, 13, 14], 1), ([3, 5, 12, 14], 1), ([4, 5, 11, 14], 1), ([5, 5, 10, 14], 1), ([5, 6, 9, 14], 1), ([5, 7, 8, 14], 1)]

def node3990Raw : WordRow := multiplyRow 14 node0449

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3990_check :
    collect (scaleRow 1 node3990Raw ++ scaleRow (-(1 : ℤ)) node3990 ++
      ([])) = [] := by
  decide +kernel

theorem node3990_mem : rowEval varIndex node3990 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3990Raw node3990 ([])
    (1) (1) (by decide) node3990_check
  · rw [node3990Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0449_mem
  · exact candidateIdeal.zero_mem

def node3995 : WordRow := [([0, 6, 8, 15], 1), ([1, 6, 8, 14], 1), ([2, 6, 8, 13], -1), ([3, 6, 8, 12], -1), ([4, 6, 8, 11], -1), ([5, 6, 8, 10], -1), ([6, 6, 8, 9], -1), ([6, 7, 8, 8], -1)]

def node3995Raw : WordRow := multiplyRow 8 node0450

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3995_check :
    collect (scaleRow 1 node3995Raw ++ scaleRow (-(1 : ℤ)) node3995 ++
      ([])) = [] := by
  decide +kernel

theorem node3995_mem : rowEval varIndex node3995 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3995Raw node3995 ([])
    (1) (1) (by decide) node3995_check
  · rw [node3995Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0450_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node3995_mem
