import VOA.DeligneAudit.D4FusionContactM2Dag15

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node5750 : WordRow := [([10, 16, 17, 17], 1)]

def node5750Raw : WordRow := multiplyRow 10 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5750_check :
    collect (scaleRow 1 node5750Raw ++ scaleRow (-(1 : ℤ)) node5750 ++
      ([])) = [] := by
  decide +kernel

theorem node5750_mem : rowEval varIndex node5750 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5750Raw node5750 ([])
    (1) (1) (by decide) node5750_check
  · rw [node5750Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5752 : WordRow := [([12, 16, 17, 17], 1)]

def node5752Raw : WordRow := multiplyRow 12 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5752_check :
    collect (scaleRow 1 node5752Raw ++ scaleRow (-(1 : ℤ)) node5752 ++
      ([])) = [] := by
  decide +kernel

theorem node5752_mem : rowEval varIndex node5752 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5752Raw node5752 ([])
    (1) (1) (by decide) node5752_check
  · rw [node5752Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5754 : WordRow := [([14, 16, 17, 17], 1)]

def node5754Raw : WordRow := multiplyRow 14 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5754_check :
    collect (scaleRow 1 node5754Raw ++ scaleRow (-(1 : ℤ)) node5754 ++
      ([])) = [] := by
  decide +kernel

theorem node5754_mem : rowEval varIndex node5754 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5754Raw node5754 ([])
    (1) (1) (by decide) node5754_check
  · rw [node5754Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5782 : WordRow := [([2, 2, 4, 7], 1), ([2, 2, 5, 6], 1)]

def node5782Raw : WordRow := multiplyRow 15 node0773

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5782_check :
    collect (scaleRow 1 node5782Raw ++ scaleRow (-(1 : ℤ)) node5782 ++
      (scaleRow (-1) node3940 ++ scaleRow (1) node0917 ++ scaleRow (-1) node2951 ++ scaleRow (-1) node1221 ++ scaleRow (-1) node2499 ++ scaleRow (-1) node1507 ++ scaleRow (-1) node2250 ++ scaleRow (-1) node1760 ++ scaleRow (2) node1971 ++ scaleRow (1) node3577 ++ scaleRow (1) node3357)) = [] := by
  decide +kernel

theorem node5782_mem : rowEval varIndex node5782 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5782Raw node5782 (scaleRow (-1) node3940 ++ scaleRow (1) node0917 ++ scaleRow (-1) node2951 ++ scaleRow (-1) node1221 ++ scaleRow (-1) node2499 ++ scaleRow (-1) node1507 ++ scaleRow (-1) node2250 ++ scaleRow (-1) node1760 ++ scaleRow (2) node1971 ++ scaleRow (1) node3577 ++ scaleRow (1) node3357)
    (1) (1) (by decide) node5782_check
  · rw [node5782Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0773_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3940 node3940_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node0917 node0917_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2951 node2951_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1221 node1221_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2499 node2499_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1507 node1507_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2250 node2250_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1760 node1760_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node1971 node1971_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3577 node3577_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3357 node3357_mem)))))))))))

def node5791 : WordRow := [([2, 4, 4, 7], 1), ([3, 4, 4, 6], 1)]

def node5791Raw : WordRow := multiplyRow 15 node0774

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5791_check :
    collect (scaleRow 1 node5791Raw ++ scaleRow (-(1 : ℤ)) node5791 ++
      (scaleRow (-1) node3941 ++ scaleRow (1) node0946 ++ scaleRow (-1) node2952 ++ scaleRow (-1) node1250 ++ scaleRow (-1) node2522 ++ scaleRow (-1) node1535 ++ scaleRow (-1) node2276 ++ scaleRow (-1) node1786 ++ scaleRow (1) node4306 ++ scaleRow (2) node2709 ++ scaleRow (1) node3750)) = [] := by
  decide +kernel

theorem node5791_mem : rowEval varIndex node5791 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5791Raw node5791 (scaleRow (-1) node3941 ++ scaleRow (1) node0946 ++ scaleRow (-1) node2952 ++ scaleRow (-1) node1250 ++ scaleRow (-1) node2522 ++ scaleRow (-1) node1535 ++ scaleRow (-1) node2276 ++ scaleRow (-1) node1786 ++ scaleRow (1) node4306 ++ scaleRow (2) node2709 ++ scaleRow (1) node3750)
    (1) (1) (by decide) node5791_check
  · rw [node5791Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0774_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3941 node3941_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node0946 node0946_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2952 node2952_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1250 node1250_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2522 node2522_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1535 node1535_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2276 node2276_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1786 node1786_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4306 node4306_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2709 node2709_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3750 node3750_mem)))))))))))

def node5795 : WordRow := [([0, 0, 6, 8], 1)]

def node5795Raw : WordRow := multiplyRow 8 node0775

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5795_check :
    collect (scaleRow 1 node5795Raw ++ scaleRow (-(1 : ℤ)) node5795 ++
      ([])) = [] := by
  decide +kernel

theorem node5795_mem : rowEval varIndex node5795 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5795Raw node5795 ([])
    (1) (1) (by decide) node5795_check
  · rw [node5795Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0775_mem
  · exact candidateIdeal.zero_mem

def node5799 : WordRow := [([2, 5, 6, 6], 1), ([3, 4, 6, 6], 1)]

def node5799Raw : WordRow := multiplyRow 15 node0775

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5799_check :
    collect (scaleRow 1 node5799Raw ++ scaleRow (-(1 : ℤ)) node5799 ++
      (scaleRow (-1) node3942 ++ scaleRow (1) node0971 ++ scaleRow (-1) node2953 ++ scaleRow (-1) node1275 ++ scaleRow (-1) node2524 ++ scaleRow (-1) node1560 ++ scaleRow (-1) node2301 ++ scaleRow (-1) node1810 ++ scaleRow (1) node4468 ++ scaleRow (1) node4141 ++ scaleRow (2) node3157)) = [] := by
  decide +kernel

theorem node5799_mem : rowEval varIndex node5799 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5799Raw node5799 (scaleRow (-1) node3942 ++ scaleRow (1) node0971 ++ scaleRow (-1) node2953 ++ scaleRow (-1) node1275 ++ scaleRow (-1) node2524 ++ scaleRow (-1) node1560 ++ scaleRow (-1) node2301 ++ scaleRow (-1) node1810 ++ scaleRow (1) node4468 ++ scaleRow (1) node4141 ++ scaleRow (2) node3157)
    (1) (1) (by decide) node5799_check
  · rw [node5799Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0775_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3942 node3942_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node0971 node0971_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2953 node2953_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1275 node1275_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2524 node2524_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1560 node1560_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2301 node2301_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1810 node1810_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4468 node4468_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4141 node4141_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node3157 node3157_mem)))))))))))

def node5803 : WordRow := [([0, 2, 17, 17], 1), ([1, 2, 16, 17], 2)]

def node5803Raw : WordRow := multiplyRow 2 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5803_check :
    collect (scaleRow 1 node5803Raw ++ scaleRow (-(1 : ℤ)) node5803 ++
      ([])) = [] := by
  decide +kernel

theorem node5803_mem : rowEval varIndex node5803 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5803Raw node5803 ([])
    (1) (1) (by decide) node5803_check
  · rw [node5803Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5805 : WordRow := [([0, 4, 17, 17], 1), ([1, 4, 16, 17], 2)]

def node5805Raw : WordRow := multiplyRow 4 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5805_check :
    collect (scaleRow 1 node5805Raw ++ scaleRow (-(1 : ℤ)) node5805 ++
      ([])) = [] := by
  decide +kernel

theorem node5805_mem : rowEval varIndex node5805 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5805Raw node5805 ([])
    (1) (1) (by decide) node5805_check
  · rw [node5805Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5807 : WordRow := [([0, 6, 17, 17], 1), ([1, 6, 16, 17], 2)]

def node5807Raw : WordRow := multiplyRow 6 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5807_check :
    collect (scaleRow 1 node5807Raw ++ scaleRow (-(1 : ℤ)) node5807 ++
      ([])) = [] := by
  decide +kernel

theorem node5807_mem : rowEval varIndex node5807 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5807Raw node5807 ([])
    (1) (1) (by decide) node5807_check
  · rw [node5807Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5809 : WordRow := [([0, 8, 17, 17], 1), ([1, 8, 16, 17], 2)]

def node5809Raw : WordRow := multiplyRow 8 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5809_check :
    collect (scaleRow 1 node5809Raw ++ scaleRow (-(1 : ℤ)) node5809 ++
      ([])) = [] := by
  decide +kernel

theorem node5809_mem : rowEval varIndex node5809 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5809Raw node5809 ([])
    (1) (1) (by decide) node5809_check
  · rw [node5809Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5811 : WordRow := [([0, 10, 17, 17], 1), ([1, 10, 16, 17], 2)]

def node5811Raw : WordRow := multiplyRow 10 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5811_check :
    collect (scaleRow 1 node5811Raw ++ scaleRow (-(1 : ℤ)) node5811 ++
      ([])) = [] := by
  decide +kernel

theorem node5811_mem : rowEval varIndex node5811 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5811Raw node5811 ([])
    (1) (1) (by decide) node5811_check
  · rw [node5811Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5813 : WordRow := [([0, 12, 17, 17], 1), ([1, 12, 16, 17], 2)]

def node5813Raw : WordRow := multiplyRow 12 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5813_check :
    collect (scaleRow 1 node5813Raw ++ scaleRow (-(1 : ℤ)) node5813 ++
      ([])) = [] := by
  decide +kernel

theorem node5813_mem : rowEval varIndex node5813 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5813Raw node5813 ([])
    (1) (1) (by decide) node5813_check
  · rw [node5813Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5815 : WordRow := [([0, 14, 17, 17], 1), ([1, 14, 16, 17], 2)]

def node5815Raw : WordRow := multiplyRow 14 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5815_check :
    collect (scaleRow 1 node5815Raw ++ scaleRow (-(1 : ℤ)) node5815 ++
      ([])) = [] := by
  decide +kernel

theorem node5815_mem : rowEval varIndex node5815 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5815Raw node5815 ([])
    (1) (1) (by decide) node5815_check
  · rw [node5815Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · exact candidateIdeal.zero_mem

def node5817 : WordRow := [([1, 16, 16, 17], 1)]

def node5817Raw : WordRow := multiplyRow 16 node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5817_check :
    collect (scaleRow 1 node5817Raw ++ scaleRow (-(2 : ℤ)) node5817 ++
      (scaleRow (-1) node5740)) = [] := by
  decide +kernel

theorem node5817_mem : rowEval varIndex node5817 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5817Raw node5817 (scaleRow (-1) node5740)
    (1) (2) (by decide) node5817_check
  · rw [node5817Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5740 node5740_mem)

def node5826 : WordRow := [([1, 2, 16, 17], 1)]

def node5826Raw : WordRow := multiplyRow 0 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5826_check :
    collect (scaleRow 1 node5826Raw ++ scaleRow (-(-4 : ℤ)) node5826 ++
      (scaleRow (-1) node5803 ++ scaleRow (-2) node1345)) = [] := by
  decide +kernel

theorem node5826_mem : rowEval varIndex node5826 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5826Raw node5826 (scaleRow (-1) node5803 ++ scaleRow (-2) node1345)
    (1) (-4) (by decide) node5826_check
  · rw [node5826Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5803 node5803_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1345 node1345_mem))

def node5828 : WordRow := [([2, 4, 17, 17], 1), ([3, 4, 16, 17], 2)]

def node5828Raw : WordRow := multiplyRow 4 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5828_check :
    collect (scaleRow 1 node5828Raw ++ scaleRow (-(1 : ℤ)) node5828 ++
      ([])) = [] := by
  decide +kernel

theorem node5828_mem : rowEval varIndex node5828 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5828Raw node5828 ([])
    (1) (1) (by decide) node5828_check
  · rw [node5828Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5830 : WordRow := [([2, 6, 17, 17], 1), ([3, 6, 16, 17], 2)]

def node5830Raw : WordRow := multiplyRow 6 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5830_check :
    collect (scaleRow 1 node5830Raw ++ scaleRow (-(1 : ℤ)) node5830 ++
      ([])) = [] := by
  decide +kernel

theorem node5830_mem : rowEval varIndex node5830 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5830Raw node5830 ([])
    (1) (1) (by decide) node5830_check
  · rw [node5830Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5832 : WordRow := [([2, 8, 17, 17], 1), ([3, 8, 16, 17], 2)]

def node5832Raw : WordRow := multiplyRow 8 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5832_check :
    collect (scaleRow 1 node5832Raw ++ scaleRow (-(1 : ℤ)) node5832 ++
      ([])) = [] := by
  decide +kernel

theorem node5832_mem : rowEval varIndex node5832 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5832Raw node5832 ([])
    (1) (1) (by decide) node5832_check
  · rw [node5832Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5834 : WordRow := [([2, 10, 17, 17], 1), ([3, 10, 16, 17], 2)]

def node5834Raw : WordRow := multiplyRow 10 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5834_check :
    collect (scaleRow 1 node5834Raw ++ scaleRow (-(1 : ℤ)) node5834 ++
      ([])) = [] := by
  decide +kernel

theorem node5834_mem : rowEval varIndex node5834 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5834Raw node5834 ([])
    (1) (1) (by decide) node5834_check
  · rw [node5834Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5836 : WordRow := [([2, 12, 17, 17], 1), ([3, 12, 16, 17], 2)]

def node5836Raw : WordRow := multiplyRow 12 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5836_check :
    collect (scaleRow 1 node5836Raw ++ scaleRow (-(1 : ℤ)) node5836 ++
      ([])) = [] := by
  decide +kernel

theorem node5836_mem : rowEval varIndex node5836 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5836Raw node5836 ([])
    (1) (1) (by decide) node5836_check
  · rw [node5836Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5838 : WordRow := [([2, 14, 17, 17], 1), ([3, 14, 16, 17], 2)]

def node5838Raw : WordRow := multiplyRow 14 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5838_check :
    collect (scaleRow 1 node5838Raw ++ scaleRow (-(1 : ℤ)) node5838 ++
      ([])) = [] := by
  decide +kernel

theorem node5838_mem : rowEval varIndex node5838 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5838Raw node5838 ([])
    (1) (1) (by decide) node5838_check
  · rw [node5838Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · exact candidateIdeal.zero_mem

def node5840 : WordRow := [([3, 16, 16, 17], 1)]

def node5840Raw : WordRow := multiplyRow 16 node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5840_check :
    collect (scaleRow 1 node5840Raw ++ scaleRow (-(2 : ℤ)) node5840 ++
      (scaleRow (-1) node5742)) = [] := by
  decide +kernel

theorem node5840_mem : rowEval varIndex node5840 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5840Raw node5840 (scaleRow (-1) node5742)
    (1) (2) (by decide) node5840_check
  · rw [node5840Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5742 node5742_mem)

def node5845 : WordRow := [([1, 4, 16, 17], 1)]

def node5845Raw : WordRow := multiplyRow 0 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5845_check :
    collect (scaleRow 1 node5845Raw ++ scaleRow (-(-4 : ℤ)) node5845 ++
      (scaleRow (-1) node5805 ++ scaleRow (-2) node1632)) = [] := by
  decide +kernel

theorem node5845_mem : rowEval varIndex node5845 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5845Raw node5845 (scaleRow (-1) node5805 ++ scaleRow (-2) node1632)
    (1) (-4) (by decide) node5845_check
  · rw [node5845Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5805 node5805_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1632 node1632_mem))

def node5846 : WordRow := [([2, 5, 16, 17], 1), ([3, 4, 16, 17], -1)]

def node5846Raw : WordRow := multiplyRow 2 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5846_check :
    collect (scaleRow 1 node5846Raw ++ scaleRow (-(2 : ℤ)) node5846 ++
      (scaleRow (-1) node5828)) = [] := by
  decide +kernel

theorem node5846_mem : rowEval varIndex node5846 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5846Raw node5846 (scaleRow (-1) node5828)
    (1) (2) (by decide) node5846_check
  · rw [node5846Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5828 node5828_mem)

def node5849 : WordRow := [([4, 6, 17, 17], 1), ([5, 6, 16, 17], 2)]

def node5849Raw : WordRow := multiplyRow 6 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5849_check :
    collect (scaleRow 1 node5849Raw ++ scaleRow (-(1 : ℤ)) node5849 ++
      ([])) = [] := by
  decide +kernel

theorem node5849_mem : rowEval varIndex node5849 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5849Raw node5849 ([])
    (1) (1) (by decide) node5849_check
  · rw [node5849Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · exact candidateIdeal.zero_mem

def node5851 : WordRow := [([4, 8, 17, 17], 1), ([5, 8, 16, 17], 2)]

def node5851Raw : WordRow := multiplyRow 8 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5851_check :
    collect (scaleRow 1 node5851Raw ++ scaleRow (-(1 : ℤ)) node5851 ++
      ([])) = [] := by
  decide +kernel

theorem node5851_mem : rowEval varIndex node5851 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5851Raw node5851 ([])
    (1) (1) (by decide) node5851_check
  · rw [node5851Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · exact candidateIdeal.zero_mem

def node5853 : WordRow := [([4, 10, 17, 17], 1), ([5, 10, 16, 17], 2)]

def node5853Raw : WordRow := multiplyRow 10 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5853_check :
    collect (scaleRow 1 node5853Raw ++ scaleRow (-(1 : ℤ)) node5853 ++
      ([])) = [] := by
  decide +kernel

theorem node5853_mem : rowEval varIndex node5853 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5853Raw node5853 ([])
    (1) (1) (by decide) node5853_check
  · rw [node5853Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · exact candidateIdeal.zero_mem

def node5855 : WordRow := [([4, 12, 17, 17], 1), ([5, 12, 16, 17], 2)]

def node5855Raw : WordRow := multiplyRow 12 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5855_check :
    collect (scaleRow 1 node5855Raw ++ scaleRow (-(1 : ℤ)) node5855 ++
      ([])) = [] := by
  decide +kernel

theorem node5855_mem : rowEval varIndex node5855 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5855Raw node5855 ([])
    (1) (1) (by decide) node5855_check
  · rw [node5855Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · exact candidateIdeal.zero_mem

def node5857 : WordRow := [([4, 14, 17, 17], 1), ([5, 14, 16, 17], 2)]

def node5857Raw : WordRow := multiplyRow 14 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5857_check :
    collect (scaleRow 1 node5857Raw ++ scaleRow (-(1 : ℤ)) node5857 ++
      ([])) = [] := by
  decide +kernel

theorem node5857_mem : rowEval varIndex node5857 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5857Raw node5857 ([])
    (1) (1) (by decide) node5857_check
  · rw [node5857Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · exact candidateIdeal.zero_mem

def node5859 : WordRow := [([5, 16, 16, 17], 1)]

def node5859Raw : WordRow := multiplyRow 16 node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5859_check :
    collect (scaleRow 1 node5859Raw ++ scaleRow (-(2 : ℤ)) node5859 ++
      (scaleRow (-1) node5744)) = [] := by
  decide +kernel

theorem node5859_mem : rowEval varIndex node5859 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5859Raw node5859 (scaleRow (-1) node5744)
    (1) (2) (by decide) node5859_check
  · rw [node5859Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5744 node5744_mem)

def node5864 : WordRow := [([1, 6, 16, 17], 1)]

def node5864Raw : WordRow := multiplyRow 0 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5864_check :
    collect (scaleRow 1 node5864Raw ++ scaleRow (-(-4 : ℤ)) node5864 ++
      (scaleRow (-1) node5807 ++ scaleRow (-2) node1884)) = [] := by
  decide +kernel

theorem node5864_mem : rowEval varIndex node5864 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5864Raw node5864 (scaleRow (-1) node5807 ++ scaleRow (-2) node1884)
    (1) (-4) (by decide) node5864_check
  · rw [node5864Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5807 node5807_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1884 node1884_mem))

def node5865 : WordRow := [([2, 7, 16, 17], 1), ([3, 6, 16, 17], -1)]

def node5865Raw : WordRow := multiplyRow 2 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5865_check :
    collect (scaleRow 1 node5865Raw ++ scaleRow (-(2 : ℤ)) node5865 ++
      (scaleRow (-1) node5830)) = [] := by
  decide +kernel

theorem node5865_mem : rowEval varIndex node5865 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5865Raw node5865 (scaleRow (-1) node5830)
    (1) (2) (by decide) node5865_check
  · rw [node5865Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5830 node5830_mem)

def node5867 : WordRow := [([4, 7, 16, 17], 1), ([5, 6, 16, 17], -1)]

def node5867Raw : WordRow := multiplyRow 4 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5867_check :
    collect (scaleRow 1 node5867Raw ++ scaleRow (-(2 : ℤ)) node5867 ++
      (scaleRow (-1) node5849)) = [] := by
  decide +kernel

theorem node5867_mem : rowEval varIndex node5867 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5867Raw node5867 (scaleRow (-1) node5849)
    (1) (2) (by decide) node5867_check
  · rw [node5867Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5849 node5849_mem)

def node5870 : WordRow := [([6, 8, 17, 17], 1), ([7, 8, 16, 17], 2)]

def node5870Raw : WordRow := multiplyRow 8 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5870_check :
    collect (scaleRow 1 node5870Raw ++ scaleRow (-(1 : ℤ)) node5870 ++
      ([])) = [] := by
  decide +kernel

theorem node5870_mem : rowEval varIndex node5870 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5870Raw node5870 ([])
    (1) (1) (by decide) node5870_check
  · rw [node5870Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · exact candidateIdeal.zero_mem

def node5872 : WordRow := [([6, 10, 17, 17], 1), ([7, 10, 16, 17], 2)]

def node5872Raw : WordRow := multiplyRow 10 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5872_check :
    collect (scaleRow 1 node5872Raw ++ scaleRow (-(1 : ℤ)) node5872 ++
      ([])) = [] := by
  decide +kernel

theorem node5872_mem : rowEval varIndex node5872 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5872Raw node5872 ([])
    (1) (1) (by decide) node5872_check
  · rw [node5872Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · exact candidateIdeal.zero_mem

def node5874 : WordRow := [([6, 12, 17, 17], 1), ([7, 12, 16, 17], 2)]

def node5874Raw : WordRow := multiplyRow 12 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5874_check :
    collect (scaleRow 1 node5874Raw ++ scaleRow (-(1 : ℤ)) node5874 ++
      ([])) = [] := by
  decide +kernel

theorem node5874_mem : rowEval varIndex node5874 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5874Raw node5874 ([])
    (1) (1) (by decide) node5874_check
  · rw [node5874Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · exact candidateIdeal.zero_mem

def node5876 : WordRow := [([6, 14, 17, 17], 1), ([7, 14, 16, 17], 2)]

def node5876Raw : WordRow := multiplyRow 14 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5876_check :
    collect (scaleRow 1 node5876Raw ++ scaleRow (-(1 : ℤ)) node5876 ++
      ([])) = [] := by
  decide +kernel

theorem node5876_mem : rowEval varIndex node5876 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5876Raw node5876 ([])
    (1) (1) (by decide) node5876_check
  · rw [node5876Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · exact candidateIdeal.zero_mem

def node5878 : WordRow := [([7, 16, 16, 17], 1)]

def node5878Raw : WordRow := multiplyRow 16 node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5878_check :
    collect (scaleRow 1 node5878Raw ++ scaleRow (-(2 : ℤ)) node5878 ++
      (scaleRow (-1) node5746)) = [] := by
  decide +kernel

theorem node5878_mem : rowEval varIndex node5878 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5878Raw node5878 (scaleRow (-1) node5746)
    (1) (2) (by decide) node5878_check
  · rw [node5878Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5746 node5746_mem)

def node5881 : WordRow := [([1, 8, 16, 17], 2), ([2, 5, 16, 17], -1), ([3, 4, 16, 17], -1)]

def node5881Raw : WordRow := multiplyRow 0 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5881_check :
    collect (scaleRow 1 node5881Raw ++ scaleRow (-(-2 : ℤ)) node5881 ++
      (scaleRow (-1) node5809 ++ scaleRow (-2) node2377)) = [] := by
  decide +kernel

theorem node5881_mem : rowEval varIndex node5881 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5881Raw node5881 (scaleRow (-1) node5809 ++ scaleRow (-2) node2377)
    (1) (-2) (by decide) node5881_check
  · rw [node5881Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5809 node5809_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node2377 node2377_mem))

def node5882 : WordRow := [([3, 8, 16, 17], 1)]

def node5882Raw : WordRow := multiplyRow 2 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5882_check :
    collect (scaleRow 1 node5882Raw ++ scaleRow (-(-4 : ℤ)) node5882 ++
      (scaleRow (-1) node5832 ++ scaleRow (-2) node3478)) = [] := by
  decide +kernel

theorem node5882_mem : rowEval varIndex node5882 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5882Raw node5882 (scaleRow (-1) node5832 ++ scaleRow (-2) node3478)
    (1) (-4) (by decide) node5882_check
  · rw [node5882Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5832 node5832_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node3478 node3478_mem))

def node5883 : WordRow := [([5, 8, 16, 17], 1)]

def node5883Raw : WordRow := multiplyRow 4 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5883_check :
    collect (scaleRow 1 node5883Raw ++ scaleRow (-(-4 : ℤ)) node5883 ++
      (scaleRow (-1) node5851 ++ scaleRow (-2) node3866)) = [] := by
  decide +kernel

theorem node5883_mem : rowEval varIndex node5883 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5883Raw node5883 (scaleRow (-1) node5851 ++ scaleRow (-2) node3866)
    (1) (-4) (by decide) node5883_check
  · rw [node5883Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5851 node5851_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node3866 node3866_mem))

def node5884 : WordRow := [([6, 9, 16, 17], 1), ([7, 8, 16, 17], -1)]

def node5884Raw : WordRow := multiplyRow 6 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5884_check :
    collect (scaleRow 1 node5884Raw ++ scaleRow (-(2 : ℤ)) node5884 ++
      (scaleRow (-1) node5870)) = [] := by
  decide +kernel

theorem node5884_mem : rowEval varIndex node5884 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5884Raw node5884 (scaleRow (-1) node5870)
    (1) (2) (by decide) node5884_check
  · rw [node5884Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5870 node5870_mem)

def node5887 : WordRow := [([8, 10, 17, 17], 1), ([9, 10, 16, 17], 2)]

def node5887Raw : WordRow := multiplyRow 10 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5887_check :
    collect (scaleRow 1 node5887Raw ++ scaleRow (-(1 : ℤ)) node5887 ++
      ([])) = [] := by
  decide +kernel

theorem node5887_mem : rowEval varIndex node5887 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5887Raw node5887 ([])
    (1) (1) (by decide) node5887_check
  · rw [node5887Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · exact candidateIdeal.zero_mem

def node5889 : WordRow := [([8, 12, 17, 17], 1), ([9, 12, 16, 17], 2)]

def node5889Raw : WordRow := multiplyRow 12 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5889_check :
    collect (scaleRow 1 node5889Raw ++ scaleRow (-(1 : ℤ)) node5889 ++
      ([])) = [] := by
  decide +kernel

theorem node5889_mem : rowEval varIndex node5889 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5889Raw node5889 ([])
    (1) (1) (by decide) node5889_check
  · rw [node5889Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · exact candidateIdeal.zero_mem

def node5891 : WordRow := [([8, 14, 17, 17], 1), ([9, 14, 16, 17], 2)]

def node5891Raw : WordRow := multiplyRow 14 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5891_check :
    collect (scaleRow 1 node5891Raw ++ scaleRow (-(1 : ℤ)) node5891 ++
      ([])) = [] := by
  decide +kernel

theorem node5891_mem : rowEval varIndex node5891 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5891Raw node5891 ([])
    (1) (1) (by decide) node5891_check
  · rw [node5891Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · exact candidateIdeal.zero_mem

def node5893 : WordRow := [([9, 16, 16, 17], 1)]

def node5893Raw : WordRow := multiplyRow 16 node0784

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5893_check :
    collect (scaleRow 1 node5893Raw ++ scaleRow (-(2 : ℤ)) node5893 ++
      (scaleRow (-1) node5748)) = [] := by
  decide +kernel

theorem node5893_mem : rowEval varIndex node5893 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5893Raw node5893 (scaleRow (-1) node5748)
    (1) (2) (by decide) node5893_check
  · rw [node5893Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0784_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5748 node5748_mem)

def node5894 : WordRow := [([1, 10, 16, 17], 2), ([2, 7, 16, 17], -1), ([3, 6, 16, 17], -1)]

def node5894Raw : WordRow := multiplyRow 0 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5894_check :
    collect (scaleRow 1 node5894Raw ++ scaleRow (-(-2 : ℤ)) node5894 ++
      (scaleRow (-1) node5811 ++ scaleRow (-2) node2624)) = [] := by
  decide +kernel

theorem node5894_mem : rowEval varIndex node5894 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5894Raw node5894 (scaleRow (-1) node5811 ++ scaleRow (-2) node2624)
    (1) (-2) (by decide) node5894_check
  · rw [node5894Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5811 node5811_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node2624 node2624_mem))

def node5895 : WordRow := [([3, 10, 16, 17], 1)]

def node5895Raw : WordRow := multiplyRow 2 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5895_check :
    collect (scaleRow 1 node5895Raw ++ scaleRow (-(-4 : ℤ)) node5895 ++
      (scaleRow (-1) node5834 ++ scaleRow (-2) node3694)) = [] := by
  decide +kernel

theorem node5895_mem : rowEval varIndex node5895 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5895Raw node5895 (scaleRow (-1) node5834 ++ scaleRow (-2) node3694)
    (1) (-4) (by decide) node5895_check
  · rw [node5895Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5834 node5834_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node3694 node3694_mem))

def node5896 : WordRow := [([4, 11, 16, 17], 1), ([5, 10, 16, 17], -1)]

def node5896Raw : WordRow := multiplyRow 4 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5896_check :
    collect (scaleRow 1 node5896Raw ++ scaleRow (-(2 : ℤ)) node5896 ++
      (scaleRow (-1) node5853)) = [] := by
  decide +kernel

theorem node5896_mem : rowEval varIndex node5896 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5896Raw node5896 (scaleRow (-1) node5853)
    (1) (2) (by decide) node5896_check
  · rw [node5896Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5853 node5853_mem)

def node5898 : WordRow := [([7, 10, 16, 17], 1)]

def node5898Raw : WordRow := multiplyRow 6 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5898_check :
    collect (scaleRow 1 node5898Raw ++ scaleRow (-(-4 : ℤ)) node5898 ++
      (scaleRow (-1) node5872 ++ scaleRow (-2) node4251)) = [] := by
  decide +kernel

theorem node5898_mem : rowEval varIndex node5898 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5898Raw node5898 (scaleRow (-1) node5872 ++ scaleRow (-2) node4251)
    (1) (-4) (by decide) node5898_check
  · rw [node5898Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5872 node5872_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4251 node4251_mem))

def node5899 : WordRow := [([8, 11, 16, 17], 1), ([9, 10, 16, 17], -1)]

def node5899Raw : WordRow := multiplyRow 8 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5899_check :
    collect (scaleRow 1 node5899Raw ++ scaleRow (-(2 : ℤ)) node5899 ++
      (scaleRow (-1) node5887)) = [] := by
  decide +kernel

theorem node5899_mem : rowEval varIndex node5899 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5899Raw node5899 (scaleRow (-1) node5887)
    (1) (2) (by decide) node5899_check
  · rw [node5899Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5887 node5887_mem)

def node5902 : WordRow := [([10, 12, 17, 17], 1), ([11, 12, 16, 17], 2)]

def node5902Raw : WordRow := multiplyRow 12 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5902_check :
    collect (scaleRow 1 node5902Raw ++ scaleRow (-(1 : ℤ)) node5902 ++
      ([])) = [] := by
  decide +kernel

theorem node5902_mem : rowEval varIndex node5902 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5902Raw node5902 ([])
    (1) (1) (by decide) node5902_check
  · rw [node5902Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · exact candidateIdeal.zero_mem

def node5904 : WordRow := [([10, 14, 17, 17], 1), ([11, 14, 16, 17], 2)]

def node5904Raw : WordRow := multiplyRow 14 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5904_check :
    collect (scaleRow 1 node5904Raw ++ scaleRow (-(1 : ℤ)) node5904 ++
      ([])) = [] := by
  decide +kernel

theorem node5904_mem : rowEval varIndex node5904 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5904Raw node5904 ([])
    (1) (1) (by decide) node5904_check
  · rw [node5904Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · exact candidateIdeal.zero_mem

def node5906 : WordRow := [([11, 16, 16, 17], 1)]

def node5906Raw : WordRow := multiplyRow 16 node0786

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5906_check :
    collect (scaleRow 1 node5906Raw ++ scaleRow (-(2 : ℤ)) node5906 ++
      (scaleRow (-1) node5750)) = [] := by
  decide +kernel

theorem node5906_mem : rowEval varIndex node5906 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5906Raw node5906 (scaleRow (-1) node5750)
    (1) (2) (by decide) node5906_check
  · rw [node5906Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0786_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5750 node5750_mem)

def node5907 : WordRow := [([1, 12, 16, 17], 2), ([4, 7, 16, 17], -1), ([5, 6, 16, 17], -1)]

def node5907Raw : WordRow := multiplyRow 0 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5907_check :
    collect (scaleRow 1 node5907Raw ++ scaleRow (-(-2 : ℤ)) node5907 ++
      (scaleRow (-1) node5813 ++ scaleRow (-2) node3074)) = [] := by
  decide +kernel

theorem node5907_mem : rowEval varIndex node5907 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5907Raw node5907 (scaleRow (-1) node5813 ++ scaleRow (-2) node3074)
    (1) (-2) (by decide) node5907_check
  · rw [node5907Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5813 node5813_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node3074 node3074_mem))

def node5908 : WordRow := [([2, 13, 16, 17], 1), ([3, 12, 16, 17], -1)]

def node5908Raw : WordRow := multiplyRow 2 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5908_check :
    collect (scaleRow 1 node5908Raw ++ scaleRow (-(2 : ℤ)) node5908 ++
      (scaleRow (-1) node5836)) = [] := by
  decide +kernel

theorem node5908_mem : rowEval varIndex node5908 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5908Raw node5908 (scaleRow (-1) node5836)
    (1) (2) (by decide) node5908_check
  · rw [node5908Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5836 node5836_mem)

def node5910 : WordRow := [([5, 12, 16, 17], 1)]

def node5910Raw : WordRow := multiplyRow 4 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5910_check :
    collect (scaleRow 1 node5910Raw ++ scaleRow (-(-4 : ℤ)) node5910 ++
      (scaleRow (-1) node5855 ++ scaleRow (-2) node4417)) = [] := by
  decide +kernel

theorem node5910_mem : rowEval varIndex node5910 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5910Raw node5910 (scaleRow (-1) node5855 ++ scaleRow (-2) node4417)
    (1) (-4) (by decide) node5910_check
  · rw [node5910Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5855 node5855_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4417 node4417_mem))

def node5911 : WordRow := [([7, 12, 16, 17], 1)]

def node5911Raw : WordRow := multiplyRow 6 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5911_check :
    collect (scaleRow 1 node5911Raw ++ scaleRow (-(-4 : ℤ)) node5911 ++
      (scaleRow (-1) node5874 ++ scaleRow (-2) node4572)) = [] := by
  decide +kernel

theorem node5911_mem : rowEval varIndex node5911 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5911Raw node5911 (scaleRow (-1) node5874 ++ scaleRow (-2) node4572)
    (1) (-4) (by decide) node5911_check
  · rw [node5911Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5874 node5874_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4572 node4572_mem))

def node5912 : WordRow := [([8, 13, 16, 17], 1), ([9, 12, 16, 17], -1)]

def node5912Raw : WordRow := multiplyRow 8 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5912_check :
    collect (scaleRow 1 node5912Raw ++ scaleRow (-(2 : ℤ)) node5912 ++
      (scaleRow (-1) node5889)) = [] := by
  decide +kernel

theorem node5912_mem : rowEval varIndex node5912 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5912Raw node5912 (scaleRow (-1) node5889)
    (1) (2) (by decide) node5912_check
  · rw [node5912Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5889 node5889_mem)

def node5914 : WordRow := [([10, 13, 16, 17], 1), ([11, 12, 16, 17], -1)]

def node5914Raw : WordRow := multiplyRow 10 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5914_check :
    collect (scaleRow 1 node5914Raw ++ scaleRow (-(2 : ℤ)) node5914 ++
      (scaleRow (-1) node5902)) = [] := by
  decide +kernel

theorem node5914_mem : rowEval varIndex node5914 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5914Raw node5914 (scaleRow (-1) node5902)
    (1) (2) (by decide) node5914_check
  · rw [node5914Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5902 node5902_mem)

def node5917 : WordRow := [([12, 14, 17, 17], 1), ([13, 14, 16, 17], 2)]

def node5917Raw : WordRow := multiplyRow 14 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5917_check :
    collect (scaleRow 1 node5917Raw ++ scaleRow (-(1 : ℤ)) node5917 ++
      ([])) = [] := by
  decide +kernel

theorem node5917_mem : rowEval varIndex node5917 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5917Raw node5917 ([])
    (1) (1) (by decide) node5917_check
  · rw [node5917Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · exact candidateIdeal.zero_mem

def node5919 : WordRow := [([13, 16, 16, 17], 1)]

def node5919Raw : WordRow := multiplyRow 16 node0788

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5919_check :
    collect (scaleRow 1 node5919Raw ++ scaleRow (-(2 : ℤ)) node5919 ++
      (scaleRow (-1) node5752)) = [] := by
  decide +kernel

theorem node5919_mem : rowEval varIndex node5919 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5919Raw node5919 (scaleRow (-1) node5752)
    (1) (2) (by decide) node5919_check
  · rw [node5919Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0788_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5752 node5752_mem)

def node5920 : WordRow := [([1, 14, 16, 17], 2), ([2, 13, 16, 17], -1), ([3, 12, 16, 17], -1), ([4, 11, 16, 17], -1), ([5, 10, 16, 17], -1), ([6, 9, 16, 17], -1), ([7, 8, 16, 17], -1)]

def node5920Raw : WordRow := multiplyRow 0 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5920_check :
    collect (scaleRow 1 node5920Raw ++ scaleRow (-(-2 : ℤ)) node5920 ++
      (scaleRow (-1) node5815 ++ scaleRow (-2) node4067)) = [] := by
  decide +kernel

theorem node5920_mem : rowEval varIndex node5920 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5920Raw node5920 (scaleRow (-1) node5815 ++ scaleRow (-2) node4067)
    (1) (-2) (by decide) node5920_check
  · rw [node5920Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5815 node5815_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4067 node4067_mem))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node5920_mem
