import VOA.DeligneAudit.D4FusionContactM2Dag05

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0782 : WordRow := [([6, 17, 17], 1), ([7, 16, 17], 2)]

def node0782Raw : WordRow := differentiateRow (images 26) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0782_check :
    collect (scaleRow 1 node0782Raw ++ scaleRow (-(1 : ℤ)) node0782 ++
      ([])) = [] := by
  decide +kernel

theorem node0782_mem : rowEval varIndex node0782 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0782Raw node0782 ([])
    (1) (1) (by decide) node0782_check
  · rw [node0782Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0783 : WordRow := [([7, 17, 17], 1)]

def node0783Raw : WordRow := differentiateRow (images 27) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0783_check :
    collect (scaleRow 1 node0783Raw ++ scaleRow (-(1 : ℤ)) node0783 ++
      ([])) = [] := by
  decide +kernel

theorem node0783_mem : rowEval varIndex node0783 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0783Raw node0783 ([])
    (1) (1) (by decide) node0783_check
  · rw [node0783Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0784 : WordRow := [([8, 17, 17], 1), ([9, 16, 17], 2)]

def node0784Raw : WordRow := differentiateRow (images 28) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0784_check :
    collect (scaleRow 1 node0784Raw ++ scaleRow (-(1 : ℤ)) node0784 ++
      ([])) = [] := by
  decide +kernel

theorem node0784_mem : rowEval varIndex node0784 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0784Raw node0784 ([])
    (1) (1) (by decide) node0784_check
  · rw [node0784Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0785 : WordRow := [([9, 17, 17], 1)]

def node0785Raw : WordRow := differentiateRow (images 29) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0785_check :
    collect (scaleRow 1 node0785Raw ++ scaleRow (-(1 : ℤ)) node0785 ++
      ([])) = [] := by
  decide +kernel

theorem node0785_mem : rowEval varIndex node0785 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0785Raw node0785 ([])
    (1) (1) (by decide) node0785_check
  · rw [node0785Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0786 : WordRow := [([10, 17, 17], 1), ([11, 16, 17], 2)]

def node0786Raw : WordRow := differentiateRow (images 30) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0786_check :
    collect (scaleRow 1 node0786Raw ++ scaleRow (-(1 : ℤ)) node0786 ++
      ([])) = [] := by
  decide +kernel

theorem node0786_mem : rowEval varIndex node0786 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0786Raw node0786 ([])
    (1) (1) (by decide) node0786_check
  · rw [node0786Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0787 : WordRow := [([11, 17, 17], 1)]

def node0787Raw : WordRow := differentiateRow (images 31) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0787_check :
    collect (scaleRow 1 node0787Raw ++ scaleRow (-(1 : ℤ)) node0787 ++
      ([])) = [] := by
  decide +kernel

theorem node0787_mem : rowEval varIndex node0787 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0787Raw node0787 ([])
    (1) (1) (by decide) node0787_check
  · rw [node0787Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0788 : WordRow := [([12, 17, 17], 1), ([13, 16, 17], 2)]

def node0788Raw : WordRow := differentiateRow (images 32) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0788_check :
    collect (scaleRow 1 node0788Raw ++ scaleRow (-(1 : ℤ)) node0788 ++
      ([])) = [] := by
  decide +kernel

theorem node0788_mem : rowEval varIndex node0788 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0788Raw node0788 ([])
    (1) (1) (by decide) node0788_check
  · rw [node0788Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0789 : WordRow := [([13, 17, 17], 1)]

def node0789Raw : WordRow := differentiateRow (images 33) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0789_check :
    collect (scaleRow 1 node0789Raw ++ scaleRow (-(1 : ℤ)) node0789 ++
      ([])) = [] := by
  decide +kernel

theorem node0789_mem : rowEval varIndex node0789 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0789Raw node0789 ([])
    (1) (1) (by decide) node0789_check
  · rw [node0789Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0790 : WordRow := [([14, 17, 17], 1), ([15, 16, 17], 2)]

def node0790Raw : WordRow := differentiateRow (images 34) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0790_check :
    collect (scaleRow 1 node0790Raw ++ scaleRow (-(1 : ℤ)) node0790 ++
      ([])) = [] := by
  decide +kernel

theorem node0790_mem : rowEval varIndex node0790 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0790Raw node0790 ([])
    (1) (1) (by decide) node0790_check
  · rw [node0790Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0791 : WordRow := [([15, 17, 17], 1)]

def node0791Raw : WordRow := differentiateRow (images 35) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0791_check :
    collect (scaleRow 1 node0791Raw ++ scaleRow (-(1 : ℤ)) node0791 ++
      ([])) = [] := by
  decide +kernel

theorem node0791_mem : rowEval varIndex node0791 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0791Raw node0791 ([])
    (1) (1) (by decide) node0791_check
  · rw [node0791Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0792 : WordRow := [([0, 2, 2], 1)]

def node0792Raw : WordRow := differentiateRow (images 14) node0773

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0792_check :
    collect (scaleRow 1 node0792Raw ++ scaleRow (-(2 : ℤ)) node0792 ++
      ([])) = [] := by
  decide +kernel

theorem node0792_mem : rowEval varIndex node0792 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0792Raw node0792 ([])
    (1) (2) (by decide) node0792_check
  · rw [node0792Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0773_mem
  · exact candidateIdeal.zero_mem

def node0793 : WordRow := [([0, 0, 8], 1), ([0, 2, 4], -2)]

def node0793Raw : WordRow := differentiateRow (images 16) node0773

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0793_check :
    collect (scaleRow 1 node0793Raw ++ scaleRow (-(-1 : ℤ)) node0793 ++
      ([])) = [] := by
  decide +kernel

theorem node0793_mem : rowEval varIndex node0793 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0793Raw node0793 ([])
    (1) (-1) (by decide) node0793_check
  · rw [node0793Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0773_mem
  · exact candidateIdeal.zero_mem

def node0794 : WordRow := [([0, 0, 10], 1), ([0, 2, 6], -2)]

def node0794Raw : WordRow := differentiateRow (images 18) node0773

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0794_check :
    collect (scaleRow 1 node0794Raw ++ scaleRow (-(1 : ℤ)) node0794 ++
      ([])) = [] := by
  decide +kernel

theorem node0794_mem : rowEval varIndex node0794 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0794Raw node0794 ([])
    (1) (1) (by decide) node0794_check
  · rw [node0794Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0773_mem
  · exact candidateIdeal.zero_mem

def node0795 : WordRow := [([0, 4, 4], 1)]

def node0795Raw : WordRow := differentiateRow (images 16) node0774

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0795_check :
    collect (scaleRow 1 node0795Raw ++ scaleRow (-(2 : ℤ)) node0795 ++
      ([])) = [] := by
  decide +kernel

theorem node0795_mem : rowEval varIndex node0795 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0795Raw node0795 ([])
    (1) (2) (by decide) node0795_check
  · rw [node0795Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0774_mem
  · exact candidateIdeal.zero_mem

def node0796 : WordRow := [([0, 0, 12], 1), ([0, 4, 6], -2)]

def node0796Raw : WordRow := differentiateRow (images 18) node0774

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0796_check :
    collect (scaleRow 1 node0796Raw ++ scaleRow (-(1 : ℤ)) node0796 ++
      ([])) = [] := by
  decide +kernel

theorem node0796_mem : rowEval varIndex node0796 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0796Raw node0796 ([])
    (1) (1) (by decide) node0796_check
  · rw [node0796Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0774_mem
  · exact candidateIdeal.zero_mem

def node0797 : WordRow := [([0, 6, 6], 1)]

def node0797Raw : WordRow := differentiateRow (images 18) node0775

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0797_check :
    collect (scaleRow 1 node0797Raw ++ scaleRow (-(-2 : ℤ)) node0797 ++
      ([])) = [] := by
  decide +kernel

theorem node0797_mem : rowEval varIndex node0797 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0797Raw node0797 ([])
    (1) (-2) (by decide) node0797_check
  · rw [node0797Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0775_mem
  · exact candidateIdeal.zero_mem

def node0798 : WordRow := [([2, 5, 17], 1), ([3, 4, 17], 1), ([3, 5, 16], 1)]

def node0798Raw : WordRow := differentiateRow (images 28) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0798_check :
    collect (scaleRow 1 node0798Raw ++ scaleRow (-(2 : ℤ)) node0798 ++
      (scaleRow (-2) node0230 ++ scaleRow (-2) node0243)) = [] := by
  decide +kernel

theorem node0798_mem : rowEval varIndex node0798 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0798Raw node0798 (scaleRow (-2) node0230 ++ scaleRow (-2) node0243)
    (1) (2) (by decide) node0798_check
  · rw [node0798Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0230 node0230_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0243 node0243_mem))

def node0799 : WordRow := [([3, 5, 17], 1)]

def node0799Raw : WordRow := differentiateRow (images 29) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0799_check :
    collect (scaleRow 1 node0799Raw ++ scaleRow (-(2 : ℤ)) node0799 ++
      (scaleRow (-2) node0244)) = [] := by
  decide +kernel

theorem node0799_mem : rowEval varIndex node0799 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0799Raw node0799 (scaleRow (-2) node0244)
    (1) (2) (by decide) node0799_check
  · rw [node0799Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0244 node0244_mem)

def node0800 : WordRow := [([2, 7, 17], 1), ([3, 6, 17], 1), ([3, 7, 16], 1)]

def node0800Raw : WordRow := differentiateRow (images 30) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0800_check :
    collect (scaleRow 1 node0800Raw ++ scaleRow (-(2 : ℤ)) node0800 ++
      (scaleRow (-2) node0261 ++ scaleRow (-2) node0272)) = [] := by
  decide +kernel

theorem node0800_mem : rowEval varIndex node0800 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0800Raw node0800 (scaleRow (-2) node0261 ++ scaleRow (-2) node0272)
    (1) (2) (by decide) node0800_check
  · rw [node0800Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0261 node0261_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0272 node0272_mem))

def node0801 : WordRow := [([3, 7, 17], 1)]

def node0801Raw : WordRow := differentiateRow (images 31) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0801_check :
    collect (scaleRow 1 node0801Raw ++ scaleRow (-(2 : ℤ)) node0801 ++
      (scaleRow (-2) node0273)) = [] := by
  decide +kernel

theorem node0801_mem : rowEval varIndex node0801 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0801Raw node0801 (scaleRow (-2) node0273)
    (1) (2) (by decide) node0801_check
  · rw [node0801Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0273 node0273_mem)

def node0802 : WordRow := [([4, 7, 17], 1), ([5, 6, 17], 1), ([5, 7, 16], 1)]

def node0802Raw : WordRow := differentiateRow (images 32) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0802_check :
    collect (scaleRow 1 node0802Raw ++ scaleRow (-(2 : ℤ)) node0802 ++
      (scaleRow (-2) node0320 ++ scaleRow (-2) node0331)) = [] := by
  decide +kernel

theorem node0802_mem : rowEval varIndex node0802 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0802Raw node0802 (scaleRow (-2) node0320 ++ scaleRow (-2) node0331)
    (1) (2) (by decide) node0802_check
  · rw [node0802Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0320 node0320_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0331 node0331_mem))

def node0803 : WordRow := [([5, 7, 17], 1)]

def node0803Raw : WordRow := differentiateRow (images 33) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0803_check :
    collect (scaleRow 1 node0803Raw ++ scaleRow (-(2 : ℤ)) node0803 ++
      (scaleRow (-2) node0332)) = [] := by
  decide +kernel

theorem node0803_mem : rowEval varIndex node0803 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0803Raw node0803 (scaleRow (-2) node0332)
    (1) (2) (by decide) node0803_check
  · rw [node0803Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0332 node0332_mem)

def node0804 : WordRow := [([2, 13, 17], 1), ([3, 12, 17], 1), ([3, 13, 16], 1), ([4, 11, 17], 1), ([5, 10, 17], 1), ([5, 11, 16], 1), ([6, 9, 17], 1), ([7, 8, 17], 1), ([7, 9, 16], 1)]

def node0804Raw : WordRow := differentiateRow (images 34) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0804_check :
    collect (scaleRow 1 node0804Raw ++ scaleRow (-(2 : ℤ)) node0804 ++
      (scaleRow (-2) node0461 ++ scaleRow (-2) node0472)) = [] := by
  decide +kernel

theorem node0804_mem : rowEval varIndex node0804 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0804Raw node0804 (scaleRow (-2) node0461 ++ scaleRow (-2) node0472)
    (1) (2) (by decide) node0804_check
  · rw [node0804Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0461 node0461_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0472 node0472_mem))

def node0805 : WordRow := [([3, 13, 17], 1), ([5, 11, 17], 1), ([7, 9, 17], 1)]

def node0805Raw : WordRow := differentiateRow (images 35) node0776

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0805_check :
    collect (scaleRow 1 node0805Raw ++ scaleRow (-(2 : ℤ)) node0805 ++
      (scaleRow (-2) node0473)) = [] := by
  decide +kernel

theorem node0805_mem : rowEval varIndex node0805 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0805Raw node0805 (scaleRow (-2) node0473)
    (1) (2) (by decide) node0805_check
  · rw [node0805Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0776_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0473 node0473_mem)

def node0806 : WordRow := [([4, 11, 17], 1), ([5, 10, 17], 1), ([5, 11, 16], 1), ([6, 9, 17], 1), ([7, 8, 17], 1), ([7, 9, 16], 1)]

def node0806Raw : WordRow := differentiateRow (images 32) node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0806_check :
    collect (scaleRow 1 node0806Raw ++ scaleRow (-(-2 : ℤ)) node0806 ++
      (scaleRow (-2) node0804)) = [] := by
  decide +kernel

theorem node0806_mem : rowEval varIndex node0806 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0806Raw node0806 (scaleRow (-2) node0804)
    (1) (-2) (by decide) node0806_check
  · rw [node0806Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0804 node0804_mem)

def node0807 : WordRow := [([5, 11, 17], 1), ([7, 9, 17], 1)]

def node0807Raw : WordRow := differentiateRow (images 33) node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0807_check :
    collect (scaleRow 1 node0807Raw ++ scaleRow (-(-2 : ℤ)) node0807 ++
      (scaleRow (-2) node0805)) = [] := by
  decide +kernel

theorem node0807_mem : rowEval varIndex node0807 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0807Raw node0807 (scaleRow (-2) node0805)
    (1) (-2) (by decide) node0807_check
  · rw [node0807Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0805 node0805_mem)

def node0808 : WordRow := [([8, 11, 17], 1), ([9, 10, 17], 1), ([9, 11, 16], 1)]

def node0808Raw : WordRow := differentiateRow (images 34) node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0808_check :
    collect (scaleRow 1 node0808Raw ++ scaleRow (-(-2 : ℤ)) node0808 ++
      (scaleRow (-2) node0591 ++ scaleRow (-2) node0600)) = [] := by
  decide +kernel

theorem node0808_mem : rowEval varIndex node0808 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0808Raw node0808 (scaleRow (-2) node0591 ++ scaleRow (-2) node0600)
    (1) (-2) (by decide) node0808_check
  · rw [node0808Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0591 node0591_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0600 node0600_mem))

def node0809 : WordRow := [([9, 11, 17], 1)]

def node0809Raw : WordRow := differentiateRow (images 35) node0778

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0809_check :
    collect (scaleRow 1 node0809Raw ++ scaleRow (-(-2 : ℤ)) node0809 ++
      (scaleRow (-2) node0601)) = [] := by
  decide +kernel

theorem node0809_mem : rowEval varIndex node0809 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0809Raw node0809 (scaleRow (-2) node0601)
    (1) (-2) (by decide) node0809_check
  · rw [node0809Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0778_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0601 node0601_mem)

def node0810 : WordRow := [([6, 9, 17], 1), ([7, 8, 17], 1), ([7, 9, 16], 1)]

def node0810Raw : WordRow := differentiateRow (images 30) node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0810_check :
    collect (scaleRow 1 node0810Raw ++ scaleRow (-(-2 : ℤ)) node0810 ++
      (scaleRow (-2) node0806)) = [] := by
  decide +kernel

theorem node0810_mem : rowEval varIndex node0810 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0810Raw node0810 (scaleRow (-2) node0806)
    (1) (-2) (by decide) node0810_check
  · rw [node0810Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0806 node0806_mem)

def node0811 : WordRow := [([7, 9, 17], 1)]

def node0811Raw : WordRow := differentiateRow (images 31) node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0811_check :
    collect (scaleRow 1 node0811Raw ++ scaleRow (-(-2 : ℤ)) node0811 ++
      (scaleRow (-2) node0807)) = [] := by
  decide +kernel

theorem node0811_mem : rowEval varIndex node0811 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0811Raw node0811 (scaleRow (-2) node0807)
    (1) (-2) (by decide) node0811_check
  · rw [node0811Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0807 node0807_mem)

def node0812 : WordRow := [([8, 13, 17], 1), ([9, 12, 17], 1), ([9, 13, 16], 1)]

def node0812Raw : WordRow := differentiateRow (images 34) node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0812_check :
    collect (scaleRow 1 node0812Raw ++ scaleRow (-(-2 : ℤ)) node0812 ++
      (scaleRow (-2) node0639 ++ scaleRow (-2) node0648)) = [] := by
  decide +kernel

theorem node0812_mem : rowEval varIndex node0812 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0812Raw node0812 (scaleRow (-2) node0639 ++ scaleRow (-2) node0648)
    (1) (-2) (by decide) node0812_check
  · rw [node0812Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0639 node0639_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0648 node0648_mem))

def node0813 : WordRow := [([9, 13, 17], 1)]

def node0813Raw : WordRow := differentiateRow (images 35) node0780

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0813_check :
    collect (scaleRow 1 node0813Raw ++ scaleRow (-(-2 : ℤ)) node0813 ++
      (scaleRow (-2) node0649)) = [] := by
  decide +kernel

theorem node0813_mem : rowEval varIndex node0813 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0813Raw node0813 (scaleRow (-2) node0649)
    (1) (-2) (by decide) node0813_check
  · rw [node0813Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0780_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0649 node0649_mem)

def node0814 : WordRow := [([10, 13, 17], 1), ([11, 12, 17], 1), ([11, 13, 16], 1)]

def node0814Raw : WordRow := differentiateRow (images 34) node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0814_check :
    collect (scaleRow 1 node0814Raw ++ scaleRow (-(-2 : ℤ)) node0814 ++
      (scaleRow (-2) node0665 ++ scaleRow (-2) node0672)) = [] := by
  decide +kernel

theorem node0814_mem : rowEval varIndex node0814 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0814Raw node0814 (scaleRow (-2) node0665 ++ scaleRow (-2) node0672)
    (1) (-2) (by decide) node0814_check
  · rw [node0814Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node0665 node0665_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node0672 node0672_mem))

def node0815 : WordRow := [([11, 13, 17], 1)]

def node0815Raw : WordRow := differentiateRow (images 35) node0782

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0815_check :
    collect (scaleRow 1 node0815Raw ++ scaleRow (-(-2 : ℤ)) node0815 ++
      (scaleRow (-2) node0673)) = [] := by
  decide +kernel

theorem node0815_mem : rowEval varIndex node0815 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0815Raw node0815 (scaleRow (-2) node0673)
    (1) (-2) (by decide) node0815_check
  · rw [node0815Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0782_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-2) node0673 node0673_mem)

def node0816 : WordRow := [([2, 2, 2], 1)]

def node0816Raw : WordRow := differentiateRow (images 14) node0792

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0816_check :
    collect (scaleRow 1 node0816Raw ++ scaleRow (-(1 : ℤ)) node0816 ++
      ([])) = [] := by
  decide +kernel

theorem node0816_mem : rowEval varIndex node0816 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0816Raw node0816 ([])
    (1) (1) (by decide) node0816_check
  · rw [node0816Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0792_mem
  · exact candidateIdeal.zero_mem

def node0817 : WordRow := [([0, 2, 8], 2), ([2, 2, 4], -1)]

def node0817Raw : WordRow := differentiateRow (images 16) node0792

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0817_check :
    collect (scaleRow 1 node0817Raw ++ scaleRow (-(-1 : ℤ)) node0817 ++
      ([])) = [] := by
  decide +kernel

theorem node0817_mem : rowEval varIndex node0817 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0817Raw node0817 ([])
    (1) (-1) (by decide) node0817_check
  · rw [node0817Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0792_mem
  · exact candidateIdeal.zero_mem

def node0818 : WordRow := [([0, 2, 10], 2), ([2, 2, 6], -1)]

def node0818Raw : WordRow := differentiateRow (images 18) node0792

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0818_check :
    collect (scaleRow 1 node0818Raw ++ scaleRow (-(1 : ℤ)) node0818 ++
      ([])) = [] := by
  decide +kernel

theorem node0818_mem : rowEval varIndex node0818 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0818Raw node0818 ([])
    (1) (1) (by decide) node0818_check
  · rw [node0818Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0792_mem
  · exact candidateIdeal.zero_mem

def node0819 : WordRow := [([0, 4, 8], 2), ([2, 4, 4], -1)]

def node0819Raw : WordRow := differentiateRow (images 16) node0793

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0819_check :
    collect (scaleRow 1 node0819Raw ++ scaleRow (-(2 : ℤ)) node0819 ++
      ([])) = [] := by
  decide +kernel

theorem node0819_mem : rowEval varIndex node0819 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0819Raw node0819 ([])
    (1) (2) (by decide) node0819_check
  · rw [node0819Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0793_mem
  · exact candidateIdeal.zero_mem

def node0820 : WordRow := [([0, 0, 14], 1), ([0, 2, 12], -2), ([0, 4, 10], -2), ([0, 6, 8], -2), ([2, 4, 6], 2)]

def node0820Raw : WordRow := differentiateRow (images 18) node0793

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0820_check :
    collect (scaleRow 1 node0820Raw ++ scaleRow (-(1 : ℤ)) node0820 ++
      ([])) = [] := by
  decide +kernel

theorem node0820_mem : rowEval varIndex node0820 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0820Raw node0820 ([])
    (1) (1) (by decide) node0820_check
  · rw [node0820Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0793_mem
  · exact candidateIdeal.zero_mem

def node0821 : WordRow := [([0, 6, 10], 2), ([2, 6, 6], -1)]

def node0821Raw : WordRow := differentiateRow (images 18) node0794

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0821_check :
    collect (scaleRow 1 node0821Raw ++ scaleRow (-(-2 : ℤ)) node0821 ++
      ([])) = [] := by
  decide +kernel

theorem node0821_mem : rowEval varIndex node0821 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0821Raw node0821 ([])
    (1) (-2) (by decide) node0821_check
  · rw [node0821Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0794_mem
  · exact candidateIdeal.zero_mem

def node0822 : WordRow := [([4, 4, 4], 1)]

def node0822Raw : WordRow := differentiateRow (images 16) node0795

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0822_check :
    collect (scaleRow 1 node0822Raw ++ scaleRow (-(1 : ℤ)) node0822 ++
      ([])) = [] := by
  decide +kernel

theorem node0822_mem : rowEval varIndex node0822 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0822Raw node0822 ([])
    (1) (1) (by decide) node0822_check
  · rw [node0822Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0795_mem
  · exact candidateIdeal.zero_mem

def node0823 : WordRow := [([0, 4, 12], 2), ([4, 4, 6], -1)]

def node0823Raw : WordRow := differentiateRow (images 18) node0795

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0823_check :
    collect (scaleRow 1 node0823Raw ++ scaleRow (-(1 : ℤ)) node0823 ++
      ([])) = [] := by
  decide +kernel

theorem node0823_mem : rowEval varIndex node0823 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0823Raw node0823 ([])
    (1) (1) (by decide) node0823_check
  · rw [node0823Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0795_mem
  · exact candidateIdeal.zero_mem

def node0824 : WordRow := [([0, 6, 12], 2), ([4, 6, 6], -1)]

def node0824Raw : WordRow := differentiateRow (images 18) node0796

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0824_check :
    collect (scaleRow 1 node0824Raw ++ scaleRow (-(-2 : ℤ)) node0824 ++
      ([])) = [] := by
  decide +kernel

theorem node0824_mem : rowEval varIndex node0824 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0824Raw node0824 ([])
    (1) (-2) (by decide) node0824_check
  · rw [node0824Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0796_mem
  · exact candidateIdeal.zero_mem

def node0825 : WordRow := [([6, 6, 6], 1)]

def node0825Raw : WordRow := differentiateRow (images 18) node0797

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0825_check :
    collect (scaleRow 1 node0825Raw ++ scaleRow (-(-1 : ℤ)) node0825 ++
      ([])) = [] := by
  decide +kernel

theorem node0825_mem : rowEval varIndex node0825 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0825Raw node0825 ([])
    (1) (-1) (by decide) node0825_check
  · rw [node0825Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0797_mem
  · exact candidateIdeal.zero_mem

def node0826 : WordRow := [([2, 2, 8], 1)]

def node0826Raw : WordRow := differentiateRow (images 16) node0816

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0826_check :
    collect (scaleRow 1 node0826Raw ++ scaleRow (-(-3 : ℤ)) node0826 ++
      ([])) = [] := by
  decide +kernel

theorem node0826_mem : rowEval varIndex node0826 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0826Raw node0826 ([])
    (1) (-3) (by decide) node0826_check
  · rw [node0826Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0816_mem
  · exact candidateIdeal.zero_mem

def node0827 : WordRow := [([2, 2, 10], 1)]

def node0827Raw : WordRow := differentiateRow (images 18) node0816

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0827_check :
    collect (scaleRow 1 node0827Raw ++ scaleRow (-(3 : ℤ)) node0827 ++
      ([])) = [] := by
  decide +kernel

theorem node0827_mem : rowEval varIndex node0827 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0827Raw node0827 ([])
    (1) (3) (by decide) node0827_check
  · rw [node0827Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0816_mem
  · exact candidateIdeal.zero_mem

def node0828 : WordRow := [([0, 8, 8], 1), ([2, 4, 8], -2)]

def node0828Raw : WordRow := differentiateRow (images 16) node0817

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0828_check :
    collect (scaleRow 1 node0828Raw ++ scaleRow (-(-2 : ℤ)) node0828 ++
      ([])) = [] := by
  decide +kernel

theorem node0828_mem : rowEval varIndex node0828 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0828Raw node0828 ([])
    (1) (-2) (by decide) node0828_check
  · rw [node0828Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0817_mem
  · exact candidateIdeal.zero_mem

def node0829 : WordRow := [([0, 2, 14], 2), ([0, 8, 10], 2), ([2, 2, 12], -1), ([2, 4, 10], -2), ([2, 6, 8], -2)]

def node0829Raw : WordRow := differentiateRow (images 18) node0817

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0829_check :
    collect (scaleRow 1 node0829Raw ++ scaleRow (-(1 : ℤ)) node0829 ++
      ([])) = [] := by
  decide +kernel

theorem node0829_mem : rowEval varIndex node0829 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0829Raw node0829 ([])
    (1) (1) (by decide) node0829_check
  · rw [node0829Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0817_mem
  · exact candidateIdeal.zero_mem

def node0830 : WordRow := [([0, 10, 10], 1), ([2, 6, 10], -2)]

def node0830Raw : WordRow := differentiateRow (images 18) node0818

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0830_check :
    collect (scaleRow 1 node0830Raw ++ scaleRow (-(2 : ℤ)) node0830 ++
      ([])) = [] := by
  decide +kernel

theorem node0830_mem : rowEval varIndex node0830 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0830Raw node0830 ([])
    (1) (2) (by decide) node0830_check
  · rw [node0830Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0818_mem
  · exact candidateIdeal.zero_mem

def node0831 : WordRow := [([4, 4, 8], 1)]

def node0831Raw : WordRow := differentiateRow (images 16) node0819

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0831_check :
    collect (scaleRow 1 node0831Raw ++ scaleRow (-(3 : ℤ)) node0831 ++
      ([])) = [] := by
  decide +kernel

theorem node0831_mem : rowEval varIndex node0831 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0831Raw node0831 ([])
    (1) (3) (by decide) node0831_check
  · rw [node0831Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0819_mem
  · exact candidateIdeal.zero_mem

def node0832 : WordRow := [([0, 4, 14], 2), ([0, 8, 12], 2), ([2, 4, 12], -2), ([4, 4, 10], -1), ([4, 6, 8], -2)]

def node0832Raw : WordRow := differentiateRow (images 18) node0819

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0832_check :
    collect (scaleRow 1 node0832Raw ++ scaleRow (-(1 : ℤ)) node0832 ++
      ([])) = [] := by
  decide +kernel

theorem node0832_mem : rowEval varIndex node0832 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0832Raw node0832 ([])
    (1) (1) (by decide) node0832_check
  · rw [node0832Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0819_mem
  · exact candidateIdeal.zero_mem

def node0833 : WordRow := [([0, 6, 14], 2), ([0, 10, 12], 2), ([2, 6, 12], -2), ([4, 6, 10], -2), ([6, 6, 8], -1)]

def node0833Raw : WordRow := differentiateRow (images 18) node0820

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0833_check :
    collect (scaleRow 1 node0833Raw ++ scaleRow (-(-2 : ℤ)) node0833 ++
      ([])) = [] := by
  decide +kernel

theorem node0833_mem : rowEval varIndex node0833 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0833Raw node0833 ([])
    (1) (-2) (by decide) node0833_check
  · rw [node0833Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0820_mem
  · exact candidateIdeal.zero_mem

def node0834 : WordRow := [([6, 6, 10], 1)]

def node0834Raw : WordRow := differentiateRow (images 18) node0821

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0834_check :
    collect (scaleRow 1 node0834Raw ++ scaleRow (-(-3 : ℤ)) node0834 ++
      ([])) = [] := by
  decide +kernel

theorem node0834_mem : rowEval varIndex node0834 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0834Raw node0834 ([])
    (1) (-3) (by decide) node0834_check
  · rw [node0834Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0821_mem
  · exact candidateIdeal.zero_mem

def node0835 : WordRow := [([4, 4, 12], 1)]

def node0835Raw : WordRow := differentiateRow (images 18) node0822

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0835_check :
    collect (scaleRow 1 node0835Raw ++ scaleRow (-(3 : ℤ)) node0835 ++
      ([])) = [] := by
  decide +kernel

theorem node0835_mem : rowEval varIndex node0835 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0835Raw node0835 ([])
    (1) (3) (by decide) node0835_check
  · rw [node0835Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0822_mem
  · exact candidateIdeal.zero_mem

def node0836 : WordRow := [([0, 12, 12], 1), ([4, 6, 12], -2)]

def node0836Raw : WordRow := differentiateRow (images 18) node0823

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0836_check :
    collect (scaleRow 1 node0836Raw ++ scaleRow (-(2 : ℤ)) node0836 ++
      ([])) = [] := by
  decide +kernel

theorem node0836_mem : rowEval varIndex node0836 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0836Raw node0836 ([])
    (1) (2) (by decide) node0836_check
  · rw [node0836Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0823_mem
  · exact candidateIdeal.zero_mem

def node0837 : WordRow := [([6, 6, 12], 1)]

def node0837Raw : WordRow := differentiateRow (images 18) node0824

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0837_check :
    collect (scaleRow 1 node0837Raw ++ scaleRow (-(-3 : ℤ)) node0837 ++
      ([])) = [] := by
  decide +kernel

theorem node0837_mem : rowEval varIndex node0837 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0837Raw node0837 ([])
    (1) (-3) (by decide) node0837_check
  · rw [node0837Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0824_mem
  · exact candidateIdeal.zero_mem

def node0838 : WordRow := [([2, 8, 8], 1)]

def node0838Raw : WordRow := differentiateRow (images 16) node0826

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0838_check :
    collect (scaleRow 1 node0838Raw ++ scaleRow (-(-2 : ℤ)) node0838 ++
      ([])) = [] := by
  decide +kernel

theorem node0838_mem : rowEval varIndex node0838 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0838Raw node0838 ([])
    (1) (-2) (by decide) node0838_check
  · rw [node0838Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0826_mem
  · exact candidateIdeal.zero_mem

def node0839 : WordRow := [([2, 2, 14], 1), ([2, 8, 10], 2)]

def node0839Raw : WordRow := differentiateRow (images 18) node0826

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0839_check :
    collect (scaleRow 1 node0839Raw ++ scaleRow (-(1 : ℤ)) node0839 ++
      ([])) = [] := by
  decide +kernel

theorem node0839_mem : rowEval varIndex node0839 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0839Raw node0839 ([])
    (1) (1) (by decide) node0839_check
  · rw [node0839Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0826_mem
  · exact candidateIdeal.zero_mem

def node0840 : WordRow := [([2, 10, 10], 1)]

def node0840Raw : WordRow := differentiateRow (images 18) node0827

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0840_check :
    collect (scaleRow 1 node0840Raw ++ scaleRow (-(2 : ℤ)) node0840 ++
      ([])) = [] := by
  decide +kernel

theorem node0840_mem : rowEval varIndex node0840 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0840Raw node0840 ([])
    (1) (2) (by decide) node0840_check
  · rw [node0840Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0827_mem
  · exact candidateIdeal.zero_mem

def node0841 : WordRow := [([4, 8, 8], 1)]

def node0841Raw : WordRow := differentiateRow (images 16) node0828

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0841_check :
    collect (scaleRow 1 node0841Raw ++ scaleRow (-(3 : ℤ)) node0841 ++
      ([])) = [] := by
  decide +kernel

theorem node0841_mem : rowEval varIndex node0841 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0841Raw node0841 ([])
    (1) (3) (by decide) node0841_check
  · rw [node0841Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0828_mem
  · exact candidateIdeal.zero_mem

def node0842 : WordRow := [([0, 8, 14], 2), ([2, 4, 14], -2), ([2, 8, 12], -2), ([4, 8, 10], -2), ([6, 8, 8], -1)]

def node0842Raw : WordRow := differentiateRow (images 18) node0828

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0842_check :
    collect (scaleRow 1 node0842Raw ++ scaleRow (-(1 : ℤ)) node0842 ++
      ([])) = [] := by
  decide +kernel

theorem node0842_mem : rowEval varIndex node0842 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0842Raw node0842 ([])
    (1) (1) (by decide) node0842_check
  · rw [node0842Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0828_mem
  · exact candidateIdeal.zero_mem

def node0843 : WordRow := [([0, 10, 14], 2), ([2, 6, 14], -2), ([2, 10, 12], -2), ([4, 10, 10], -1), ([6, 8, 10], -2)]

def node0843Raw : WordRow := differentiateRow (images 18) node0829

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0843_check :
    collect (scaleRow 1 node0843Raw ++ scaleRow (-(2 : ℤ)) node0843 ++
      ([])) = [] := by
  decide +kernel

theorem node0843_mem : rowEval varIndex node0843 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0843Raw node0843 ([])
    (1) (2) (by decide) node0843_check
  · rw [node0843Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0829_mem
  · exact candidateIdeal.zero_mem

def node0844 : WordRow := [([6, 10, 10], 1)]

def node0844Raw : WordRow := differentiateRow (images 18) node0830

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0844_check :
    collect (scaleRow 1 node0844Raw ++ scaleRow (-(-3 : ℤ)) node0844 ++
      ([])) = [] := by
  decide +kernel

theorem node0844_mem : rowEval varIndex node0844 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0844Raw node0844 ([])
    (1) (-3) (by decide) node0844_check
  · rw [node0844Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0830_mem
  · exact candidateIdeal.zero_mem

def node0845 : WordRow := [([4, 4, 14], 1), ([4, 8, 12], 2)]

def node0845Raw : WordRow := differentiateRow (images 18) node0831

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0845_check :
    collect (scaleRow 1 node0845Raw ++ scaleRow (-(1 : ℤ)) node0845 ++
      ([])) = [] := by
  decide +kernel

theorem node0845_mem : rowEval varIndex node0845 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0845Raw node0845 ([])
    (1) (1) (by decide) node0845_check
  · rw [node0845Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0831_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0845_mem
