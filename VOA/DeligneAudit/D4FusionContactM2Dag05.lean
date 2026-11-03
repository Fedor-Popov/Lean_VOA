import VOA.DeligneAudit.D4FusionContactM2Dag04

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0667 : WordRow := [([7, 9, 15], 1), ([9, 11, 13], 1)]

def node0667Raw : WordRow := multiplyRow 9 node0043

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0667_check :
    collect (scaleRow 1 node0667Raw ++ scaleRow (-(1 : ℤ)) node0667 ++
      ([])) = [] := by
  decide +kernel

theorem node0667_mem : rowEval varIndex node0667 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0667Raw node0667 ([])
    (1) (1) (by decide) node0667_check
  · rw [node0667Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0043_mem
  · exact candidateIdeal.zero_mem

def node0672 : WordRow := [([7, 15, 16], 1), ([11, 13, 16], 1)]

def node0672Raw : WordRow := multiplyRow 16 node0043

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0672_check :
    collect (scaleRow 1 node0672Raw ++ scaleRow (-(1 : ℤ)) node0672 ++
      ([])) = [] := by
  decide +kernel

theorem node0672_mem : rowEval varIndex node0672 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0672Raw node0672 ([])
    (1) (1) (by decide) node0672_check
  · rw [node0672Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0043_mem
  · exact candidateIdeal.zero_mem

def node0673 : WordRow := [([7, 15, 17], 1), ([11, 13, 17], 1)]

def node0673Raw : WordRow := multiplyRow 17 node0043

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0673_check :
    collect (scaleRow 1 node0673Raw ++ scaleRow (-(1 : ℤ)) node0673 ++
      ([])) = [] := by
  decide +kernel

theorem node0673_mem : rowEval varIndex node0673 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0673Raw node0673 ([])
    (1) (1) (by decide) node0673_check
  · rw [node0673Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0043_mem
  · exact candidateIdeal.zero_mem

def node0674 : WordRow := [([1, 12, 12], 1), ([4, 7, 12], -1), ([5, 6, 12], -1)]

def node0674Raw : WordRow := multiplyRow 0 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0674_check :
    collect (scaleRow 1 node0674Raw ++ scaleRow (-(-1 : ℤ)) node0674 ++
      (scaleRow (-1) node0315)) = [] := by
  decide +kernel

theorem node0674_mem : rowEval varIndex node0674 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0674Raw node0674 (scaleRow (-1) node0315)
    (1) (-1) (by decide) node0674_check
  · rw [node0674Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0315 node0315_mem)

def node0675 : WordRow := [([2, 12, 13], 1)]

def node0675Raw : WordRow := multiplyRow 2 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0675_check :
    collect (scaleRow 1 node0675Raw ++ scaleRow (-(1 : ℤ)) node0675 ++
      ([])) = [] := by
  decide +kernel

theorem node0675_mem : rowEval varIndex node0675 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0675Raw node0675 ([])
    (1) (1) (by decide) node0675_check
  · rw [node0675Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · exact candidateIdeal.zero_mem

def node0676 : WordRow := [([3, 12, 13], 1)]

def node0676Raw : WordRow := multiplyRow 3 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0676_check :
    collect (scaleRow 1 node0676Raw ++ scaleRow (-(1 : ℤ)) node0676 ++
      ([])) = [] := by
  decide +kernel

theorem node0676_mem : rowEval varIndex node0676 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0676Raw node0676 ([])
    (1) (1) (by decide) node0676_check
  · rw [node0676Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · exact candidateIdeal.zero_mem

def node0677 : WordRow := [([5, 12, 12], 1)]

def node0677Raw : WordRow := multiplyRow 4 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0677_check :
    collect (scaleRow 1 node0677Raw ++ scaleRow (-(-1 : ℤ)) node0677 ++
      (scaleRow (-1) node0510)) = [] := by
  decide +kernel

theorem node0677_mem : rowEval varIndex node0677 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0677Raw node0677 (scaleRow (-1) node0510)
    (1) (-1) (by decide) node0677_check
  · rw [node0677Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0510 node0510_mem)

def node0678 : WordRow := [([7, 12, 12], 1)]

def node0678Raw : WordRow := multiplyRow 6 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0678_check :
    collect (scaleRow 1 node0678Raw ++ scaleRow (-(-1 : ℤ)) node0678 ++
      (scaleRow (-1) node0536)) = [] := by
  decide +kernel

theorem node0678_mem : rowEval varIndex node0678 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0678Raw node0678 (scaleRow (-1) node0536)
    (1) (-1) (by decide) node0678_check
  · rw [node0678Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0536 node0536_mem)

def node0679 : WordRow := [([8, 12, 13], 1)]

def node0679Raw : WordRow := multiplyRow 8 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0679_check :
    collect (scaleRow 1 node0679Raw ++ scaleRow (-(1 : ℤ)) node0679 ++
      ([])) = [] := by
  decide +kernel

theorem node0679_mem : rowEval varIndex node0679 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0679Raw node0679 ([])
    (1) (1) (by decide) node0679_check
  · rw [node0679Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · exact candidateIdeal.zero_mem

def node0681 : WordRow := [([10, 12, 13], 1)]

def node0681Raw : WordRow := multiplyRow 10 node0044

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0681_check :
    collect (scaleRow 1 node0681Raw ++ scaleRow (-(1 : ℤ)) node0681 ++
      ([])) = [] := by
  decide +kernel

theorem node0681_mem : rowEval varIndex node0681 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0681Raw node0681 ([])
    (1) (1) (by decide) node0681_check
  · rw [node0681Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0044_mem
  · exact candidateIdeal.zero_mem

def node0694 : WordRow := [([1, 8, 14], 2), ([2, 5, 14], -1), ([2, 8, 13], -1), ([3, 4, 14], -1), ([3, 8, 12], -1), ([4, 8, 11], -1), ([5, 8, 10], -1), ([6, 8, 9], -1), ([7, 8, 8], -1)]

def node0694Raw : WordRow := multiplyRow 0 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0694_check :
    collect (scaleRow 1 node0694Raw ++ scaleRow (-(-1 : ℤ)) node0694 ++
      (scaleRow (-1) node0452 ++ scaleRow (-1) node0227)) = [] := by
  decide +kernel

theorem node0694_mem : rowEval varIndex node0694 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0694Raw node0694 (scaleRow (-1) node0452 ++ scaleRow (-1) node0227)
    (1) (-1) (by decide) node0694_check
  · rw [node0694Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0452 node0452_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0227 node0227_mem))

def node0695 : WordRow := [([3, 8, 14], 2), ([8, 8, 11], 1), ([8, 9, 10], 1)]

def node0695Raw : WordRow := multiplyRow 2 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0695_check :
    collect (scaleRow 1 node0695Raw ++ scaleRow (-(-1 : ℤ)) node0695 ++
      (scaleRow (-1) node0582 ++ scaleRow (-1) node0373)) = [] := by
  decide +kernel

theorem node0695_mem : rowEval varIndex node0695 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0695Raw node0695 (scaleRow (-1) node0582 ++ scaleRow (-1) node0373)
    (1) (-1) (by decide) node0695_check
  · rw [node0695Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0582 node0582_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0373 node0373_mem))

def node0696 : WordRow := [([5, 8, 14], 2), ([8, 8, 13], 1), ([8, 9, 12], 1)]

def node0696Raw : WordRow := multiplyRow 4 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0696_check :
    collect (scaleRow 1 node0696Raw ++ scaleRow (-(-1 : ℤ)) node0696 ++
      (scaleRow (-1) node0630 ++ scaleRow (-1) node0429)) = [] := by
  decide +kernel

theorem node0696_mem : rowEval varIndex node0696 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0696Raw node0696 (scaleRow (-1) node0630 ++ scaleRow (-1) node0429)
    (1) (-1) (by decide) node0696_check
  · rw [node0696Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0630 node0630_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0429 node0429_mem))

def node0697 : WordRow := [([6, 9, 14], 1), ([7, 8, 14], -1), ([8, 10, 13], -1), ([8, 11, 12], -1)]

def node0697Raw : WordRow := multiplyRow 6 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0697_check :
    collect (scaleRow 1 node0697Raw ++ scaleRow (-(1 : ℤ)) node0697 ++
      (scaleRow (-1) node0656)) = [] := by
  decide +kernel

theorem node0697_mem : rowEval varIndex node0697 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0697Raw node0697 (scaleRow (-1) node0656)
    (1) (1) (by decide) node0697_check
  · rw [node0697Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0656 node0656_mem)

def node0698 : WordRow := [([7, 9, 14], 1), ([8, 11, 13], -1)]

def node0698Raw : WordRow := multiplyRow 7 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0698_check :
    collect (scaleRow 1 node0698Raw ++ scaleRow (-(1 : ℤ)) node0698 ++
      (scaleRow (-1) node0666)) = [] := by
  decide +kernel

theorem node0698_mem : rowEval varIndex node0698 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0698Raw node0698 (scaleRow (-1) node0666)
    (1) (1) (by decide) node0698_check
  · rw [node0698Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0666 node0666_mem)

def node0700 : WordRow := [([8, 10, 15], 1), ([9, 10, 14], 1)]

def node0700Raw : WordRow := multiplyRow 10 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0700_check :
    collect (scaleRow 1 node0700Raw ++ scaleRow (-(1 : ℤ)) node0700 ++
      ([])) = [] := by
  decide +kernel

theorem node0700_mem : rowEval varIndex node0700 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0700Raw node0700 ([])
    (1) (1) (by decide) node0700_check
  · rw [node0700Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0702 : WordRow := [([8, 12, 15], 1), ([9, 12, 14], 1)]

def node0702Raw : WordRow := multiplyRow 12 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0702_check :
    collect (scaleRow 1 node0702Raw ++ scaleRow (-(1 : ℤ)) node0702 ++
      ([])) = [] := by
  decide +kernel

theorem node0702_mem : rowEval varIndex node0702 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0702Raw node0702 ([])
    (1) (1) (by decide) node0702_check
  · rw [node0702Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0704 : WordRow := [([8, 14, 15], 1), ([9, 14, 14], 1)]

def node0704Raw : WordRow := multiplyRow 14 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0704_check :
    collect (scaleRow 1 node0704Raw ++ scaleRow (-(1 : ℤ)) node0704 ++
      ([])) = [] := by
  decide +kernel

theorem node0704_mem : rowEval varIndex node0704 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0704Raw node0704 ([])
    (1) (1) (by decide) node0704_check
  · rw [node0704Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0706 : WordRow := [([8, 15, 16], 1), ([9, 14, 16], 1)]

def node0706Raw : WordRow := multiplyRow 16 node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0706_check :
    collect (scaleRow 1 node0706Raw ++ scaleRow (-(1 : ℤ)) node0706 ++
      ([])) = [] := by
  decide +kernel

theorem node0706_mem : rowEval varIndex node0706 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0706Raw node0706 ([])
    (1) (1) (by decide) node0706_check
  · rw [node0706Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0708 : WordRow := [([8, 11, 13], 1), ([9, 10, 13], 1), ([9, 11, 12], 1)]

def node0708Raw : WordRow := multiplyRow 6 node0047

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0708_check :
    collect (scaleRow 1 node0708Raw ++ scaleRow (-(-1 : ℤ)) node0708 ++
      (scaleRow (-1) node0657 ++ scaleRow (1) node0698)) = [] := by
  decide +kernel

theorem node0708_mem : rowEval varIndex node0708 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0708Raw node0708 (scaleRow (-1) node0657 ++ scaleRow (1) node0698)
    (1) (-1) (by decide) node0708_check
  · rw [node0708Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0047_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0657 node0657_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node0698 node0698_mem))

def node0709 : WordRow := [([9, 11, 13], 1)]

def node0709Raw : WordRow := multiplyRow 7 node0047

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0709_check :
    collect (scaleRow 1 node0709Raw ++ scaleRow (-(-1 : ℤ)) node0709 ++
      (scaleRow (-1) node0667)) = [] := by
  decide +kernel

theorem node0709_mem : rowEval varIndex node0709 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0709Raw node0709 (scaleRow (-1) node0667)
    (1) (-1) (by decide) node0709_check
  · rw [node0709Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0047_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0667 node0667_mem)

def node0710 : WordRow := [([9, 10, 15], 1)]

def node0710Raw : WordRow := multiplyRow 10 node0047

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0710_check :
    collect (scaleRow 1 node0710Raw ++ scaleRow (-(1 : ℤ)) node0710 ++
      ([])) = [] := by
  decide +kernel

theorem node0710_mem : rowEval varIndex node0710 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0710Raw node0710 ([])
    (1) (1) (by decide) node0710_check
  · rw [node0710Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0047_mem
  · exact candidateIdeal.zero_mem

def node0712 : WordRow := [([9, 12, 15], 1)]

def node0712Raw : WordRow := multiplyRow 12 node0047

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0712_check :
    collect (scaleRow 1 node0712Raw ++ scaleRow (-(1 : ℤ)) node0712 ++
      ([])) = [] := by
  decide +kernel

theorem node0712_mem : rowEval varIndex node0712 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0712Raw node0712 ([])
    (1) (1) (by decide) node0712_check
  · rw [node0712Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0047_mem
  · exact candidateIdeal.zero_mem

def node0718 : WordRow := [([1, 10, 14], 2), ([2, 7, 14], -1), ([2, 10, 13], -1), ([3, 6, 14], -1), ([3, 10, 12], -1), ([4, 10, 11], -1), ([5, 10, 10], -1), ([6, 9, 10], -1), ([7, 8, 10], -1)]

def node0718Raw : WordRow := multiplyRow 0 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0718_check :
    collect (scaleRow 1 node0718Raw ++ scaleRow (-(-1 : ℤ)) node0718 ++
      (scaleRow (-1) node0454 ++ scaleRow (-1) node0258)) = [] := by
  decide +kernel

theorem node0718_mem : rowEval varIndex node0718 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0718Raw node0718 (scaleRow (-1) node0454 ++ scaleRow (-1) node0258)
    (1) (-1) (by decide) node0718_check
  · rw [node0718Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0454 node0454_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0258 node0258_mem))

def node0719 : WordRow := [([3, 10, 14], 2), ([8, 10, 11], 1), ([9, 10, 10], 1)]

def node0719Raw : WordRow := multiplyRow 2 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0719_check :
    collect (scaleRow 1 node0719Raw ++ scaleRow (-(-1 : ℤ)) node0719 ++
      (scaleRow (-1) node0584 ++ scaleRow (-1) node0403)) = [] := by
  decide +kernel

theorem node0719_mem : rowEval varIndex node0719 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0719Raw node0719 (scaleRow (-1) node0584 ++ scaleRow (-1) node0403)
    (1) (-1) (by decide) node0719_check
  · rw [node0719Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0584 node0584_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0403 node0403_mem))

def node0720 : WordRow := [([4, 11, 14], 1), ([5, 10, 14], -1), ([8, 10, 13], -1), ([9, 10, 12], -1)]

def node0720Raw : WordRow := multiplyRow 4 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0720_check :
    collect (scaleRow 1 node0720Raw ++ scaleRow (-(1 : ℤ)) node0720 ++
      (scaleRow (-1) node0632)) = [] := by
  decide +kernel

theorem node0720_mem : rowEval varIndex node0720 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0720Raw node0720 (scaleRow (-1) node0632)
    (1) (1) (by decide) node0720_check
  · rw [node0720Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0632 node0632_mem)

def node0721 : WordRow := [([5, 11, 14], 1), ([9, 10, 13], -1)]

def node0721Raw : WordRow := multiplyRow 5 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0721_check :
    collect (scaleRow 1 node0721Raw ++ scaleRow (-(1 : ℤ)) node0721 ++
      (scaleRow (-1) node0642)) = [] := by
  decide +kernel

theorem node0721_mem : rowEval varIndex node0721 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0721Raw node0721 (scaleRow (-1) node0642)
    (1) (1) (by decide) node0721_check
  · rw [node0721Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0642 node0642_mem)

def node0722 : WordRow := [([7, 10, 14], 2), ([10, 10, 13], 1), ([10, 11, 12], 1)]

def node0722Raw : WordRow := multiplyRow 6 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0722_check :
    collect (scaleRow 1 node0722Raw ++ scaleRow (-(-1 : ℤ)) node0722 ++
      (scaleRow (-1) node0658 ++ scaleRow (-1) node0486)) = [] := by
  decide +kernel

theorem node0722_mem : rowEval varIndex node0722 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0722Raw node0722 (scaleRow (-1) node0658 ++ scaleRow (-1) node0486)
    (1) (-1) (by decide) node0722_check
  · rw [node0722Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0658 node0658_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0486 node0486_mem))

def node0723 : WordRow := [([8, 11, 14], 1), ([9, 10, 14], -1)]

def node0723Raw : WordRow := multiplyRow 8 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0723_check :
    collect (scaleRow 1 node0723Raw ++ scaleRow (-(1 : ℤ)) node0723 ++
      (scaleRow (-1) node0700)) = [] := by
  decide +kernel

theorem node0723_mem : rowEval varIndex node0723 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0723Raw node0723 (scaleRow (-1) node0700)
    (1) (1) (by decide) node0723_check
  · rw [node0723Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0700 node0700_mem)

def node0724 : WordRow := [([9, 11, 14], 1)]

def node0724Raw : WordRow := multiplyRow 9 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0724_check :
    collect (scaleRow 1 node0724Raw ++ scaleRow (-(1 : ℤ)) node0724 ++
      (scaleRow (-1) node0710)) = [] := by
  decide +kernel

theorem node0724_mem : rowEval varIndex node0724 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0724Raw node0724 (scaleRow (-1) node0710)
    (1) (1) (by decide) node0724_check
  · rw [node0724Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0710 node0710_mem)

def node0726 : WordRow := [([10, 12, 15], 1), ([11, 12, 14], 1)]

def node0726Raw : WordRow := multiplyRow 12 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0726_check :
    collect (scaleRow 1 node0726Raw ++ scaleRow (-(1 : ℤ)) node0726 ++
      ([])) = [] := by
  decide +kernel

theorem node0726_mem : rowEval varIndex node0726 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0726Raw node0726 ([])
    (1) (1) (by decide) node0726_check
  · rw [node0726Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · exact candidateIdeal.zero_mem

def node0728 : WordRow := [([10, 14, 15], 1), ([11, 14, 14], 1)]

def node0728Raw : WordRow := multiplyRow 14 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0728_check :
    collect (scaleRow 1 node0728Raw ++ scaleRow (-(1 : ℤ)) node0728 ++
      ([])) = [] := by
  decide +kernel

theorem node0728_mem : rowEval varIndex node0728 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0728Raw node0728 ([])
    (1) (1) (by decide) node0728_check
  · rw [node0728Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · exact candidateIdeal.zero_mem

def node0730 : WordRow := [([10, 15, 16], 1), ([11, 14, 16], 1)]

def node0730Raw : WordRow := multiplyRow 16 node0048

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0730_check :
    collect (scaleRow 1 node0730Raw ++ scaleRow (-(1 : ℤ)) node0730 ++
      ([])) = [] := by
  decide +kernel

theorem node0730_mem : rowEval varIndex node0730 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0730Raw node0730 ([])
    (1) (1) (by decide) node0730_check
  · rw [node0730Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0048_mem
  · exact candidateIdeal.zero_mem

def node0732 : WordRow := [([11, 12, 15], 1)]

def node0732Raw : WordRow := multiplyRow 12 node0049

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0732_check :
    collect (scaleRow 1 node0732Raw ++ scaleRow (-(1 : ℤ)) node0732 ++
      ([])) = [] := by
  decide +kernel

theorem node0732_mem : rowEval varIndex node0732 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0732Raw node0732 ([])
    (1) (1) (by decide) node0732_check
  · rw [node0732Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0049_mem
  · exact candidateIdeal.zero_mem

def node0738 : WordRow := [([1, 12, 14], 2), ([2, 12, 13], -1), ([3, 12, 12], -1), ([4, 7, 14], -1), ([4, 11, 12], -1), ([5, 6, 14], -1), ([5, 10, 12], -1), ([6, 9, 12], -1), ([7, 8, 12], -1)]

def node0738Raw : WordRow := multiplyRow 0 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0738_check :
    collect (scaleRow 1 node0738Raw ++ scaleRow (-(-1 : ℤ)) node0738 ++
      (scaleRow (-1) node0456 ++ scaleRow (-1) node0317)) = [] := by
  decide +kernel

theorem node0738_mem : rowEval varIndex node0738 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0738Raw node0738 (scaleRow (-1) node0456 ++ scaleRow (-1) node0317)
    (1) (-1) (by decide) node0738_check
  · rw [node0738Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0456 node0456_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0317 node0317_mem))

def node0739 : WordRow := [([2, 13, 14], 1), ([3, 12, 14], -1), ([8, 11, 12], -1), ([9, 10, 12], -1)]

def node0739Raw : WordRow := multiplyRow 2 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0739_check :
    collect (scaleRow 1 node0739Raw ++ scaleRow (-(1 : ℤ)) node0739 ++
      (scaleRow (-1) node0586)) = [] := by
  decide +kernel

theorem node0739_mem : rowEval varIndex node0739 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0739Raw node0739 (scaleRow (-1) node0586)
    (1) (1) (by decide) node0739_check
  · rw [node0739Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0586 node0586_mem)

def node0740 : WordRow := [([3, 13, 14], 1), ([9, 11, 12], -1)]

def node0740Raw : WordRow := multiplyRow 3 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0740_check :
    collect (scaleRow 1 node0740Raw ++ scaleRow (-(1 : ℤ)) node0740 ++
      (scaleRow (-1) node0596)) = [] := by
  decide +kernel

theorem node0740_mem : rowEval varIndex node0740 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0740Raw node0740 (scaleRow (-1) node0596)
    (1) (1) (by decide) node0740_check
  · rw [node0740Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0596 node0596_mem)

def node0741 : WordRow := [([5, 12, 14], 2), ([8, 12, 13], 1), ([9, 12, 12], 1)]

def node0741Raw : WordRow := multiplyRow 4 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0741_check :
    collect (scaleRow 1 node0741Raw ++ scaleRow (-(-1 : ℤ)) node0741 ++
      (scaleRow (-1) node0634 ++ scaleRow (-1) node0512)) = [] := by
  decide +kernel

theorem node0741_mem : rowEval varIndex node0741 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0741Raw node0741 (scaleRow (-1) node0634 ++ scaleRow (-1) node0512)
    (1) (-1) (by decide) node0741_check
  · rw [node0741Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0634 node0634_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0512 node0512_mem))

def node0742 : WordRow := [([7, 12, 14], 2), ([10, 12, 13], 1), ([11, 12, 12], 1)]

def node0742Raw : WordRow := multiplyRow 6 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0742_check :
    collect (scaleRow 1 node0742Raw ++ scaleRow (-(-1 : ℤ)) node0742 ++
      (scaleRow (-1) node0660 ++ scaleRow (-1) node0538)) = [] := by
  decide +kernel

theorem node0742_mem : rowEval varIndex node0742 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0742Raw node0742 (scaleRow (-1) node0660 ++ scaleRow (-1) node0538)
    (1) (-1) (by decide) node0742_check
  · rw [node0742Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node0660 node0660_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0538 node0538_mem))

def node0743 : WordRow := [([8, 13, 14], 1), ([9, 12, 14], -1)]

def node0743Raw : WordRow := multiplyRow 8 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0743_check :
    collect (scaleRow 1 node0743Raw ++ scaleRow (-(1 : ℤ)) node0743 ++
      (scaleRow (-1) node0702)) = [] := by
  decide +kernel

theorem node0743_mem : rowEval varIndex node0743 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0743Raw node0743 (scaleRow (-1) node0702)
    (1) (1) (by decide) node0743_check
  · rw [node0743Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0702 node0702_mem)

def node0744 : WordRow := [([9, 13, 14], 1)]

def node0744Raw : WordRow := multiplyRow 9 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0744_check :
    collect (scaleRow 1 node0744Raw ++ scaleRow (-(1 : ℤ)) node0744 ++
      (scaleRow (-1) node0712)) = [] := by
  decide +kernel

theorem node0744_mem : rowEval varIndex node0744 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0744Raw node0744 (scaleRow (-1) node0712)
    (1) (1) (by decide) node0744_check
  · rw [node0744Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0712 node0712_mem)

def node0745 : WordRow := [([10, 13, 14], 1), ([11, 12, 14], -1)]

def node0745Raw : WordRow := multiplyRow 10 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0745_check :
    collect (scaleRow 1 node0745Raw ++ scaleRow (-(1 : ℤ)) node0745 ++
      (scaleRow (-1) node0726)) = [] := by
  decide +kernel

theorem node0745_mem : rowEval varIndex node0745 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0745Raw node0745 (scaleRow (-1) node0726)
    (1) (1) (by decide) node0745_check
  · rw [node0745Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0726 node0726_mem)

def node0746 : WordRow := [([11, 13, 14], 1)]

def node0746Raw : WordRow := multiplyRow 11 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0746_check :
    collect (scaleRow 1 node0746Raw ++ scaleRow (-(1 : ℤ)) node0746 ++
      (scaleRow (-1) node0732)) = [] := by
  decide +kernel

theorem node0746_mem : rowEval varIndex node0746 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0746Raw node0746 (scaleRow (-1) node0732)
    (1) (1) (by decide) node0746_check
  · rw [node0746Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0732 node0732_mem)

def node0748 : WordRow := [([12, 14, 15], 1), ([13, 14, 14], 1)]

def node0748Raw : WordRow := multiplyRow 14 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0748_check :
    collect (scaleRow 1 node0748Raw ++ scaleRow (-(1 : ℤ)) node0748 ++
      ([])) = [] := by
  decide +kernel

theorem node0748_mem : rowEval varIndex node0748 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0748Raw node0748 ([])
    (1) (1) (by decide) node0748_check
  · rw [node0748Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · exact candidateIdeal.zero_mem

def node0750 : WordRow := [([12, 15, 16], 1), ([13, 14, 16], 1)]

def node0750Raw : WordRow := multiplyRow 16 node0050

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0750_check :
    collect (scaleRow 1 node0750Raw ++ scaleRow (-(1 : ℤ)) node0750 ++
      ([])) = [] := by
  decide +kernel

theorem node0750_mem : rowEval varIndex node0750 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0750Raw node0750 ([])
    (1) (1) (by decide) node0750_check
  · rw [node0750Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0050_mem
  · exact candidateIdeal.zero_mem

def node0756 : WordRow := [([1, 14, 14], 1), ([2, 13, 14], -1), ([3, 12, 14], -1), ([4, 11, 14], -1), ([5, 10, 14], -1), ([6, 9, 14], -1), ([7, 8, 14], -1)]

def node0756Raw : WordRow := multiplyRow 0 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0756_check :
    collect (scaleRow 1 node0756Raw ++ scaleRow (-(-1 : ℤ)) node0756 ++
      (scaleRow (-1) node0458)) = [] := by
  decide +kernel

theorem node0756_mem : rowEval varIndex node0756 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0756Raw node0756 (scaleRow (-1) node0458)
    (1) (-1) (by decide) node0756_check
  · rw [node0756Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0458 node0458_mem)

def node0757 : WordRow := [([3, 14, 14], 1), ([8, 11, 14], 1), ([9, 10, 14], 1)]

def node0757Raw : WordRow := multiplyRow 2 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0757_check :
    collect (scaleRow 1 node0757Raw ++ scaleRow (-(-1 : ℤ)) node0757 ++
      (scaleRow (-1) node0588)) = [] := by
  decide +kernel

theorem node0757_mem : rowEval varIndex node0757 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0757Raw node0757 (scaleRow (-1) node0588)
    (1) (-1) (by decide) node0757_check
  · rw [node0757Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0588 node0588_mem)

def node0758 : WordRow := [([5, 14, 14], 1), ([8, 13, 14], 1), ([9, 12, 14], 1)]

def node0758Raw : WordRow := multiplyRow 4 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0758_check :
    collect (scaleRow 1 node0758Raw ++ scaleRow (-(-1 : ℤ)) node0758 ++
      (scaleRow (-1) node0636)) = [] := by
  decide +kernel

theorem node0758_mem : rowEval varIndex node0758 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0758Raw node0758 (scaleRow (-1) node0636)
    (1) (-1) (by decide) node0758_check
  · rw [node0758Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0636 node0636_mem)

def node0759 : WordRow := [([7, 14, 14], 1), ([10, 13, 14], 1), ([11, 12, 14], 1)]

def node0759Raw : WordRow := multiplyRow 6 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0759_check :
    collect (scaleRow 1 node0759Raw ++ scaleRow (-(-1 : ℤ)) node0759 ++
      (scaleRow (-1) node0662)) = [] := by
  decide +kernel

theorem node0759_mem : rowEval varIndex node0759 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0759Raw node0759 (scaleRow (-1) node0662)
    (1) (-1) (by decide) node0759_check
  · rw [node0759Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0662 node0662_mem)

def node0760 : WordRow := [([9, 14, 14], 1)]

def node0760Raw : WordRow := multiplyRow 8 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0760_check :
    collect (scaleRow 1 node0760Raw ++ scaleRow (-(-1 : ℤ)) node0760 ++
      (scaleRow (-1) node0704)) = [] := by
  decide +kernel

theorem node0760_mem : rowEval varIndex node0760 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0760Raw node0760 (scaleRow (-1) node0704)
    (1) (-1) (by decide) node0760_check
  · rw [node0760Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0704 node0704_mem)

def node0761 : WordRow := [([11, 14, 14], 1)]

def node0761Raw : WordRow := multiplyRow 10 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0761_check :
    collect (scaleRow 1 node0761Raw ++ scaleRow (-(-1 : ℤ)) node0761 ++
      (scaleRow (-1) node0728)) = [] := by
  decide +kernel

theorem node0761_mem : rowEval varIndex node0761 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0761Raw node0761 (scaleRow (-1) node0728)
    (1) (-1) (by decide) node0761_check
  · rw [node0761Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0728 node0728_mem)

def node0762 : WordRow := [([13, 14, 14], 1)]

def node0762Raw : WordRow := multiplyRow 12 node0052

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0762_check :
    collect (scaleRow 1 node0762Raw ++ scaleRow (-(-1 : ℤ)) node0762 ++
      (scaleRow (-1) node0748)) = [] := by
  decide +kernel

theorem node0762_mem : rowEval varIndex node0762 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0762Raw node0762 (scaleRow (-1) node0748)
    (1) (-1) (by decide) node0762_check
  · rw [node0762Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0052_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node0748 node0748_mem)

def node0770 : WordRow := [([0, 0, 0], 1)]

def node0770Raw : WordRow := [(seedWords 0,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0770_check :
    collect (scaleRow 1 node0770Raw ++ scaleRow (-(1 : ℤ)) node0770 ++
      ([])) = [] := by
  decide +kernel

theorem node0770_mem : rowEval varIndex node0770 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0770Raw node0770 ([])
    (1) (1) (by decide) node0770_check
  · exact seedWord_mem 0
  · exact candidateIdeal.zero_mem

def node0771 : WordRow := [([16, 17, 17], 1)]

def node0771Raw : WordRow := [(seedWords 5,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0771_check :
    collect (scaleRow 1 node0771Raw ++ scaleRow (-(1 : ℤ)) node0771 ++
      ([])) = [] := by
  decide +kernel

theorem node0771_mem : rowEval varIndex node0771 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0771Raw node0771 ([])
    (1) (1) (by decide) node0771_check
  · exact seedWord_mem 5
  · exact candidateIdeal.zero_mem

def node0772 : WordRow := [([17, 17, 17], 1)]

def node0772Raw : WordRow := [(seedWords 6,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0772_check :
    collect (scaleRow 1 node0772Raw ++ scaleRow (-(1 : ℤ)) node0772 ++
      ([])) = [] := by
  decide +kernel

theorem node0772_mem : rowEval varIndex node0772 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0772Raw node0772 ([])
    (1) (1) (by decide) node0772_check
  · exact seedWord_mem 6
  · exact candidateIdeal.zero_mem

def node0773 : WordRow := [([0, 0, 2], 1)]

def node0773Raw : WordRow := differentiateRow (images 14) node0770

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0773_check :
    collect (scaleRow 1 node0773Raw ++ scaleRow (-(3 : ℤ)) node0773 ++
      ([])) = [] := by
  decide +kernel

theorem node0773_mem : rowEval varIndex node0773 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0773Raw node0773 ([])
    (1) (3) (by decide) node0773_check
  · rw [node0773Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0770_mem
  · exact candidateIdeal.zero_mem

def node0774 : WordRow := [([0, 0, 4], 1)]

def node0774Raw : WordRow := differentiateRow (images 16) node0770

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0774_check :
    collect (scaleRow 1 node0774Raw ++ scaleRow (-(3 : ℤ)) node0774 ++
      ([])) = [] := by
  decide +kernel

theorem node0774_mem : rowEval varIndex node0774 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0774Raw node0774 ([])
    (1) (3) (by decide) node0774_check
  · rw [node0774Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0770_mem
  · exact candidateIdeal.zero_mem

def node0775 : WordRow := [([0, 0, 6], 1)]

def node0775Raw : WordRow := differentiateRow (images 18) node0770

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0775_check :
    collect (scaleRow 1 node0775Raw ++ scaleRow (-(-3 : ℤ)) node0775 ++
      ([])) = [] := by
  decide +kernel

theorem node0775_mem : rowEval varIndex node0775 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0775Raw node0775 ([])
    (1) (-3) (by decide) node0775_check
  · rw [node0775Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0770_mem
  · exact candidateIdeal.zero_mem

def node0776 : WordRow := [([0, 17, 17], 1), ([1, 16, 17], 2)]

def node0776Raw : WordRow := differentiateRow (images 20) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0776_check :
    collect (scaleRow 1 node0776Raw ++ scaleRow (-(1 : ℤ)) node0776 ++
      ([])) = [] := by
  decide +kernel

theorem node0776_mem : rowEval varIndex node0776 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0776Raw node0776 ([])
    (1) (1) (by decide) node0776_check
  · rw [node0776Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0777 : WordRow := [([1, 17, 17], 1)]

def node0777Raw : WordRow := differentiateRow (images 21) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0777_check :
    collect (scaleRow 1 node0777Raw ++ scaleRow (-(1 : ℤ)) node0777 ++
      ([])) = [] := by
  decide +kernel

theorem node0777_mem : rowEval varIndex node0777 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0777Raw node0777 ([])
    (1) (1) (by decide) node0777_check
  · rw [node0777Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0778 : WordRow := [([2, 17, 17], 1), ([3, 16, 17], 2)]

def node0778Raw : WordRow := differentiateRow (images 22) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0778_check :
    collect (scaleRow 1 node0778Raw ++ scaleRow (-(1 : ℤ)) node0778 ++
      ([])) = [] := by
  decide +kernel

theorem node0778_mem : rowEval varIndex node0778 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0778Raw node0778 ([])
    (1) (1) (by decide) node0778_check
  · rw [node0778Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0779 : WordRow := [([3, 17, 17], 1)]

def node0779Raw : WordRow := differentiateRow (images 23) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0779_check :
    collect (scaleRow 1 node0779Raw ++ scaleRow (-(1 : ℤ)) node0779 ++
      ([])) = [] := by
  decide +kernel

theorem node0779_mem : rowEval varIndex node0779 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0779Raw node0779 ([])
    (1) (1) (by decide) node0779_check
  · rw [node0779Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0780 : WordRow := [([4, 17, 17], 1), ([5, 16, 17], 2)]

def node0780Raw : WordRow := differentiateRow (images 24) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0780_check :
    collect (scaleRow 1 node0780Raw ++ scaleRow (-(1 : ℤ)) node0780 ++
      ([])) = [] := by
  decide +kernel

theorem node0780_mem : rowEval varIndex node0780 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0780Raw node0780 ([])
    (1) (1) (by decide) node0780_check
  · rw [node0780Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

def node0781 : WordRow := [([5, 17, 17], 1)]

def node0781Raw : WordRow := differentiateRow (images 25) node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0781_check :
    collect (scaleRow 1 node0781Raw ++ scaleRow (-(1 : ℤ)) node0781 ++
      ([])) = [] := by
  decide +kernel

theorem node0781_mem : rowEval varIndex node0781 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0781Raw node0781 ([])
    (1) (1) (by decide) node0781_check
  · rw [node0781Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0771_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0781_mem
