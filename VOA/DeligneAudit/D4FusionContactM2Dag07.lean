import VOA.DeligneAudit.D4FusionContactM2Dag06

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0846 : WordRow := [([0, 12, 14], 2), ([2, 12, 12], -1), ([4, 6, 14], -2), ([4, 10, 12], -2), ([6, 8, 12], -2)]

def node0846Raw : WordRow := differentiateRow (images 18) node0832

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0846_check :
    collect (scaleRow 1 node0846Raw ++ scaleRow (-(2 : ℤ)) node0846 ++
      ([])) = [] := by
  decide +kernel

theorem node0846_mem : rowEval varIndex node0846 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0846Raw node0846 ([])
    (1) (2) (by decide) node0846_check
  · rw [node0846Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0832_mem
  · exact candidateIdeal.zero_mem

def node0847 : WordRow := [([6, 6, 14], 1), ([6, 10, 12], 2)]

def node0847Raw : WordRow := differentiateRow (images 18) node0833

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0847_check :
    collect (scaleRow 1 node0847Raw ++ scaleRow (-(-3 : ℤ)) node0847 ++
      ([])) = [] := by
  decide +kernel

theorem node0847_mem : rowEval varIndex node0847 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0847Raw node0847 ([])
    (1) (-3) (by decide) node0847_check
  · rw [node0847Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0833_mem
  · exact candidateIdeal.zero_mem

def node0848 : WordRow := [([4, 12, 12], 1)]

def node0848Raw : WordRow := differentiateRow (images 18) node0835

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0848_check :
    collect (scaleRow 1 node0848Raw ++ scaleRow (-(2 : ℤ)) node0848 ++
      ([])) = [] := by
  decide +kernel

theorem node0848_mem : rowEval varIndex node0848 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0848Raw node0848 ([])
    (1) (2) (by decide) node0848_check
  · rw [node0848Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0835_mem
  · exact candidateIdeal.zero_mem

def node0849 : WordRow := [([6, 12, 12], 1)]

def node0849Raw : WordRow := differentiateRow (images 18) node0836

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0849_check :
    collect (scaleRow 1 node0849Raw ++ scaleRow (-(-3 : ℤ)) node0849 ++
      ([])) = [] := by
  decide +kernel

theorem node0849_mem : rowEval varIndex node0849 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0849Raw node0849 ([])
    (1) (-3) (by decide) node0849_check
  · rw [node0849Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0836_mem
  · exact candidateIdeal.zero_mem

def node0850 : WordRow := [([8, 8, 8], 1)]

def node0850Raw : WordRow := differentiateRow (images 16) node0838

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0850_check :
    collect (scaleRow 1 node0850Raw ++ scaleRow (-(-1 : ℤ)) node0850 ++
      ([])) = [] := by
  decide +kernel

theorem node0850_mem : rowEval varIndex node0850 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0850Raw node0850 ([])
    (1) (-1) (by decide) node0850_check
  · rw [node0850Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0838_mem
  · exact candidateIdeal.zero_mem

def node0851 : WordRow := [([2, 8, 14], 2), ([8, 8, 10], 1)]

def node0851Raw : WordRow := differentiateRow (images 18) node0838

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0851_check :
    collect (scaleRow 1 node0851Raw ++ scaleRow (-(1 : ℤ)) node0851 ++
      ([])) = [] := by
  decide +kernel

theorem node0851_mem : rowEval varIndex node0851 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0851Raw node0851 ([])
    (1) (1) (by decide) node0851_check
  · rw [node0851Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0838_mem
  · exact candidateIdeal.zero_mem

def node0852 : WordRow := [([2, 10, 14], 2), ([8, 10, 10], 1)]

def node0852Raw : WordRow := differentiateRow (images 18) node0839

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0852_check :
    collect (scaleRow 1 node0852Raw ++ scaleRow (-(2 : ℤ)) node0852 ++
      ([])) = [] := by
  decide +kernel

theorem node0852_mem : rowEval varIndex node0852 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0852Raw node0852 ([])
    (1) (2) (by decide) node0852_check
  · rw [node0852Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0839_mem
  · exact candidateIdeal.zero_mem

def node0853 : WordRow := [([10, 10, 10], 1)]

def node0853Raw : WordRow := differentiateRow (images 18) node0840

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0853_check :
    collect (scaleRow 1 node0853Raw ++ scaleRow (-(1 : ℤ)) node0853 ++
      ([])) = [] := by
  decide +kernel

theorem node0853_mem : rowEval varIndex node0853 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0853Raw node0853 ([])
    (1) (1) (by decide) node0853_check
  · rw [node0853Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0840_mem
  · exact candidateIdeal.zero_mem

def node0854 : WordRow := [([4, 8, 14], 2), ([8, 8, 12], 1)]

def node0854Raw : WordRow := differentiateRow (images 18) node0841

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0854_check :
    collect (scaleRow 1 node0854Raw ++ scaleRow (-(1 : ℤ)) node0854 ++
      ([])) = [] := by
  decide +kernel

theorem node0854_mem : rowEval varIndex node0854 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0854Raw node0854 ([])
    (1) (1) (by decide) node0854_check
  · rw [node0854Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0841_mem
  · exact candidateIdeal.zero_mem

def node0855 : WordRow := [([0, 14, 14], 1), ([2, 12, 14], -2), ([4, 10, 14], -2), ([6, 8, 14], -2), ([8, 10, 12], -2)]

def node0855Raw : WordRow := differentiateRow (images 18) node0842

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0855_check :
    collect (scaleRow 1 node0855Raw ++ scaleRow (-(2 : ℤ)) node0855 ++
      ([])) = [] := by
  decide +kernel

theorem node0855_mem : rowEval varIndex node0855 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0855Raw node0855 ([])
    (1) (2) (by decide) node0855_check
  · rw [node0855Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0842_mem
  · exact candidateIdeal.zero_mem

def node0856 : WordRow := [([6, 10, 14], 2), ([10, 10, 12], 1)]

def node0856Raw : WordRow := differentiateRow (images 18) node0843

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0856_check :
    collect (scaleRow 1 node0856Raw ++ scaleRow (-(-3 : ℤ)) node0856 ++
      ([])) = [] := by
  decide +kernel

theorem node0856_mem : rowEval varIndex node0856 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0856Raw node0856 ([])
    (1) (-3) (by decide) node0856_check
  · rw [node0856Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0843_mem
  · exact candidateIdeal.zero_mem

def node0857 : WordRow := [([4, 12, 14], 2), ([8, 12, 12], 1)]

def node0857Raw : WordRow := differentiateRow (images 18) node0845

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0857_check :
    collect (scaleRow 1 node0857Raw ++ scaleRow (-(2 : ℤ)) node0857 ++
      ([])) = [] := by
  decide +kernel

theorem node0857_mem : rowEval varIndex node0857 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0857Raw node0857 ([])
    (1) (2) (by decide) node0857_check
  · rw [node0857Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0845_mem
  · exact candidateIdeal.zero_mem

def node0858 : WordRow := [([6, 12, 14], 2), ([10, 12, 12], 1)]

def node0858Raw : WordRow := differentiateRow (images 18) node0846

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0858_check :
    collect (scaleRow 1 node0858Raw ++ scaleRow (-(-3 : ℤ)) node0858 ++
      ([])) = [] := by
  decide +kernel

theorem node0858_mem : rowEval varIndex node0858 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0858Raw node0858 ([])
    (1) (-3) (by decide) node0858_check
  · rw [node0858Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0846_mem
  · exact candidateIdeal.zero_mem

def node0859 : WordRow := [([12, 12, 12], 1)]

def node0859Raw : WordRow := differentiateRow (images 18) node0848

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0859_check :
    collect (scaleRow 1 node0859Raw ++ scaleRow (-(1 : ℤ)) node0859 ++
      ([])) = [] := by
  decide +kernel

theorem node0859_mem : rowEval varIndex node0859 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0859Raw node0859 ([])
    (1) (1) (by decide) node0859_check
  · rw [node0859Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0848_mem
  · exact candidateIdeal.zero_mem

def node0860 : WordRow := [([8, 8, 14], 1)]

def node0860Raw : WordRow := differentiateRow (images 18) node0850

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0860_check :
    collect (scaleRow 1 node0860Raw ++ scaleRow (-(3 : ℤ)) node0860 ++
      ([])) = [] := by
  decide +kernel

theorem node0860_mem : rowEval varIndex node0860 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0860Raw node0860 ([])
    (1) (3) (by decide) node0860_check
  · rw [node0860Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0850_mem
  · exact candidateIdeal.zero_mem

def node0861 : WordRow := [([2, 14, 14], 1), ([8, 10, 14], 2)]

def node0861Raw : WordRow := differentiateRow (images 18) node0851

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0861_check :
    collect (scaleRow 1 node0861Raw ++ scaleRow (-(2 : ℤ)) node0861 ++
      ([])) = [] := by
  decide +kernel

theorem node0861_mem : rowEval varIndex node0861 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0861Raw node0861 ([])
    (1) (2) (by decide) node0861_check
  · rw [node0861Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0851_mem
  · exact candidateIdeal.zero_mem

def node0862 : WordRow := [([10, 10, 14], 1)]

def node0862Raw : WordRow := differentiateRow (images 18) node0852

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0862_check :
    collect (scaleRow 1 node0862Raw ++ scaleRow (-(3 : ℤ)) node0862 ++
      ([])) = [] := by
  decide +kernel

theorem node0862_mem : rowEval varIndex node0862 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0862Raw node0862 ([])
    (1) (3) (by decide) node0862_check
  · rw [node0862Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0852_mem
  · exact candidateIdeal.zero_mem

def node0863 : WordRow := [([4, 14, 14], 1), ([8, 12, 14], 2)]

def node0863Raw : WordRow := differentiateRow (images 18) node0854

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0863_check :
    collect (scaleRow 1 node0863Raw ++ scaleRow (-(2 : ℤ)) node0863 ++
      ([])) = [] := by
  decide +kernel

theorem node0863_mem : rowEval varIndex node0863 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0863Raw node0863 ([])
    (1) (2) (by decide) node0863_check
  · rw [node0863Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0854_mem
  · exact candidateIdeal.zero_mem

def node0864 : WordRow := [([6, 14, 14], 1), ([10, 12, 14], 2)]

def node0864Raw : WordRow := differentiateRow (images 18) node0855

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0864_check :
    collect (scaleRow 1 node0864Raw ++ scaleRow (-(-3 : ℤ)) node0864 ++
      ([])) = [] := by
  decide +kernel

theorem node0864_mem : rowEval varIndex node0864 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0864Raw node0864 ([])
    (1) (-3) (by decide) node0864_check
  · rw [node0864Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0855_mem
  · exact candidateIdeal.zero_mem

def node0865 : WordRow := [([12, 12, 14], 1)]

def node0865Raw : WordRow := differentiateRow (images 18) node0857

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0865_check :
    collect (scaleRow 1 node0865Raw ++ scaleRow (-(3 : ℤ)) node0865 ++
      ([])) = [] := by
  decide +kernel

theorem node0865_mem : rowEval varIndex node0865 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0865Raw node0865 ([])
    (1) (3) (by decide) node0865_check
  · rw [node0865Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0857_mem
  · exact candidateIdeal.zero_mem

def node0866 : WordRow := [([8, 14, 14], 1)]

def node0866Raw : WordRow := differentiateRow (images 18) node0860

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0866_check :
    collect (scaleRow 1 node0866Raw ++ scaleRow (-(2 : ℤ)) node0866 ++
      ([])) = [] := by
  decide +kernel

theorem node0866_mem : rowEval varIndex node0866 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0866Raw node0866 ([])
    (1) (2) (by decide) node0866_check
  · rw [node0866Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0860_mem
  · exact candidateIdeal.zero_mem

def node0867 : WordRow := [([10, 14, 14], 1)]

def node0867Raw : WordRow := differentiateRow (images 18) node0861

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0867_check :
    collect (scaleRow 1 node0867Raw ++ scaleRow (-(3 : ℤ)) node0867 ++
      ([])) = [] := by
  decide +kernel

theorem node0867_mem : rowEval varIndex node0867 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0867Raw node0867 ([])
    (1) (3) (by decide) node0867_check
  · rw [node0867Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0861_mem
  · exact candidateIdeal.zero_mem

def node0868 : WordRow := [([12, 14, 14], 1)]

def node0868Raw : WordRow := differentiateRow (images 18) node0863

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0868_check :
    collect (scaleRow 1 node0868Raw ++ scaleRow (-(3 : ℤ)) node0868 ++
      ([])) = [] := by
  decide +kernel

theorem node0868_mem : rowEval varIndex node0868 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0868Raw node0868 ([])
    (1) (3) (by decide) node0868_check
  · rw [node0868Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0863_mem
  · exact candidateIdeal.zero_mem

def node0869 : WordRow := [([14, 14, 14], 1)]

def node0869Raw : WordRow := differentiateRow (images 18) node0866

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0869_check :
    collect (scaleRow 1 node0869Raw ++ scaleRow (-(1 : ℤ)) node0869 ++
      ([])) = [] := by
  decide +kernel

theorem node0869_mem : rowEval varIndex node0869 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0869Raw node0869 ([])
    (1) (1) (by decide) node0869_check
  · rw [node0869Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0866_mem
  · exact candidateIdeal.zero_mem

def node0884 : WordRow := [([0, 0, 1, 14], 1)]

def node0884Raw : WordRow := multiplyRow 14 node0054

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0884_check :
    collect (scaleRow 1 node0884Raw ++ scaleRow (-(1 : ℤ)) node0884 ++
      ([])) = [] := by
  decide +kernel

theorem node0884_mem : rowEval varIndex node0884 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0884Raw node0884 ([])
    (1) (1) (by decide) node0884_check
  · rw [node0884Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0054_mem
  · exact candidateIdeal.zero_mem

def node0915 : WordRow := [([0, 1, 2, 12], 1)]

def node0915Raw : WordRow := multiplyRow 12 node0056

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0915_check :
    collect (scaleRow 1 node0915Raw ++ scaleRow (-(1 : ℤ)) node0915 ++
      ([])) = [] := by
  decide +kernel

theorem node0915_mem : rowEval varIndex node0915 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0915Raw node0915 ([])
    (1) (1) (by decide) node0915_check
  · rw [node0915Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0056_mem
  · exact candidateIdeal.zero_mem

def node0917 : WordRow := [([0, 1, 2, 14], 1)]

def node0917Raw : WordRow := multiplyRow 14 node0056

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0917_check :
    collect (scaleRow 1 node0917Raw ++ scaleRow (-(1 : ℤ)) node0917 ++
      ([])) = [] := by
  decide +kernel

theorem node0917_mem : rowEval varIndex node0917 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0917Raw node0917 ([])
    (1) (1) (by decide) node0917_check
  · rw [node0917Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0056_mem
  · exact candidateIdeal.zero_mem

def node0942 : WordRow := [([0, 1, 4, 10], 1)]

def node0942Raw : WordRow := multiplyRow 10 node0058

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0942_check :
    collect (scaleRow 1 node0942Raw ++ scaleRow (-(1 : ℤ)) node0942 ++
      ([])) = [] := by
  decide +kernel

theorem node0942_mem : rowEval varIndex node0942 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0942Raw node0942 ([])
    (1) (1) (by decide) node0942_check
  · rw [node0942Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0058_mem
  · exact candidateIdeal.zero_mem

def node0946 : WordRow := [([0, 1, 4, 14], 1)]

def node0946Raw : WordRow := multiplyRow 14 node0058

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0946_check :
    collect (scaleRow 1 node0946Raw ++ scaleRow (-(1 : ℤ)) node0946 ++
      ([])) = [] := by
  decide +kernel

theorem node0946_mem : rowEval varIndex node0946 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0946Raw node0946 ([])
    (1) (1) (by decide) node0946_check
  · rw [node0946Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0058_mem
  · exact candidateIdeal.zero_mem

def node0965 : WordRow := [([0, 1, 6, 8], 1)]

def node0965Raw : WordRow := multiplyRow 8 node0060

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0965_check :
    collect (scaleRow 1 node0965Raw ++ scaleRow (-(1 : ℤ)) node0965 ++
      ([])) = [] := by
  decide +kernel

theorem node0965_mem : rowEval varIndex node0965 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0965Raw node0965 ([])
    (1) (1) (by decide) node0965_check
  · rw [node0965Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0060_mem
  · exact candidateIdeal.zero_mem

def node0971 : WordRow := [([0, 1, 6, 14], 1)]

def node0971Raw : WordRow := multiplyRow 14 node0060

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0971_check :
    collect (scaleRow 1 node0971Raw ++ scaleRow (-(1 : ℤ)) node0971 ++
      ([])) = [] := by
  decide +kernel

theorem node0971_mem : rowEval varIndex node0971 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0971Raw node0971 ([])
    (1) (1) (by decide) node0971_check
  · rw [node0971Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0060_mem
  · exact candidateIdeal.zero_mem

def node0992 : WordRow := [([0, 1, 8, 14], 1)]

def node0992Raw : WordRow := multiplyRow 14 node0062

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0992_check :
    collect (scaleRow 1 node0992Raw ++ scaleRow (-(1 : ℤ)) node0992 ++
      ([])) = [] := by
  decide +kernel

theorem node0992_mem : rowEval varIndex node0992 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0992Raw node0992 ([])
    (1) (1) (by decide) node0992_check
  · rw [node0992Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0062_mem
  · exact candidateIdeal.zero_mem

def node0994 : WordRow := [([0, 1, 8, 16], 1)]

def node0994Raw : WordRow := multiplyRow 16 node0062

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0994_check :
    collect (scaleRow 1 node0994Raw ++ scaleRow (-(1 : ℤ)) node0994 ++
      ([])) = [] := by
  decide +kernel

theorem node0994_mem : rowEval varIndex node0994 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0994Raw node0994 ([])
    (1) (1) (by decide) node0994_check
  · rw [node0994Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0062_mem
  · exact candidateIdeal.zero_mem

def node1009 : WordRow := [([0, 1, 10, 14], 1)]

def node1009Raw : WordRow := multiplyRow 14 node0064

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1009_check :
    collect (scaleRow 1 node1009Raw ++ scaleRow (-(1 : ℤ)) node1009 ++
      ([])) = [] := by
  decide +kernel

theorem node1009_mem : rowEval varIndex node1009 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1009Raw node1009 ([])
    (1) (1) (by decide) node1009_check
  · rw [node1009Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0064_mem
  · exact candidateIdeal.zero_mem

def node1011 : WordRow := [([0, 1, 10, 16], 1)]

def node1011Raw : WordRow := multiplyRow 16 node0064

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1011_check :
    collect (scaleRow 1 node1011Raw ++ scaleRow (-(1 : ℤ)) node1011 ++
      ([])) = [] := by
  decide +kernel

theorem node1011_mem : rowEval varIndex node1011 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1011Raw node1011 ([])
    (1) (1) (by decide) node1011_check
  · rw [node1011Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0064_mem
  · exact candidateIdeal.zero_mem

def node1022 : WordRow := [([0, 1, 12, 14], 1)]

def node1022Raw : WordRow := multiplyRow 14 node0066

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1022_check :
    collect (scaleRow 1 node1022Raw ++ scaleRow (-(1 : ℤ)) node1022 ++
      ([])) = [] := by
  decide +kernel

theorem node1022_mem : rowEval varIndex node1022 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1022Raw node1022 ([])
    (1) (1) (by decide) node1022_check
  · rw [node1022Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0066_mem
  · exact candidateIdeal.zero_mem

def node1024 : WordRow := [([0, 1, 12, 16], 1)]

def node1024Raw : WordRow := multiplyRow 16 node0066

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1024_check :
    collect (scaleRow 1 node1024Raw ++ scaleRow (-(1 : ℤ)) node1024 ++
      ([])) = [] := by
  decide +kernel

theorem node1024_mem : rowEval varIndex node1024 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1024Raw node1024 ([])
    (1) (1) (by decide) node1024_check
  · rw [node1024Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0066_mem
  · exact candidateIdeal.zero_mem

def node1031 : WordRow := [([0, 1, 14, 14], 1)]

def node1031Raw : WordRow := multiplyRow 14 node0068

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1031_check :
    collect (scaleRow 1 node1031Raw ++ scaleRow (-(1 : ℤ)) node1031 ++
      ([])) = [] := by
  decide +kernel

theorem node1031_mem : rowEval varIndex node1031 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1031Raw node1031 ([])
    (1) (1) (by decide) node1031_check
  · rw [node1031Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0068_mem
  · exact candidateIdeal.zero_mem

def node1033 : WordRow := [([0, 1, 14, 16], 1)]

def node1033Raw : WordRow := multiplyRow 16 node0068

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1033_check :
    collect (scaleRow 1 node1033Raw ++ scaleRow (-(1 : ℤ)) node1033 ++
      ([])) = [] := by
  decide +kernel

theorem node1033_mem : rowEval varIndex node1033 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1033Raw node1033 ([])
    (1) (1) (by decide) node1033_check
  · rw [node1033Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0068_mem
  · exact candidateIdeal.zero_mem

def node1205 : WordRow := [([0, 0, 3, 12], 1), ([0, 1, 2, 12], 1)]

def node1205Raw : WordRow := multiplyRow 12 node0089

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1205_check :
    collect (scaleRow 1 node1205Raw ++ scaleRow (-(1 : ℤ)) node1205 ++
      ([])) = [] := by
  decide +kernel

theorem node1205_mem : rowEval varIndex node1205 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1205Raw node1205 ([])
    (1) (1) (by decide) node1205_check
  · rw [node1205Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0089_mem
  · exact candidateIdeal.zero_mem

def node1221 : WordRow := [([0, 2, 3, 12], 1), ([1, 2, 2, 12], 1)]

def node1221Raw : WordRow := multiplyRow 12 node0090

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1221_check :
    collect (scaleRow 1 node1221Raw ++ scaleRow (-(1 : ℤ)) node1221 ++
      ([])) = [] := by
  decide +kernel

theorem node1221_mem : rowEval varIndex node1221 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1221Raw node1221 ([])
    (1) (1) (by decide) node1221_check
  · rw [node1221Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0090_mem
  · exact candidateIdeal.zero_mem

def node1244 : WordRow := [([0, 3, 4, 6], 1), ([1, 2, 4, 6], 1)]

def node1244Raw : WordRow := multiplyRow 6 node0092

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1244_check :
    collect (scaleRow 1 node1244Raw ++ scaleRow (-(1 : ℤ)) node1244 ++
      ([])) = [] := by
  decide +kernel

theorem node1244_mem : rowEval varIndex node1244 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1244Raw node1244 ([])
    (1) (1) (by decide) node1244_check
  · rw [node1244Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0092_mem
  · exact candidateIdeal.zero_mem

def node1250 : WordRow := [([0, 3, 4, 12], 1), ([1, 2, 4, 12], 1)]

def node1250Raw : WordRow := multiplyRow 12 node0092

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1250_check :
    collect (scaleRow 1 node1250Raw ++ scaleRow (-(1 : ℤ)) node1250 ++
      ([])) = [] := by
  decide +kernel

theorem node1250_mem : rowEval varIndex node1250 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1250Raw node1250 ([])
    (1) (1) (by decide) node1250_check
  · rw [node1250Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0092_mem
  · exact candidateIdeal.zero_mem

def node1255 : WordRow := [([0, 3, 4, 17], 1), ([1, 2, 4, 17], 1)]

def node1255Raw : WordRow := multiplyRow 17 node0092

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1255_check :
    collect (scaleRow 1 node1255Raw ++ scaleRow (-(1 : ℤ)) node1255 ++
      ([])) = [] := by
  decide +kernel

theorem node1255_mem : rowEval varIndex node1255 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1255Raw node1255 ([])
    (1) (1) (by decide) node1255_check
  · rw [node1255Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0092_mem
  · exact candidateIdeal.zero_mem

def node1267 : WordRow := [([0, 3, 5, 16], 1), ([1, 2, 5, 16], 1)]

def node1267Raw : WordRow := multiplyRow 16 node0093

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1267_check :
    collect (scaleRow 1 node1267Raw ++ scaleRow (-(1 : ℤ)) node1267 ++
      ([])) = [] := by
  decide +kernel

theorem node1267_mem : rowEval varIndex node1267 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1267Raw node1267 ([])
    (1) (1) (by decide) node1267_check
  · rw [node1267Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0093_mem
  · exact candidateIdeal.zero_mem

def node1275 : WordRow := [([0, 3, 6, 12], 1), ([1, 2, 6, 12], 1)]

def node1275Raw : WordRow := multiplyRow 12 node0094

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1275_check :
    collect (scaleRow 1 node1275Raw ++ scaleRow (-(1 : ℤ)) node1275 ++
      ([])) = [] := by
  decide +kernel

theorem node1275_mem : rowEval varIndex node1275 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1275Raw node1275 ([])
    (1) (1) (by decide) node1275_check
  · rw [node1275Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0094_mem
  · exact candidateIdeal.zero_mem

def node1280 : WordRow := [([0, 3, 6, 17], 1), ([1, 2, 6, 17], 1)]

def node1280Raw : WordRow := multiplyRow 17 node0094

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1280_check :
    collect (scaleRow 1 node1280Raw ++ scaleRow (-(1 : ℤ)) node1280 ++
      ([])) = [] := by
  decide +kernel

theorem node1280_mem : rowEval varIndex node1280 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1280Raw node1280 ([])
    (1) (1) (by decide) node1280_check
  · rw [node1280Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0094_mem
  · exact candidateIdeal.zero_mem

def node1290 : WordRow := [([0, 3, 7, 16], 1), ([1, 2, 7, 16], 1)]

def node1290Raw : WordRow := multiplyRow 16 node0095

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1290_check :
    collect (scaleRow 1 node1290Raw ++ scaleRow (-(1 : ℤ)) node1290 ++
      ([])) = [] := by
  decide +kernel

theorem node1290_mem : rowEval varIndex node1290 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1290Raw node1290 ([])
    (1) (1) (by decide) node1290_check
  · rw [node1290Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0095_mem
  · exact candidateIdeal.zero_mem

def node1296 : WordRow := [([0, 3, 8, 12], 1), ([1, 2, 8, 12], 1)]

def node1296Raw : WordRow := multiplyRow 12 node0096

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1296_check :
    collect (scaleRow 1 node1296Raw ++ scaleRow (-(1 : ℤ)) node1296 ++
      ([])) = [] := by
  decide +kernel

theorem node1296_mem : rowEval varIndex node1296 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1296Raw node1296 ([])
    (1) (1) (by decide) node1296_check
  · rw [node1296Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0096_mem
  · exact candidateIdeal.zero_mem

def node1300 : WordRow := [([0, 3, 8, 16], 1), ([1, 2, 8, 16], 1)]

def node1300Raw : WordRow := multiplyRow 16 node0096

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1300_check :
    collect (scaleRow 1 node1300Raw ++ scaleRow (-(1 : ℤ)) node1300 ++
      ([])) = [] := by
  decide +kernel

theorem node1300_mem : rowEval varIndex node1300 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1300Raw node1300 ([])
    (1) (1) (by decide) node1300_check
  · rw [node1300Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0096_mem
  · exact candidateIdeal.zero_mem

def node1313 : WordRow := [([0, 3, 10, 12], 1), ([1, 2, 10, 12], 1)]

def node1313Raw : WordRow := multiplyRow 12 node0098

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1313_check :
    collect (scaleRow 1 node1313Raw ++ scaleRow (-(1 : ℤ)) node1313 ++
      ([])) = [] := by
  decide +kernel

theorem node1313_mem : rowEval varIndex node1313 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1313Raw node1313 ([])
    (1) (1) (by decide) node1313_check
  · rw [node1313Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0098_mem
  · exact candidateIdeal.zero_mem

def node1317 : WordRow := [([0, 3, 10, 16], 1), ([1, 2, 10, 16], 1)]

def node1317Raw : WordRow := multiplyRow 16 node0098

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1317_check :
    collect (scaleRow 1 node1317Raw ++ scaleRow (-(1 : ℤ)) node1317 ++
      ([])) = [] := by
  decide +kernel

theorem node1317_mem : rowEval varIndex node1317 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1317Raw node1317 ([])
    (1) (1) (by decide) node1317_check
  · rw [node1317Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0098_mem
  · exact candidateIdeal.zero_mem

def node1326 : WordRow := [([0, 3, 12, 12], 1), ([1, 2, 12, 12], 1)]

def node1326Raw : WordRow := multiplyRow 12 node0100

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1326_check :
    collect (scaleRow 1 node1326Raw ++ scaleRow (-(1 : ℤ)) node1326 ++
      ([])) = [] := by
  decide +kernel

theorem node1326_mem : rowEval varIndex node1326 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1326Raw node1326 ([])
    (1) (1) (by decide) node1326_check
  · rw [node1326Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0100_mem
  · exact candidateIdeal.zero_mem

def node1328 : WordRow := [([0, 3, 12, 14], 1), ([1, 2, 12, 14], 1)]

def node1328Raw : WordRow := multiplyRow 14 node0100

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1328_check :
    collect (scaleRow 1 node1328Raw ++ scaleRow (-(1 : ℤ)) node1328 ++
      ([])) = [] := by
  decide +kernel

theorem node1328_mem : rowEval varIndex node1328 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1328Raw node1328 ([])
    (1) (1) (by decide) node1328_check
  · rw [node1328Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0100_mem
  · exact candidateIdeal.zero_mem

def node1330 : WordRow := [([0, 3, 12, 16], 1), ([1, 2, 12, 16], 1)]

def node1330Raw : WordRow := multiplyRow 16 node0100

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1330_check :
    collect (scaleRow 1 node1330Raw ++ scaleRow (-(1 : ℤ)) node1330 ++
      ([])) = [] := by
  decide +kernel

theorem node1330_mem : rowEval varIndex node1330 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1330Raw node1330 ([])
    (1) (1) (by decide) node1330_check
  · rw [node1330Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0100_mem
  · exact candidateIdeal.zero_mem

def node1331 : WordRow := [([0, 3, 12, 17], 1), ([1, 2, 12, 17], 1)]

def node1331Raw : WordRow := multiplyRow 17 node0100

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1331_check :
    collect (scaleRow 1 node1331Raw ++ scaleRow (-(1 : ℤ)) node1331 ++
      ([])) = [] := by
  decide +kernel

theorem node1331_mem : rowEval varIndex node1331 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1331Raw node1331 ([])
    (1) (1) (by decide) node1331_check
  · rw [node1331Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0100_mem
  · exact candidateIdeal.zero_mem

def node1335 : WordRow := [([0, 3, 13, 16], 1), ([1, 2, 13, 16], 1)]

def node1335Raw : WordRow := multiplyRow 16 node0101

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1335_check :
    collect (scaleRow 1 node1335Raw ++ scaleRow (-(1 : ℤ)) node1335 ++
      ([])) = [] := by
  decide +kernel

theorem node1335_mem : rowEval varIndex node1335 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1335Raw node1335 ([])
    (1) (1) (by decide) node1335_check
  · rw [node1335Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0101_mem
  · exact candidateIdeal.zero_mem

def node1339 : WordRow := [([0, 3, 14, 16], 1), ([1, 2, 14, 16], 1)]

def node1339Raw : WordRow := multiplyRow 16 node0102

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1339_check :
    collect (scaleRow 1 node1339Raw ++ scaleRow (-(1 : ℤ)) node1339 ++
      ([])) = [] := by
  decide +kernel

theorem node1339_mem : rowEval varIndex node1339 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1339Raw node1339 ([])
    (1) (1) (by decide) node1339_check
  · rw [node1339Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0102_mem
  · exact candidateIdeal.zero_mem

def node1345 : WordRow := [([0, 3, 16, 17], 1), ([1, 2, 16, 17], 1)]

def node1345Raw : WordRow := multiplyRow 17 node0104

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1345_check :
    collect (scaleRow 1 node1345Raw ++ scaleRow (-(1 : ℤ)) node1345 ++
      ([])) = [] := by
  decide +kernel

theorem node1345_mem : rowEval varIndex node1345 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1345Raw node1345 ([])
    (1) (1) (by decide) node1345_check
  · rw [node1345Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0104_mem
  · exact candidateIdeal.zero_mem

def node1491 : WordRow := [([0, 0, 5, 10], 1), ([0, 1, 4, 10], 1)]

def node1491Raw : WordRow := multiplyRow 10 node0122

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1491_check :
    collect (scaleRow 1 node1491Raw ++ scaleRow (-(1 : ℤ)) node1491 ++
      ([])) = [] := by
  decide +kernel

theorem node1491_mem : rowEval varIndex node1491 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1491Raw node1491 ([])
    (1) (1) (by decide) node1491_check
  · rw [node1491Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0122_mem
  · exact candidateIdeal.zero_mem

def node1503 : WordRow := [([0, 2, 5, 6], 1), ([1, 2, 4, 6], 1)]

def node1503Raw : WordRow := multiplyRow 6 node0123

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1503_check :
    collect (scaleRow 1 node1503Raw ++ scaleRow (-(1 : ℤ)) node1503 ++
      ([])) = [] := by
  decide +kernel

theorem node1503_mem : rowEval varIndex node1503 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1503Raw node1503 ([])
    (1) (1) (by decide) node1503_check
  · rw [node1503Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0123_mem
  · exact candidateIdeal.zero_mem

def node1507 : WordRow := [([0, 2, 5, 10], 1), ([1, 2, 4, 10], 1)]

def node1507Raw : WordRow := multiplyRow 10 node0123

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1507_check :
    collect (scaleRow 1 node1507Raw ++ scaleRow (-(1 : ℤ)) node1507 ++
      ([])) = [] := by
  decide +kernel

theorem node1507_mem : rowEval varIndex node1507 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1507Raw node1507 ([])
    (1) (1) (by decide) node1507_check
  · rw [node1507Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0123_mem
  · exact candidateIdeal.zero_mem

def node1514 : WordRow := [([0, 2, 5, 17], 1), ([1, 2, 4, 17], 1)]

def node1514Raw : WordRow := multiplyRow 17 node0123

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1514_check :
    collect (scaleRow 1 node1514Raw ++ scaleRow (-(1 : ℤ)) node1514 ++
      ([])) = [] := by
  decide +kernel

theorem node1514_mem : rowEval varIndex node1514 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1514Raw node1514 ([])
    (1) (1) (by decide) node1514_check
  · rw [node1514Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0123_mem
  · exact candidateIdeal.zero_mem

def node1535 : WordRow := [([0, 4, 5, 10], 1), ([1, 4, 4, 10], 1)]

def node1535Raw : WordRow := multiplyRow 10 node0125

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1535_check :
    collect (scaleRow 1 node1535Raw ++ scaleRow (-(1 : ℤ)) node1535 ++
      ([])) = [] := by
  decide +kernel

theorem node1535_mem : rowEval varIndex node1535 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1535Raw node1535 ([])
    (1) (1) (by decide) node1535_check
  · rw [node1535Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0125_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node1535_mem
