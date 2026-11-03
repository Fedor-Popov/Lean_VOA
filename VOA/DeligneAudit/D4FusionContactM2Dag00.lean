import VOA.DeligneAudit.D4FusionContactM2Images

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node0000 : WordRow := [([0, 1], 1)]

def node0000Raw : WordRow := [(seedWords 1,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0000_check :
    collect (scaleRow 1 node0000Raw ++ scaleRow (-(1 : ℤ)) node0000 ++
      ([])) = [] := by
  decide +kernel

theorem node0000_mem : rowEval varIndex node0000 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0000Raw node0000 ([])
    (1) (1) (by decide) node0000_check
  · exact seedWord_mem 1
  · exact candidateIdeal.zero_mem

def node0001 : WordRow := [([1, 1], 1)]

def node0001Raw : WordRow := [(seedWords 2,1)]

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0001_check :
    collect (scaleRow 1 node0001Raw ++ scaleRow (-(1 : ℤ)) node0001 ++
      ([])) = [] := by
  decide +kernel

theorem node0001_mem : rowEval varIndex node0001 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0001Raw node0001 ([])
    (1) (1) (by decide) node0001_check
  · exact seedWord_mem 2
  · exact candidateIdeal.zero_mem

def node0002 : WordRow := [([0, 3], 1), ([1, 2], 1)]

def node0002Raw : WordRow := differentiateRow (images 14) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0002_check :
    collect (scaleRow 1 node0002Raw ++ scaleRow (-(1 : ℤ)) node0002 ++
      ([])) = [] := by
  decide +kernel

theorem node0002_mem : rowEval varIndex node0002 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0002Raw node0002 ([])
    (1) (1) (by decide) node0002_check
  · rw [node0002Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0003 : WordRow := [([1, 3], 1)]

def node0003Raw : WordRow := differentiateRow (images 15) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0003_check :
    collect (scaleRow 1 node0003Raw ++ scaleRow (-(1 : ℤ)) node0003 ++
      ([])) = [] := by
  decide +kernel

theorem node0003_mem : rowEval varIndex node0003 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0003Raw node0003 ([])
    (1) (1) (by decide) node0003_check
  · rw [node0003Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0004 : WordRow := [([0, 5], 1), ([1, 4], 1)]

def node0004Raw : WordRow := differentiateRow (images 16) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0004_check :
    collect (scaleRow 1 node0004Raw ++ scaleRow (-(1 : ℤ)) node0004 ++
      ([])) = [] := by
  decide +kernel

theorem node0004_mem : rowEval varIndex node0004 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0004Raw node0004 ([])
    (1) (1) (by decide) node0004_check
  · rw [node0004Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0005 : WordRow := [([1, 5], 1)]

def node0005Raw : WordRow := differentiateRow (images 17) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0005_check :
    collect (scaleRow 1 node0005Raw ++ scaleRow (-(1 : ℤ)) node0005 ++
      ([])) = [] := by
  decide +kernel

theorem node0005_mem : rowEval varIndex node0005 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0005Raw node0005 ([])
    (1) (1) (by decide) node0005_check
  · rw [node0005Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0006 : WordRow := [([0, 7], 1), ([1, 6], 1)]

def node0006Raw : WordRow := differentiateRow (images 18) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0006_check :
    collect (scaleRow 1 node0006Raw ++ scaleRow (-(-1 : ℤ)) node0006 ++
      ([])) = [] := by
  decide +kernel

theorem node0006_mem : rowEval varIndex node0006 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0006Raw node0006 ([])
    (1) (-1) (by decide) node0006_check
  · rw [node0006Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0007 : WordRow := [([1, 7], 1)]

def node0007Raw : WordRow := differentiateRow (images 19) node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0007_check :
    collect (scaleRow 1 node0007Raw ++ scaleRow (-(-1 : ℤ)) node0007 ++
      ([])) = [] := by
  decide +kernel

theorem node0007_mem : rowEval varIndex node0007 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0007Raw node0007 ([])
    (1) (-1) (by decide) node0007_check
  · rw [node0007Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0008 : WordRow := [([2, 3], 1)]

def node0008Raw : WordRow := differentiateRow (images 14) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0008_check :
    collect (scaleRow 1 node0008Raw ++ scaleRow (-(2 : ℤ)) node0008 ++
      ([])) = [] := by
  decide +kernel

theorem node0008_mem : rowEval varIndex node0008 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0008Raw node0008 ([])
    (1) (2) (by decide) node0008_check
  · rw [node0008Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0009 : WordRow := [([3, 3], 1)]

def node0009Raw : WordRow := differentiateRow (images 15) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0009_check :
    collect (scaleRow 1 node0009Raw ++ scaleRow (-(1 : ℤ)) node0009 ++
      ([])) = [] := by
  decide +kernel

theorem node0009_mem : rowEval varIndex node0009 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0009Raw node0009 ([])
    (1) (1) (by decide) node0009_check
  · rw [node0009Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0010 : WordRow := [([0, 9], 1), ([1, 8], 1), ([2, 5], -1), ([3, 4], -1)]

def node0010Raw : WordRow := differentiateRow (images 16) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0010_check :
    collect (scaleRow 1 node0010Raw ++ scaleRow (-(-1 : ℤ)) node0010 ++
      ([])) = [] := by
  decide +kernel

theorem node0010_mem : rowEval varIndex node0010 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0010Raw node0010 ([])
    (1) (-1) (by decide) node0010_check
  · rw [node0010Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0011 : WordRow := [([1, 9], 1), ([3, 5], -1)]

def node0011Raw : WordRow := differentiateRow (images 17) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0011_check :
    collect (scaleRow 1 node0011Raw ++ scaleRow (-(-1 : ℤ)) node0011 ++
      ([])) = [] := by
  decide +kernel

theorem node0011_mem : rowEval varIndex node0011 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0011Raw node0011 ([])
    (1) (-1) (by decide) node0011_check
  · rw [node0011Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0012 : WordRow := [([0, 11], 1), ([1, 10], 1), ([2, 7], -1), ([3, 6], -1)]

def node0012Raw : WordRow := differentiateRow (images 18) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0012_check :
    collect (scaleRow 1 node0012Raw ++ scaleRow (-(1 : ℤ)) node0012 ++
      ([])) = [] := by
  decide +kernel

theorem node0012_mem : rowEval varIndex node0012 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0012Raw node0012 ([])
    (1) (1) (by decide) node0012_check
  · rw [node0012Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0013 : WordRow := [([1, 11], 1), ([3, 7], -1)]

def node0013Raw : WordRow := differentiateRow (images 19) node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0013_check :
    collect (scaleRow 1 node0013Raw ++ scaleRow (-(1 : ℤ)) node0013 ++
      ([])) = [] := by
  decide +kernel

theorem node0013_mem : rowEval varIndex node0013 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0013Raw node0013 ([])
    (1) (1) (by decide) node0013_check
  · rw [node0013Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0014 : WordRow := [([4, 5], 1)]

def node0014Raw : WordRow := differentiateRow (images 16) node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0014_check :
    collect (scaleRow 1 node0014Raw ++ scaleRow (-(2 : ℤ)) node0014 ++
      ([])) = [] := by
  decide +kernel

theorem node0014_mem : rowEval varIndex node0014 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0014Raw node0014 ([])
    (1) (2) (by decide) node0014_check
  · rw [node0014Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0015 : WordRow := [([5, 5], 1)]

def node0015Raw : WordRow := differentiateRow (images 17) node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0015_check :
    collect (scaleRow 1 node0015Raw ++ scaleRow (-(1 : ℤ)) node0015 ++
      ([])) = [] := by
  decide +kernel

theorem node0015_mem : rowEval varIndex node0015 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0015Raw node0015 ([])
    (1) (1) (by decide) node0015_check
  · rw [node0015Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0016 : WordRow := [([0, 13], 1), ([1, 12], 1), ([4, 7], -1), ([5, 6], -1)]

def node0016Raw : WordRow := differentiateRow (images 18) node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0016_check :
    collect (scaleRow 1 node0016Raw ++ scaleRow (-(1 : ℤ)) node0016 ++
      ([])) = [] := by
  decide +kernel

theorem node0016_mem : rowEval varIndex node0016 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0016Raw node0016 ([])
    (1) (1) (by decide) node0016_check
  · rw [node0016Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0017 : WordRow := [([1, 13], 1), ([5, 7], -1)]

def node0017Raw : WordRow := differentiateRow (images 19) node0004

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0017_check :
    collect (scaleRow 1 node0017Raw ++ scaleRow (-(1 : ℤ)) node0017 ++
      ([])) = [] := by
  decide +kernel

theorem node0017_mem : rowEval varIndex node0017 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0017Raw node0017 ([])
    (1) (1) (by decide) node0017_check
  · rw [node0017Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0004_mem
  · exact candidateIdeal.zero_mem

def node0018 : WordRow := [([6, 7], 1)]

def node0018Raw : WordRow := differentiateRow (images 18) node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0018_check :
    collect (scaleRow 1 node0018Raw ++ scaleRow (-(-2 : ℤ)) node0018 ++
      ([])) = [] := by
  decide +kernel

theorem node0018_mem : rowEval varIndex node0018 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0018Raw node0018 ([])
    (1) (-2) (by decide) node0018_check
  · rw [node0018Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0019 : WordRow := [([7, 7], 1)]

def node0019Raw : WordRow := differentiateRow (images 19) node0006

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0019_check :
    collect (scaleRow 1 node0019Raw ++ scaleRow (-(-1 : ℤ)) node0019 ++
      ([])) = [] := by
  decide +kernel

theorem node0019_mem : rowEval varIndex node0019 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0019Raw node0019 ([])
    (1) (-1) (by decide) node0019_check
  · rw [node0019Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0006_mem
  · exact candidateIdeal.zero_mem

def node0020 : WordRow := [([2, 9], 1), ([3, 8], 1)]

def node0020Raw : WordRow := differentiateRow (images 16) node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0020_check :
    collect (scaleRow 1 node0020Raw ++ scaleRow (-(-1 : ℤ)) node0020 ++
      ([])) = [] := by
  decide +kernel

theorem node0020_mem : rowEval varIndex node0020 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0020Raw node0020 ([])
    (1) (-1) (by decide) node0020_check
  · rw [node0020Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0021 : WordRow := [([3, 9], 1)]

def node0021Raw : WordRow := differentiateRow (images 17) node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0021_check :
    collect (scaleRow 1 node0021Raw ++ scaleRow (-(-1 : ℤ)) node0021 ++
      ([])) = [] := by
  decide +kernel

theorem node0021_mem : rowEval varIndex node0021 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0021Raw node0021 ([])
    (1) (-1) (by decide) node0021_check
  · rw [node0021Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0022 : WordRow := [([2, 11], 1), ([3, 10], 1)]

def node0022Raw : WordRow := differentiateRow (images 18) node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0022_check :
    collect (scaleRow 1 node0022Raw ++ scaleRow (-(1 : ℤ)) node0022 ++
      ([])) = [] := by
  decide +kernel

theorem node0022_mem : rowEval varIndex node0022 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0022Raw node0022 ([])
    (1) (1) (by decide) node0022_check
  · rw [node0022Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0023 : WordRow := [([3, 11], 1)]

def node0023Raw : WordRow := differentiateRow (images 19) node0008

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0023_check :
    collect (scaleRow 1 node0023Raw ++ scaleRow (-(1 : ℤ)) node0023 ++
      ([])) = [] := by
  decide +kernel

theorem node0023_mem : rowEval varIndex node0023 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0023Raw node0023 ([])
    (1) (1) (by decide) node0023_check
  · rw [node0023Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0008_mem
  · exact candidateIdeal.zero_mem

def node0024 : WordRow := [([4, 9], 1), ([5, 8], 1)]

def node0024Raw : WordRow := differentiateRow (images 16) node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0024_check :
    collect (scaleRow 1 node0024Raw ++ scaleRow (-(2 : ℤ)) node0024 ++
      ([])) = [] := by
  decide +kernel

theorem node0024_mem : rowEval varIndex node0024 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0024Raw node0024 ([])
    (1) (2) (by decide) node0024_check
  · rw [node0024Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0025 : WordRow := [([5, 9], 1)]

def node0025Raw : WordRow := differentiateRow (images 17) node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0025_check :
    collect (scaleRow 1 node0025Raw ++ scaleRow (-(2 : ℤ)) node0025 ++
      ([])) = [] := by
  decide +kernel

theorem node0025_mem : rowEval varIndex node0025 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0025Raw node0025 ([])
    (1) (2) (by decide) node0025_check
  · rw [node0025Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0026 : WordRow := [([0, 15], 1), ([1, 14], 1), ([2, 13], -1), ([3, 12], -1), ([4, 11], -1), ([5, 10], -1), ([6, 9], -1), ([7, 8], -1)]

def node0026Raw : WordRow := differentiateRow (images 18) node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0026_check :
    collect (scaleRow 1 node0026Raw ++ scaleRow (-(1 : ℤ)) node0026 ++
      ([])) = [] := by
  decide +kernel

theorem node0026_mem : rowEval varIndex node0026 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0026Raw node0026 ([])
    (1) (1) (by decide) node0026_check
  · rw [node0026Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0027 : WordRow := [([1, 15], 1), ([3, 13], -1), ([5, 11], -1), ([7, 9], -1)]

def node0027Raw : WordRow := differentiateRow (images 19) node0010

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0027_check :
    collect (scaleRow 1 node0027Raw ++ scaleRow (-(1 : ℤ)) node0027 ++
      ([])) = [] := by
  decide +kernel

theorem node0027_mem : rowEval varIndex node0027 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0027Raw node0027 ([])
    (1) (1) (by decide) node0027_check
  · rw [node0027Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0010_mem
  · exact candidateIdeal.zero_mem

def node0028 : WordRow := [([6, 11], 1), ([7, 10], 1)]

def node0028Raw : WordRow := differentiateRow (images 18) node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0028_check :
    collect (scaleRow 1 node0028Raw ++ scaleRow (-(-2 : ℤ)) node0028 ++
      ([])) = [] := by
  decide +kernel

theorem node0028_mem : rowEval varIndex node0028 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0028Raw node0028 ([])
    (1) (-2) (by decide) node0028_check
  · rw [node0028Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0029 : WordRow := [([7, 11], 1)]

def node0029Raw : WordRow := differentiateRow (images 19) node0012

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0029_check :
    collect (scaleRow 1 node0029Raw ++ scaleRow (-(-2 : ℤ)) node0029 ++
      ([])) = [] := by
  decide +kernel

theorem node0029_mem : rowEval varIndex node0029 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0029Raw node0029 ([])
    (1) (-2) (by decide) node0029_check
  · rw [node0029Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0012_mem
  · exact candidateIdeal.zero_mem

def node0030 : WordRow := [([4, 13], 1), ([5, 12], 1)]

def node0030Raw : WordRow := differentiateRow (images 18) node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0030_check :
    collect (scaleRow 1 node0030Raw ++ scaleRow (-(1 : ℤ)) node0030 ++
      ([])) = [] := by
  decide +kernel

theorem node0030_mem : rowEval varIndex node0030 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0030Raw node0030 ([])
    (1) (1) (by decide) node0030_check
  · rw [node0030Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0031 : WordRow := [([5, 13], 1)]

def node0031Raw : WordRow := differentiateRow (images 19) node0014

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0031_check :
    collect (scaleRow 1 node0031Raw ++ scaleRow (-(1 : ℤ)) node0031 ++
      ([])) = [] := by
  decide +kernel

theorem node0031_mem : rowEval varIndex node0031 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0031Raw node0031 ([])
    (1) (1) (by decide) node0031_check
  · rw [node0031Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0014_mem
  · exact candidateIdeal.zero_mem

def node0032 : WordRow := [([6, 13], 1), ([7, 12], 1)]

def node0032Raw : WordRow := differentiateRow (images 18) node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0032_check :
    collect (scaleRow 1 node0032Raw ++ scaleRow (-(-2 : ℤ)) node0032 ++
      ([])) = [] := by
  decide +kernel

theorem node0032_mem : rowEval varIndex node0032 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0032Raw node0032 ([])
    (1) (-2) (by decide) node0032_check
  · rw [node0032Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0033 : WordRow := [([7, 13], 1)]

def node0033Raw : WordRow := differentiateRow (images 19) node0016

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0033_check :
    collect (scaleRow 1 node0033Raw ++ scaleRow (-(-2 : ℤ)) node0033 ++
      ([])) = [] := by
  decide +kernel

theorem node0033_mem : rowEval varIndex node0033 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0033Raw node0033 ([])
    (1) (-2) (by decide) node0033_check
  · rw [node0033Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0016_mem
  · exact candidateIdeal.zero_mem

def node0034 : WordRow := [([8, 9], 1)]

def node0034Raw : WordRow := differentiateRow (images 16) node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0034_check :
    collect (scaleRow 1 node0034Raw ++ scaleRow (-(-2 : ℤ)) node0034 ++
      ([])) = [] := by
  decide +kernel

theorem node0034_mem : rowEval varIndex node0034 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0034Raw node0034 ([])
    (1) (-2) (by decide) node0034_check
  · rw [node0034Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0035 : WordRow := [([9, 9], 1)]

def node0035Raw : WordRow := differentiateRow (images 17) node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0035_check :
    collect (scaleRow 1 node0035Raw ++ scaleRow (-(-1 : ℤ)) node0035 ++
      ([])) = [] := by
  decide +kernel

theorem node0035_mem : rowEval varIndex node0035 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0035Raw node0035 ([])
    (1) (-1) (by decide) node0035_check
  · rw [node0035Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0036 : WordRow := [([2, 15], 1), ([3, 14], 1), ([8, 11], 1), ([9, 10], 1)]

def node0036Raw : WordRow := differentiateRow (images 18) node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0036_check :
    collect (scaleRow 1 node0036Raw ++ scaleRow (-(1 : ℤ)) node0036 ++
      ([])) = [] := by
  decide +kernel

theorem node0036_mem : rowEval varIndex node0036 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0036Raw node0036 ([])
    (1) (1) (by decide) node0036_check
  · rw [node0036Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0037 : WordRow := [([3, 15], 1), ([9, 11], 1)]

def node0037Raw : WordRow := differentiateRow (images 19) node0020

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0037_check :
    collect (scaleRow 1 node0037Raw ++ scaleRow (-(1 : ℤ)) node0037 ++
      ([])) = [] := by
  decide +kernel

theorem node0037_mem : rowEval varIndex node0037 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0037Raw node0037 ([])
    (1) (1) (by decide) node0037_check
  · rw [node0037Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0020_mem
  · exact candidateIdeal.zero_mem

def node0038 : WordRow := [([10, 11], 1)]

def node0038Raw : WordRow := differentiateRow (images 18) node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0038_check :
    collect (scaleRow 1 node0038Raw ++ scaleRow (-(2 : ℤ)) node0038 ++
      ([])) = [] := by
  decide +kernel

theorem node0038_mem : rowEval varIndex node0038 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0038Raw node0038 ([])
    (1) (2) (by decide) node0038_check
  · rw [node0038Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0039 : WordRow := [([11, 11], 1)]

def node0039Raw : WordRow := differentiateRow (images 19) node0022

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0039_check :
    collect (scaleRow 1 node0039Raw ++ scaleRow (-(1 : ℤ)) node0039 ++
      ([])) = [] := by
  decide +kernel

theorem node0039_mem : rowEval varIndex node0039 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0039Raw node0039 ([])
    (1) (1) (by decide) node0039_check
  · rw [node0039Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0022_mem
  · exact candidateIdeal.zero_mem

def node0040 : WordRow := [([4, 15], 1), ([5, 14], 1), ([8, 13], 1), ([9, 12], 1)]

def node0040Raw : WordRow := differentiateRow (images 18) node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0040_check :
    collect (scaleRow 1 node0040Raw ++ scaleRow (-(1 : ℤ)) node0040 ++
      ([])) = [] := by
  decide +kernel

theorem node0040_mem : rowEval varIndex node0040 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0040Raw node0040 ([])
    (1) (1) (by decide) node0040_check
  · rw [node0040Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0041 : WordRow := [([5, 15], 1), ([9, 13], 1)]

def node0041Raw : WordRow := differentiateRow (images 19) node0024

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0041_check :
    collect (scaleRow 1 node0041Raw ++ scaleRow (-(1 : ℤ)) node0041 ++
      ([])) = [] := by
  decide +kernel

theorem node0041_mem : rowEval varIndex node0041 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0041Raw node0041 ([])
    (1) (1) (by decide) node0041_check
  · rw [node0041Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0024_mem
  · exact candidateIdeal.zero_mem

def node0042 : WordRow := [([6, 15], 1), ([7, 14], 1), ([10, 13], 1), ([11, 12], 1)]

def node0042Raw : WordRow := differentiateRow (images 18) node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0042_check :
    collect (scaleRow 1 node0042Raw ++ scaleRow (-(-2 : ℤ)) node0042 ++
      ([])) = [] := by
  decide +kernel

theorem node0042_mem : rowEval varIndex node0042 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0042Raw node0042 ([])
    (1) (-2) (by decide) node0042_check
  · rw [node0042Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0043 : WordRow := [([7, 15], 1), ([11, 13], 1)]

def node0043Raw : WordRow := differentiateRow (images 19) node0026

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0043_check :
    collect (scaleRow 1 node0043Raw ++ scaleRow (-(-2 : ℤ)) node0043 ++
      ([])) = [] := by
  decide +kernel

theorem node0043_mem : rowEval varIndex node0043 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0043Raw node0043 ([])
    (1) (-2) (by decide) node0043_check
  · rw [node0043Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0026_mem
  · exact candidateIdeal.zero_mem

def node0044 : WordRow := [([12, 13], 1)]

def node0044Raw : WordRow := differentiateRow (images 18) node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0044_check :
    collect (scaleRow 1 node0044Raw ++ scaleRow (-(2 : ℤ)) node0044 ++
      ([])) = [] := by
  decide +kernel

theorem node0044_mem : rowEval varIndex node0044 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0044Raw node0044 ([])
    (1) (2) (by decide) node0044_check
  · rw [node0044Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0045 : WordRow := [([13, 13], 1)]

def node0045Raw : WordRow := differentiateRow (images 19) node0030

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0045_check :
    collect (scaleRow 1 node0045Raw ++ scaleRow (-(1 : ℤ)) node0045 ++
      ([])) = [] := by
  decide +kernel

theorem node0045_mem : rowEval varIndex node0045 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0045Raw node0045 ([])
    (1) (1) (by decide) node0045_check
  · rw [node0045Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0030_mem
  · exact candidateIdeal.zero_mem

def node0046 : WordRow := [([8, 15], 1), ([9, 14], 1)]

def node0046Raw : WordRow := differentiateRow (images 18) node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0046_check :
    collect (scaleRow 1 node0046Raw ++ scaleRow (-(1 : ℤ)) node0046 ++
      ([])) = [] := by
  decide +kernel

theorem node0046_mem : rowEval varIndex node0046 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0046Raw node0046 ([])
    (1) (1) (by decide) node0046_check
  · rw [node0046Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0034_mem
  · exact candidateIdeal.zero_mem

def node0047 : WordRow := [([9, 15], 1)]

def node0047Raw : WordRow := differentiateRow (images 19) node0034

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0047_check :
    collect (scaleRow 1 node0047Raw ++ scaleRow (-(1 : ℤ)) node0047 ++
      ([])) = [] := by
  decide +kernel

theorem node0047_mem : rowEval varIndex node0047 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0047Raw node0047 ([])
    (1) (1) (by decide) node0047_check
  · rw [node0047Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0034_mem
  · exact candidateIdeal.zero_mem

def node0048 : WordRow := [([10, 15], 1), ([11, 14], 1)]

def node0048Raw : WordRow := differentiateRow (images 18) node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0048_check :
    collect (scaleRow 1 node0048Raw ++ scaleRow (-(2 : ℤ)) node0048 ++
      ([])) = [] := by
  decide +kernel

theorem node0048_mem : rowEval varIndex node0048 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0048Raw node0048 ([])
    (1) (2) (by decide) node0048_check
  · rw [node0048Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0049 : WordRow := [([11, 15], 1)]

def node0049Raw : WordRow := differentiateRow (images 19) node0036

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0049_check :
    collect (scaleRow 1 node0049Raw ++ scaleRow (-(2 : ℤ)) node0049 ++
      ([])) = [] := by
  decide +kernel

theorem node0049_mem : rowEval varIndex node0049 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0049Raw node0049 ([])
    (1) (2) (by decide) node0049_check
  · rw [node0049Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0036_mem
  · exact candidateIdeal.zero_mem

def node0050 : WordRow := [([12, 15], 1), ([13, 14], 1)]

def node0050Raw : WordRow := differentiateRow (images 18) node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0050_check :
    collect (scaleRow 1 node0050Raw ++ scaleRow (-(2 : ℤ)) node0050 ++
      ([])) = [] := by
  decide +kernel

theorem node0050_mem : rowEval varIndex node0050 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0050Raw node0050 ([])
    (1) (2) (by decide) node0050_check
  · rw [node0050Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0051 : WordRow := [([13, 15], 1)]

def node0051Raw : WordRow := differentiateRow (images 19) node0040

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0051_check :
    collect (scaleRow 1 node0051Raw ++ scaleRow (-(2 : ℤ)) node0051 ++
      ([])) = [] := by
  decide +kernel

theorem node0051_mem : rowEval varIndex node0051 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0051Raw node0051 ([])
    (1) (2) (by decide) node0051_check
  · rw [node0051Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0040_mem
  · exact candidateIdeal.zero_mem

def node0052 : WordRow := [([14, 15], 1)]

def node0052Raw : WordRow := differentiateRow (images 18) node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0052_check :
    collect (scaleRow 1 node0052Raw ++ scaleRow (-(2 : ℤ)) node0052 ++
      ([])) = [] := by
  decide +kernel

theorem node0052_mem : rowEval varIndex node0052 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0052Raw node0052 ([])
    (1) (2) (by decide) node0052_check
  · rw [node0052Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0053 : WordRow := [([15, 15], 1)]

def node0053Raw : WordRow := differentiateRow (images 19) node0046

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0053_check :
    collect (scaleRow 1 node0053Raw ++ scaleRow (-(1 : ℤ)) node0053 ++
      ([])) = [] := by
  decide +kernel

theorem node0053_mem : rowEval varIndex node0053 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0053Raw node0053 ([])
    (1) (1) (by decide) node0053_check
  · rw [node0053Raw,rowEval_images]
    exact candidateIdeal_deriv _ node0046_mem
  · exact candidateIdeal.zero_mem

def node0054 : WordRow := [([0, 0, 1], 1)]

def node0054Raw : WordRow := multiplyRow 0 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0054_check :
    collect (scaleRow 1 node0054Raw ++ scaleRow (-(1 : ℤ)) node0054 ++
      ([])) = [] := by
  decide +kernel

theorem node0054_mem : rowEval varIndex node0054 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0054Raw node0054 ([])
    (1) (1) (by decide) node0054_check
  · rw [node0054Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0056 : WordRow := [([0, 1, 2], 1)]

def node0056Raw : WordRow := multiplyRow 2 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0056_check :
    collect (scaleRow 1 node0056Raw ++ scaleRow (-(1 : ℤ)) node0056 ++
      ([])) = [] := by
  decide +kernel

theorem node0056_mem : rowEval varIndex node0056 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0056Raw node0056 ([])
    (1) (1) (by decide) node0056_check
  · rw [node0056Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0058 : WordRow := [([0, 1, 4], 1)]

def node0058Raw : WordRow := multiplyRow 4 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0058_check :
    collect (scaleRow 1 node0058Raw ++ scaleRow (-(1 : ℤ)) node0058 ++
      ([])) = [] := by
  decide +kernel

theorem node0058_mem : rowEval varIndex node0058 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0058Raw node0058 ([])
    (1) (1) (by decide) node0058_check
  · rw [node0058Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0060 : WordRow := [([0, 1, 6], 1)]

def node0060Raw : WordRow := multiplyRow 6 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0060_check :
    collect (scaleRow 1 node0060Raw ++ scaleRow (-(1 : ℤ)) node0060 ++
      ([])) = [] := by
  decide +kernel

theorem node0060_mem : rowEval varIndex node0060 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0060Raw node0060 ([])
    (1) (1) (by decide) node0060_check
  · rw [node0060Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0062 : WordRow := [([0, 1, 8], 1)]

def node0062Raw : WordRow := multiplyRow 8 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0062_check :
    collect (scaleRow 1 node0062Raw ++ scaleRow (-(1 : ℤ)) node0062 ++
      ([])) = [] := by
  decide +kernel

theorem node0062_mem : rowEval varIndex node0062 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0062Raw node0062 ([])
    (1) (1) (by decide) node0062_check
  · rw [node0062Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0064 : WordRow := [([0, 1, 10], 1)]

def node0064Raw : WordRow := multiplyRow 10 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0064_check :
    collect (scaleRow 1 node0064Raw ++ scaleRow (-(1 : ℤ)) node0064 ++
      ([])) = [] := by
  decide +kernel

theorem node0064_mem : rowEval varIndex node0064 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0064Raw node0064 ([])
    (1) (1) (by decide) node0064_check
  · rw [node0064Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0066 : WordRow := [([0, 1, 12], 1)]

def node0066Raw : WordRow := multiplyRow 12 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0066_check :
    collect (scaleRow 1 node0066Raw ++ scaleRow (-(1 : ℤ)) node0066 ++
      ([])) = [] := by
  decide +kernel

theorem node0066_mem : rowEval varIndex node0066 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0066Raw node0066 ([])
    (1) (1) (by decide) node0066_check
  · rw [node0066Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0068 : WordRow := [([0, 1, 14], 1)]

def node0068Raw : WordRow := multiplyRow 14 node0000

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0068_check :
    collect (scaleRow 1 node0068Raw ++ scaleRow (-(1 : ℤ)) node0068 ++
      ([])) = [] := by
  decide +kernel

theorem node0068_mem : rowEval varIndex node0068 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0068Raw node0068 ([])
    (1) (1) (by decide) node0068_check
  · rw [node0068Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0000_mem
  · exact candidateIdeal.zero_mem

def node0089 : WordRow := [([0, 0, 3], 1), ([0, 1, 2], 1)]

def node0089Raw : WordRow := multiplyRow 0 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0089_check :
    collect (scaleRow 1 node0089Raw ++ scaleRow (-(1 : ℤ)) node0089 ++
      ([])) = [] := by
  decide +kernel

theorem node0089_mem : rowEval varIndex node0089 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0089Raw node0089 ([])
    (1) (1) (by decide) node0089_check
  · rw [node0089Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

def node0090 : WordRow := [([0, 2, 3], 1), ([1, 2, 2], 1)]

def node0090Raw : WordRow := multiplyRow 2 node0002

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node0090_check :
    collect (scaleRow 1 node0090Raw ++ scaleRow (-(1 : ℤ)) node0090 ++
      ([])) = [] := by
  decide +kernel

theorem node0090_mem : rowEval varIndex node0090 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node0090Raw node0090 ([])
    (1) (1) (by decide) node0090_check
  · rw [node0090Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0002_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node0090_mem
