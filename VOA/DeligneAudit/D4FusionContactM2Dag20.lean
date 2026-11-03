import VOA.DeligneAudit.D4FusionContactM2Dag19

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node6495 : WordRow := [([2, 6, 10, 17], 2), ([2, 7, 10, 16], 1), ([3, 6, 10, 16], 1)]

def node6495Raw : WordRow := differentiateRow (images 30) node6444

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6495_check :
    collect (scaleRow 1 node6495Raw ++ scaleRow (-(2 : ℤ)) node6495 ++
      (scaleRow (-2) node6198 ++ scaleRow (-4) node2596 ++ scaleRow (2) node4927)) = [] := by
  decide +kernel

theorem node6495_mem : rowEval varIndex node6495 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6495Raw node6495 (scaleRow (-2) node6198 ++ scaleRow (-4) node2596 ++ scaleRow (2) node4927)
    (1) (2) (by decide) node6495_check
  · rw [node6495Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6444_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6198 node6198_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node2596 node2596_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node4927 node4927_mem)))

def node6496 : WordRow := [([2, 6, 12, 17], 2), ([2, 6, 13, 16], 1), ([2, 7, 12, 16], 1), ([3, 6, 12, 16], 2), ([4, 6, 10, 17], 2), ([4, 6, 11, 16], 1), ([4, 7, 10, 16], 1), ([5, 6, 10, 16], 2), ([6, 6, 8, 17], 1), ([6, 6, 9, 16], 1), ([6, 7, 8, 16], 1)]

def node6496Raw : WordRow := differentiateRow (images 32) node6444

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6496_check :
    collect (scaleRow 1 node6496Raw ++ scaleRow (-(1 : ℤ)) node6496 ++
      (scaleRow (-1) node6490 ++ scaleRow (-2) node3046 ++ scaleRow (-2) node2609 ++ scaleRow (1) node5192)) = [] := by
  decide +kernel

theorem node6496_mem : rowEval varIndex node6496 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6496Raw node6496 (scaleRow (-1) node6490 ++ scaleRow (-2) node3046 ++ scaleRow (-2) node2609 ++ scaleRow (1) node5192)
    (1) (1) (by decide) node6496_check
  · rw [node6496Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6444_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6490 node6490_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3046 node3046_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2609 node2609_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5192 node5192_mem))))

def node6497 : WordRow := [([2, 6, 14, 17], 2), ([2, 7, 14, 16], 1), ([2, 10, 12, 17], 2), ([2, 10, 13, 16], 1), ([3, 6, 14, 16], 1), ([3, 10, 12, 16], 1), ([4, 10, 10, 17], 1), ([4, 10, 11, 16], 1), ([5, 10, 10, 16], 1), ([6, 8, 10, 17], 2), ([6, 9, 10, 16], 1), ([7, 8, 10, 16], 1)]

def node6497Raw : WordRow := differentiateRow (images 34) node6444

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6497_check :
    collect (scaleRow 1 node6497Raw ++ scaleRow (-(1 : ℤ)) node6497 ++
      (scaleRow (-1) node6289 ++ scaleRow (-2) node4039 ++ scaleRow (-2) node2618 ++ scaleRow (1) node5532)) = [] := by
  decide +kernel

theorem node6497_mem : rowEval varIndex node6497 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6497Raw node6497 (scaleRow (-1) node6289 ++ scaleRow (-2) node4039 ++ scaleRow (-2) node2618 ++ scaleRow (1) node5532)
    (1) (1) (by decide) node6497_check
  · rw [node6497Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6444_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6289 node6289_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4039 node4039_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2618 node2618_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5532 node5532_mem))))

def node6498 : WordRow := [([4, 6, 12, 17], 2), ([4, 7, 12, 16], 1), ([5, 6, 12, 16], 1)]

def node6498Raw : WordRow := differentiateRow (images 32) node6445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6498_check :
    collect (scaleRow 1 node6498Raw ++ scaleRow (-(2 : ℤ)) node6498 ++
      (scaleRow (-2) node6241 ++ scaleRow (-4) node3059 ++ scaleRow (2) node5319)) = [] := by
  decide +kernel

theorem node6498_mem : rowEval varIndex node6498 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6498Raw node6498 (scaleRow (-2) node6241 ++ scaleRow (-4) node3059 ++ scaleRow (2) node5319)
    (1) (2) (by decide) node6498_check
  · rw [node6498Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6445_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6241 node6241_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node3059 node3059_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5319 node5319_mem)))

def node6499 : WordRow := [([2, 12, 12, 17], 1), ([2, 12, 13, 16], 1), ([3, 12, 12, 16], 1), ([4, 6, 14, 17], 2), ([4, 7, 14, 16], 1), ([4, 10, 12, 17], 2), ([4, 11, 12, 16], 1), ([5, 6, 14, 16], 1), ([5, 10, 12, 16], 1), ([6, 8, 12, 17], 2), ([6, 9, 12, 16], 1), ([7, 8, 12, 16], 1)]

def node6499Raw : WordRow := differentiateRow (images 34) node6445

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6499_check :
    collect (scaleRow 1 node6499Raw ++ scaleRow (-(1 : ℤ)) node6499 ++
      (scaleRow (-1) node6309 ++ scaleRow (-2) node4052 ++ scaleRow (-2) node3068 ++ scaleRow (1) node5618)) = [] := by
  decide +kernel

theorem node6499_mem : rowEval varIndex node6499 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6499Raw node6499 (scaleRow (-1) node6309 ++ scaleRow (-2) node4052 ++ scaleRow (-2) node3068 ++ scaleRow (1) node5618)
    (1) (1) (by decide) node6499_check
  · rw [node6499Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6445_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6309 node6309_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4052 node4052_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3068 node3068_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5618 node5618_mem))))

def node6500 : WordRow := [([2, 12, 14, 17], 2), ([2, 13, 14, 16], 1), ([3, 12, 14, 16], 1), ([4, 10, 14, 17], 2), ([4, 11, 14, 16], 1), ([5, 10, 14, 16], 1), ([6, 8, 14, 17], 2), ([6, 9, 14, 16], 1), ([7, 8, 14, 16], 1), ([8, 10, 12, 17], 2)]

def node6500Raw : WordRow := differentiateRow (images 34) node6446

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6500_check :
    collect (scaleRow 1 node6500Raw ++ scaleRow (-(2 : ℤ)) node6500 ++
      (scaleRow (-2) node6363 ++ scaleRow (-4) node4061 ++ scaleRow (2) node5687)) = [] := by
  decide +kernel

theorem node6500_mem : rowEval varIndex node6500 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6500Raw node6500 (scaleRow (-2) node6363 ++ scaleRow (-4) node4061 ++ scaleRow (2) node5687)
    (1) (2) (by decide) node6500_check
  · rw [node6500Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6446_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6363 node6363_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node4061 node4061_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5687 node5687_mem)))

def node6501 : WordRow := [([2, 4, 10, 17], 2), ([2, 4, 11, 16], 1), ([2, 5, 10, 16], 2), ([2, 6, 8, 17], 2), ([2, 6, 9, 16], 1), ([2, 7, 8, 16], 2), ([3, 4, 10, 16], 1), ([3, 6, 8, 16], 1)]

def node6501Raw : WordRow := differentiateRow (images 32) node6447

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6501_check :
    collect (scaleRow 1 node6501Raw ++ scaleRow (-(-1 : ℤ)) node6501 ++
      (scaleRow (-1) node6492 ++ scaleRow (-1) node2096)) = [] := by
  decide +kernel

theorem node6501_mem : rowEval varIndex node6501 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6501Raw node6501 (scaleRow (-1) node6492 ++ scaleRow (-1) node2096)
    (1) (-1) (by decide) node6501_check
  · rw [node6501Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6447_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6492 node6492_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2096 node2096_mem))

def node6502 : WordRow := [([2, 8, 10, 17], 2), ([2, 8, 11, 16], 1), ([2, 9, 10, 16], 1)]

def node6502Raw : WordRow := differentiateRow (images 34) node6447

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6502_check :
    collect (scaleRow 1 node6502Raw ++ scaleRow (-(-1 : ℤ)) node6502 ++
      (scaleRow (-1) node6260 ++ scaleRow (-1) node4786 ++ scaleRow (-1) node2105)) = [] := by
  decide +kernel

theorem node6502_mem : rowEval varIndex node6502 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6502Raw node6502 (scaleRow (-1) node6260 ++ scaleRow (-1) node4786 ++ scaleRow (-1) node2105)
    (1) (-1) (by decide) node6502_check
  · rw [node6502Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6447_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6260 node6260_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4786 node4786_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2105 node2105_mem)))

def node6503 : WordRow := [([2, 6, 8, 17], 2), ([2, 6, 9, 16], 1), ([2, 7, 8, 16], 2), ([3, 6, 8, 16], 1)]

def node6503Raw : WordRow := differentiateRow (images 30) node6448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6503_check :
    collect (scaleRow 1 node6503Raw ++ scaleRow (-(-1 : ℤ)) node6503 ++
      (scaleRow (-1) node6501 ++ scaleRow (-1) node3611)) = [] := by
  decide +kernel

theorem node6503_mem : rowEval varIndex node6503 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6503Raw node6503 (scaleRow (-1) node6501 ++ scaleRow (-1) node3611)
    (1) (-1) (by decide) node6503_check
  · rw [node6503Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6448_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6501 node6501_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3611 node3611_mem))

def node6504 : WordRow := [([4, 4, 10, 17], 1), ([4, 4, 11, 16], 1), ([4, 5, 10, 16], 1), ([4, 6, 8, 17], 2), ([4, 6, 9, 16], 1), ([4, 7, 8, 16], 2), ([5, 6, 8, 16], 1)]

def node6504Raw : WordRow := differentiateRow (images 32) node6448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6504_check :
    collect (scaleRow 1 node6504Raw ++ scaleRow (-(-1 : ℤ)) node6504 ++
      (scaleRow (-1) node6493 ++ scaleRow (-1) node4329)) = [] := by
  decide +kernel

theorem node6504_mem : rowEval varIndex node6504 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6504Raw node6504 (scaleRow (-1) node6493 ++ scaleRow (-1) node4329)
    (1) (-1) (by decide) node6504_check
  · rw [node6504Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6448_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6493 node6493_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4329 node4329_mem))

def node6505 : WordRow := [([2, 8, 12, 17], 2), ([2, 8, 13, 16], 2), ([2, 9, 12, 16], 1), ([3, 8, 12, 16], 1), ([4, 8, 10, 17], 2), ([4, 8, 11, 16], 2), ([4, 9, 10, 16], 1), ([5, 8, 10, 16], 1), ([6, 8, 8, 17], 1), ([6, 8, 9, 16], 1), ([7, 8, 8, 16], 1)]

def node6505Raw : WordRow := differentiateRow (images 34) node6448

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6505_check :
    collect (scaleRow 1 node6505Raw ++ scaleRow (-(-1 : ℤ)) node6505 ++
      (scaleRow (-1) node6494 ++ scaleRow (-2) node4798 ++ scaleRow (-1) node5060)) = [] := by
  decide +kernel

theorem node6505_mem : rowEval varIndex node6505 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6505Raw node6505 (scaleRow (-1) node6494 ++ scaleRow (-2) node4798 ++ scaleRow (-1) node5060)
    (1) (-1) (by decide) node6505_check
  · rw [node6505Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6448_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6494 node6494_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4798 node4798_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5060 node5060_mem)))

def node6506 : WordRow := [([4, 6, 10, 17], 2), ([4, 6, 11, 16], 1), ([4, 7, 10, 16], 1), ([5, 6, 10, 16], 2), ([6, 6, 8, 17], 1), ([6, 6, 9, 16], 1), ([6, 7, 8, 16], 1)]

def node6506Raw : WordRow := differentiateRow (images 32) node6449

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6506_check :
    collect (scaleRow 1 node6506Raw ++ scaleRow (-(-1 : ℤ)) node6506 ++
      (scaleRow (-1) node6496 ++ scaleRow (-1) node4488)) = [] := by
  decide +kernel

theorem node6506_mem : rowEval varIndex node6506 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6506Raw node6506 (scaleRow (-1) node6496 ++ scaleRow (-1) node4488)
    (1) (-1) (by decide) node6506_check
  · rw [node6506Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6449_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6496 node6496_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4488 node4488_mem))

def node6507 : WordRow := [([2, 10, 12, 17], 2), ([2, 10, 13, 16], 2), ([2, 11, 12, 16], 1), ([3, 10, 12, 16], 1), ([4, 10, 10, 17], 1), ([4, 10, 11, 16], 1), ([5, 10, 10, 16], 1), ([6, 8, 10, 17], 2), ([6, 8, 11, 16], 1), ([6, 9, 10, 16], 2), ([7, 8, 10, 16], 1)]

def node6507Raw : WordRow := differentiateRow (images 34) node6449

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6507_check :
    collect (scaleRow 1 node6507Raw ++ scaleRow (-(-1 : ℤ)) node6507 ++
      (scaleRow (-1) node6497 ++ scaleRow (-2) node4815 ++ scaleRow (-1) node5204)) = [] := by
  decide +kernel

theorem node6507_mem : rowEval varIndex node6507 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6507Raw node6507 (scaleRow (-1) node6497 ++ scaleRow (-2) node4815 ++ scaleRow (-1) node5204)
    (1) (-1) (by decide) node6507_check
  · rw [node6507Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6449_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6497 node6497_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4815 node4815_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5204 node5204_mem)))

def node6508 : WordRow := [([4, 8, 10, 17], 2), ([4, 8, 11, 16], 2), ([4, 9, 10, 16], 1), ([5, 8, 10, 16], 1), ([6, 8, 8, 17], 1), ([6, 8, 9, 16], 1), ([7, 8, 8, 16], 1)]

def node6508Raw : WordRow := differentiateRow (images 32) node6450

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6508_check :
    collect (scaleRow 1 node6508Raw ++ scaleRow (-(-1 : ℤ)) node6508 ++
      (scaleRow (-1) node6505 ++ scaleRow (-1) node3463)) = [] := by
  decide +kernel

theorem node6508_mem : rowEval varIndex node6508 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6508Raw node6508 (scaleRow (-1) node6505 ++ scaleRow (-1) node3463)
    (1) (-1) (by decide) node6508_check
  · rw [node6508Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6450_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6505 node6505_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3463 node3463_mem))

def node6509 : WordRow := [([8, 8, 10, 17], 1), ([8, 8, 11, 16], 1), ([8, 9, 10, 16], 1)]

def node6509Raw : WordRow := differentiateRow (images 34) node6450

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6509_check :
    collect (scaleRow 1 node6509Raw ++ scaleRow (-(-1 : ℤ)) node6509 ++
      (scaleRow (-1) node6338 ++ scaleRow (-2) node4828 ++ scaleRow (-2) node3472 ++ scaleRow (1) node5424)) = [] := by
  decide +kernel

theorem node6509_mem : rowEval varIndex node6509 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6509Raw node6509 (scaleRow (-1) node6338 ++ scaleRow (-2) node4828 ++ scaleRow (-2) node3472 ++ scaleRow (1) node5424)
    (1) (-1) (by decide) node6509_check
  · rw [node6509Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6450_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6338 node6338_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4828 node4828_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3472 node3472_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5424 node5424_mem))))

def node6510 : WordRow := [([4, 10, 10, 17], 1), ([4, 10, 11, 16], 1), ([5, 10, 10, 16], 1), ([6, 8, 10, 17], 2), ([6, 8, 11, 16], 1), ([6, 9, 10, 16], 2), ([7, 8, 10, 16], 1)]

def node6510Raw : WordRow := differentiateRow (images 32) node6451

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6510_check :
    collect (scaleRow 1 node6510Raw ++ scaleRow (-(-1 : ℤ)) node6510 ++
      (scaleRow (-1) node6507 ++ scaleRow (-1) node3679)) = [] := by
  decide +kernel

theorem node6510_mem : rowEval varIndex node6510 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6510Raw node6510 (scaleRow (-1) node6507 ++ scaleRow (-1) node3679)
    (1) (-1) (by decide) node6510_check
  · rw [node6510Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6451_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6507 node6507_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3679 node3679_mem))

def node6511 : WordRow := [([8, 10, 10, 17], 1), ([8, 10, 11, 16], 1), ([9, 10, 10, 16], 1)]

def node6511Raw : WordRow := differentiateRow (images 34) node6451

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6511_check :
    collect (scaleRow 1 node6511Raw ++ scaleRow (-(-1 : ℤ)) node6511 ++
      (scaleRow (-1) node6344 ++ scaleRow (-2) node4843 ++ scaleRow (-2) node3688 ++ scaleRow (1) node5538)) = [] := by
  decide +kernel

theorem node6511_mem : rowEval varIndex node6511 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6511Raw node6511 (scaleRow (-1) node6344 ++ scaleRow (-2) node4843 ++ scaleRow (-2) node3688 ++ scaleRow (1) node5538)
    (1) (-1) (by decide) node6511_check
  · rw [node6511Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6451_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6344 node6344_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4843 node4843_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3688 node3688_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5538 node5538_mem))))

def node6512 : WordRow := [([4, 6, 14, 17], 2), ([4, 7, 14, 16], 1), ([4, 10, 12, 17], 2), ([4, 11, 12, 16], 1), ([5, 6, 14, 16], 1), ([5, 10, 12, 16], 1), ([6, 8, 12, 17], 2), ([6, 9, 12, 16], 1), ([7, 8, 12, 16], 1)]

def node6512Raw : WordRow := differentiateRow (images 32) node6452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6512_check :
    collect (scaleRow 1 node6512Raw ++ scaleRow (-(-2 : ℤ)) node6512 ++
      (scaleRow (-2) node6499 ++ scaleRow (-2) node5329)) = [] := by
  decide +kernel

theorem node6512_mem : rowEval varIndex node6512 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6512Raw node6512 (scaleRow (-2) node6499 ++ scaleRow (-2) node5329)
    (1) (-2) (by decide) node6512_check
  · rw [node6512Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6452_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6499 node6499_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5329 node5329_mem))

def node6513 : WordRow := [([4, 10, 14, 17], 2), ([4, 11, 14, 16], 1), ([5, 10, 14, 16], 1), ([6, 8, 14, 17], 2), ([6, 9, 14, 16], 1), ([7, 8, 14, 16], 1), ([8, 10, 12, 17], 2), ([8, 11, 12, 16], 1), ([9, 10, 12, 16], 1)]

def node6513Raw : WordRow := differentiateRow (images 34) node6452

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6513_check :
    collect (scaleRow 1 node6513Raw ++ scaleRow (-(-1 : ℤ)) node6513 ++
      (scaleRow (-1) node6500 ++ scaleRow (-2) node4856 ++ scaleRow (-1) node5626)) = [] := by
  decide +kernel

theorem node6513_mem : rowEval varIndex node6513 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6513Raw node6513 (scaleRow (-1) node6500 ++ scaleRow (-2) node4856 ++ scaleRow (-1) node5626)
    (1) (-1) (by decide) node6513_check
  · rw [node6513Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6452_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6500 node6500_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4856 node4856_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5626 node5626_mem)))

def node6514 : WordRow := [([8, 10, 14, 17], 2), ([8, 11, 14, 16], 1), ([9, 10, 14, 16], 1)]

def node6514Raw : WordRow := differentiateRow (images 34) node6453

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6514_check :
    collect (scaleRow 1 node6514Raw ++ scaleRow (-(-2 : ℤ)) node6514 ++
      (scaleRow (-2) node6395 ++ scaleRow (-4) node4865 ++ scaleRow (2) node5691)) = [] := by
  decide +kernel

theorem node6514_mem : rowEval varIndex node6514 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6514Raw node6514 (scaleRow (-2) node6395 ++ scaleRow (-4) node4865 ++ scaleRow (2) node5691)
    (1) (-2) (by decide) node6514_check
  · rw [node6514Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6453_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6395 node6395_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node4865 node4865_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5691 node5691_mem)))

def node6515 : WordRow := [([4, 6, 8, 17], 2), ([4, 6, 9, 16], 1), ([4, 7, 8, 16], 2), ([5, 6, 8, 16], 1)]

def node6515Raw : WordRow := differentiateRow (images 30) node6454

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6515_check :
    collect (scaleRow 1 node6515Raw ++ scaleRow (-(-1 : ℤ)) node6515 ++
      (scaleRow (-1) node6504 ++ scaleRow (-1) node2816)) = [] := by
  decide +kernel

theorem node6515_mem : rowEval varIndex node6515 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6515Raw node6515 (scaleRow (-1) node6504 ++ scaleRow (-1) node2816)
    (1) (-1) (by decide) node6515_check
  · rw [node6515Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6454_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6504 node6504_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2816 node2816_mem))

def node6516 : WordRow := [([4, 8, 12, 17], 2), ([4, 8, 13, 16], 1), ([4, 9, 12, 16], 1)]

def node6516Raw : WordRow := differentiateRow (images 34) node6454

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6516_check :
    collect (scaleRow 1 node6516Raw ++ scaleRow (-(-1 : ℤ)) node6516 ++
      (scaleRow (-1) node6301 ++ scaleRow (-1) node5076 ++ scaleRow (-1) node2838)) = [] := by
  decide +kernel

theorem node6516_mem : rowEval varIndex node6516 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6516Raw node6516 (scaleRow (-1) node6301 ++ scaleRow (-1) node5076 ++ scaleRow (-1) node2838)
    (1) (-1) (by decide) node6516_check
  · rw [node6516Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6454_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6301 node6301_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5076 node5076_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2838 node2838_mem)))

def node6517 : WordRow := [([6, 6, 8, 17], 1), ([6, 6, 9, 16], 1), ([6, 7, 8, 16], 1)]

def node6517Raw : WordRow := differentiateRow (images 30) node6455

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6517_check :
    collect (scaleRow 1 node6517Raw ++ scaleRow (-(-1 : ℤ)) node6517 ++
      (scaleRow (-1) node6506 ++ scaleRow (-1) node4179)) = [] := by
  decide +kernel

theorem node6517_mem : rowEval varIndex node6517 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6517Raw node6517 (scaleRow (-1) node6506 ++ scaleRow (-1) node4179)
    (1) (-1) (by decide) node6517_check
  · rw [node6517Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6455_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6506 node6506_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4179 node4179_mem))

def node6518 : WordRow := [([4, 10, 12, 17], 2), ([4, 10, 13, 16], 1), ([4, 11, 12, 16], 2), ([5, 10, 12, 16], 1), ([6, 8, 12, 17], 2), ([6, 8, 13, 16], 1), ([6, 9, 12, 16], 2), ([7, 8, 12, 16], 1)]

def node6518Raw : WordRow := differentiateRow (images 34) node6455

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6518_check :
    collect (scaleRow 1 node6518Raw ++ scaleRow (-(-1 : ℤ)) node6518 ++
      (scaleRow (-1) node6512 ++ scaleRow (-2) node5087 ++ scaleRow (-1) node5221)) = [] := by
  decide +kernel

theorem node6518_mem : rowEval varIndex node6518 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6518Raw node6518 (scaleRow (-1) node6512 ++ scaleRow (-2) node5087 ++ scaleRow (-1) node5221)
    (1) (-1) (by decide) node6518_check
  · rw [node6518Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6455_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6512 node6512_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5087 node5087_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5221 node5221_mem)))

def node6519 : WordRow := [([6, 8, 8, 17], 1), ([6, 8, 9, 16], 1), ([7, 8, 8, 16], 1)]

def node6519Raw : WordRow := differentiateRow (images 30) node6456

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6519_check :
    collect (scaleRow 1 node6519Raw ++ scaleRow (-(-1 : ℤ)) node6519 ++
      (scaleRow (-1) node6508 ++ scaleRow (-1) node3838)) = [] := by
  decide +kernel

theorem node6519_mem : rowEval varIndex node6519 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6519Raw node6519 (scaleRow (-1) node6508 ++ scaleRow (-1) node3838)
    (1) (-1) (by decide) node6519_check
  · rw [node6519Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6456_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6508 node6508_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3838 node3838_mem))

def node6520 : WordRow := [([8, 8, 12, 17], 1), ([8, 8, 13, 16], 1), ([8, 9, 12, 16], 1)]

def node6520Raw : WordRow := differentiateRow (images 34) node6456

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6520_check :
    collect (scaleRow 1 node6520Raw ++ scaleRow (-(-1 : ℤ)) node6520 ++
      (scaleRow (-1) node6355 ++ scaleRow (-2) node5100 ++ scaleRow (-2) node3860 ++ scaleRow (1) node5433)) = [] := by
  decide +kernel

theorem node6520_mem : rowEval varIndex node6520 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6520Raw node6520 (scaleRow (-1) node6355 ++ scaleRow (-2) node5100 ++ scaleRow (-2) node3860 ++ scaleRow (1) node5433)
    (1) (-1) (by decide) node6520_check
  · rw [node6520Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6456_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6355 node6355_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5100 node5100_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3860 node3860_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5433 node5433_mem))))

def node6521 : WordRow := [([6, 8, 10, 17], 2), ([6, 8, 11, 16], 1), ([6, 9, 10, 16], 2), ([7, 8, 10, 16], 1)]

def node6521Raw : WordRow := differentiateRow (images 30) node6457

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6521_check :
    collect (scaleRow 1 node6521Raw ++ scaleRow (-(-2 : ℤ)) node6521 ++
      (scaleRow (-2) node6510 ++ scaleRow (-2) node4947)) = [] := by
  decide +kernel

theorem node6521_mem : rowEval varIndex node6521 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6521Raw node6521 (scaleRow (-2) node6510 ++ scaleRow (-2) node4947)
    (1) (-2) (by decide) node6521_check
  · rw [node6521Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6457_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6510 node6510_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4947 node4947_mem))

def node6522 : WordRow := [([6, 8, 12, 17], 2), ([6, 8, 13, 16], 1), ([6, 9, 12, 16], 2), ([7, 8, 12, 16], 1)]

def node6522Raw : WordRow := differentiateRow (images 32) node6457

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6522_check :
    collect (scaleRow 1 node6522Raw ++ scaleRow (-(-1 : ℤ)) node6522 ++
      (scaleRow (-1) node6518 ++ scaleRow (-1) node4389)) = [] := by
  decide +kernel

theorem node6522_mem : rowEval varIndex node6522 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6522Raw node6522 (scaleRow (-1) node6518 ++ scaleRow (-1) node4389)
    (1) (-1) (by decide) node6522_check
  · rw [node6522Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6457_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6518 node6518_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node4389 node4389_mem))

def node6523 : WordRow := [([6, 8, 14, 17], 2), ([6, 9, 14, 16], 1), ([7, 8, 14, 16], 1), ([8, 10, 12, 17], 2), ([8, 10, 13, 16], 1), ([8, 11, 12, 16], 1), ([9, 10, 12, 16], 2)]

def node6523Raw : WordRow := differentiateRow (images 34) node6457

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6523_check :
    collect (scaleRow 1 node6523Raw ++ scaleRow (-(-1 : ℤ)) node6523 ++
      (scaleRow (-1) node6513 ++ scaleRow (-2) node5112 ++ scaleRow (-1) node5548)) = [] := by
  decide +kernel

theorem node6523_mem : rowEval varIndex node6523 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6523Raw node6523 (scaleRow (-1) node6513 ++ scaleRow (-2) node5112 ++ scaleRow (-1) node5548)
    (1) (-1) (by decide) node6523_check
  · rw [node6523Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6457_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6513 node6513_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5112 node5112_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5548 node5548_mem)))

def node6524 : WordRow := [([8, 12, 12, 17], 1), ([8, 12, 13, 16], 1), ([9, 12, 12, 16], 1)]

def node6524Raw : WordRow := differentiateRow (images 34) node6458

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6524_check :
    collect (scaleRow 1 node6524Raw ++ scaleRow (-(-1 : ℤ)) node6524 ++
      (scaleRow (-1) node6374 ++ scaleRow (-2) node5124 ++ scaleRow (-2) node4411 ++ scaleRow (1) node5634)) = [] := by
  decide +kernel

theorem node6524_mem : rowEval varIndex node6524 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6524Raw node6524 (scaleRow (-1) node6374 ++ scaleRow (-2) node5124 ++ scaleRow (-2) node4411 ++ scaleRow (1) node5634)
    (1) (-1) (by decide) node6524_check
  · rw [node6524Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6458_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6374 node6374_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5124 node5124_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4411 node4411_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5634 node5634_mem))))

def node6525 : WordRow := [([8, 12, 14, 17], 2), ([8, 13, 14, 16], 1), ([9, 12, 14, 16], 1)]

def node6525Raw : WordRow := differentiateRow (images 34) node6459

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6525_check :
    collect (scaleRow 1 node6525Raw ++ scaleRow (-(-2 : ℤ)) node6525 ++
      (scaleRow (-2) node6405 ++ scaleRow (-4) node5133 ++ scaleRow (2) node5695)) = [] := by
  decide +kernel

theorem node6525_mem : rowEval varIndex node6525 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6525Raw node6525 (scaleRow (-2) node6405 ++ scaleRow (-4) node5133 ++ scaleRow (2) node5695)
    (1) (-2) (by decide) node6525_check
  · rw [node6525Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6459_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6405 node6405_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node5133 node5133_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5695 node5695_mem)))

def node6526 : WordRow := [([6, 10, 12, 17], 2), ([6, 10, 13, 16], 1), ([6, 11, 12, 16], 1)]

def node6526Raw : WordRow := differentiateRow (images 34) node6460

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6526_check :
    collect (scaleRow 1 node6526Raw ++ scaleRow (-(-1 : ℤ)) node6526 ++
      (scaleRow (-1) node6314 ++ scaleRow (-1) node5233 ++ scaleRow (-1) node3281)) = [] := by
  decide +kernel

theorem node6526_mem : rowEval varIndex node6526 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6526Raw node6526 (scaleRow (-1) node6314 ++ scaleRow (-1) node5233 ++ scaleRow (-1) node3281)
    (1) (-1) (by decide) node6526_check
  · rw [node6526Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6460_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6314 node6314_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5233 node5233_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3281 node3281_mem)))

def node6527 : WordRow := [([8, 10, 12, 17], 1), ([8, 10, 13, 16], 1), ([8, 11, 12, 16], 1), ([9, 10, 12, 16], 1)]

def node6527Raw : WordRow := differentiateRow (images 34) node6461

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6527_check :
    collect (scaleRow 1 node6527Raw ++ scaleRow (-(-2 : ℤ)) node6527 ++
      (scaleRow (-1) node6523 ++ scaleRow (-2) node5242 ++ scaleRow (-1) node5443)) = [] := by
  decide +kernel

theorem node6527_mem : rowEval varIndex node6527 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6527Raw node6527 (scaleRow (-1) node6523 ++ scaleRow (-2) node5242 ++ scaleRow (-1) node5443)
    (1) (-2) (by decide) node6527_check
  · rw [node6527Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6461_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6523 node6523_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5242 node5242_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node5443 node5443_mem)))

def node6528 : WordRow := [([10, 10, 12, 17], 1), ([10, 10, 13, 16], 1), ([10, 11, 12, 16], 1)]

def node6528Raw : WordRow := differentiateRow (images 34) node6462

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6528_check :
    collect (scaleRow 1 node6528Raw ++ scaleRow (-(-1 : ℤ)) node6528 ++
      (scaleRow (-1) node6368 ++ scaleRow (-2) node5253 ++ scaleRow (-2) node4245 ++ scaleRow (1) node5558)) = [] := by
  decide +kernel

theorem node6528_mem : rowEval varIndex node6528 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6528Raw node6528 (scaleRow (-1) node6368 ++ scaleRow (-2) node5253 ++ scaleRow (-2) node4245 ++ scaleRow (1) node5558)
    (1) (-1) (by decide) node6528_check
  · rw [node6528Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6462_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6368 node6368_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5253 node5253_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4245 node4245_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5558 node5558_mem))))

def node6529 : WordRow := [([10, 12, 12, 17], 1), ([10, 12, 13, 16], 1), ([11, 12, 12, 16], 1)]

def node6529Raw : WordRow := differentiateRow (images 34) node6463

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6529_check :
    collect (scaleRow 1 node6529Raw ++ scaleRow (-(-1 : ℤ)) node6529 ++
      (scaleRow (-1) node6379 ++ scaleRow (-2) node5264 ++ scaleRow (-2) node4566 ++ scaleRow (1) node5639)) = [] := by
  decide +kernel

theorem node6529_mem : rowEval varIndex node6529 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6529Raw node6529 (scaleRow (-1) node6379 ++ scaleRow (-2) node5264 ++ scaleRow (-2) node4566 ++ scaleRow (1) node5639)
    (1) (-1) (by decide) node6529_check
  · rw [node6529Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6463_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6379 node6379_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node5264 node5264_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4566 node4566_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5639 node5639_mem))))

def node6530 : WordRow := [([10, 12, 14, 17], 2), ([10, 13, 14, 16], 1), ([11, 12, 14, 16], 1)]

def node6530Raw : WordRow := differentiateRow (images 34) node6464

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6530_check :
    collect (scaleRow 1 node6530Raw ++ scaleRow (-(-2 : ℤ)) node6530 ++
      (scaleRow (-2) node6410 ++ scaleRow (-4) node5273 ++ scaleRow (2) node5699)) = [] := by
  decide +kernel

theorem node6530_mem : rowEval varIndex node6530 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6530Raw node6530 (scaleRow (-2) node6410 ++ scaleRow (-4) node5273 ++ scaleRow (2) node5699)
    (1) (-2) (by decide) node6530_check
  · rw [node6530Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6464_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6410 node6410_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node5273 node5273_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node5699 node5699_mem)))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node6530_mem
