import VOA.DeligneAudit.D4FusionContactM2Dag14

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node5406 : WordRow := [([1, 8, 10, 12], 2), ([2, 5, 6, 14], 1), ([2, 7, 8, 12], -1), ([3, 4, 6, 14], 1), ([3, 6, 8, 12], -1), ([4, 7, 8, 10], -1), ([5, 6, 8, 10], -1)]

def node5406Raw : WordRow := multiplyRow 6 node0694

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5406_check :
    collect (scaleRow 1 node5406Raw ++ scaleRow (-(-1 : ℤ)) node5406 ++
      (scaleRow (-1) node5186)) = [] := by
  decide +kernel

theorem node5406_mem : rowEval varIndex node5406 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5406Raw node5406 (scaleRow (-1) node5186)
    (1) (-1) (by decide) node5406_check
  · rw [node5406Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0694_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5186 node5186_mem)

def node5409 : WordRow := [([3, 8, 10, 13], 2), ([3, 8, 11, 12], 4), ([4, 8, 11, 11], 2), ([4, 9, 10, 11], 1), ([5, 8, 10, 11], 1), ([6, 8, 9, 11], 3), ([6, 9, 9, 10], 2), ([7, 8, 8, 11], 1)]

def node5409Raw : WordRow := multiplyRow 11 node0694

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5409_check :
    collect (scaleRow 1 node5409Raw ++ scaleRow (-(-1 : ℤ)) node5409 ++
      (scaleRow (-2) node2586 ++ scaleRow (-2) node2452 ++ scaleRow (-1) node2655 ++ scaleRow (1) node3421 ++ scaleRow (1) node3647 ++ scaleRow (-1) node5055 ++ scaleRow (2) node3509 ++ scaleRow (-2) node5198)) = [] := by
  decide +kernel

theorem node5409_mem : rowEval varIndex node5409 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5409Raw node5409 (scaleRow (-2) node2586 ++ scaleRow (-2) node2452 ++ scaleRow (-1) node2655 ++ scaleRow (1) node3421 ++ scaleRow (1) node3647 ++ scaleRow (-1) node5055 ++ scaleRow (2) node3509 ++ scaleRow (-2) node5198)
    (1) (-1) (by decide) node5409_check
  · rw [node5409Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0694_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2586 node2586_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2452 node2452_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2655 node2655_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3421 node3421_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3647 node3647_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5055 node5055_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3509 node3509_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5198 node5198_mem))))))))

def node5411 : WordRow := [([5, 8, 11, 12], 2), ([5, 9, 10, 12], 2), ([6, 8, 9, 13], 3), ([6, 9, 9, 12], 4), ([7, 8, 8, 13], -1)]

def node5411Raw : WordRow := multiplyRow 13 node0694

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5411_check :
    collect (scaleRow 2 node5411Raw ++ scaleRow (-(-2 : ℤ)) node5411 ++
      (scaleRow (-4) node3036 ++ scaleRow (-4) node2465 ++ scaleRow (-2) node3105 ++ scaleRow (2) node4090 ++ scaleRow (-1) node5046 ++ scaleRow (-1) node5057 ++ scaleRow (4) node3555 ++ scaleRow (2) node5062 ++ scaleRow (2) node5072 ++ scaleRow (2) node4368 ++ scaleRow (2) node3835 ++ scaleRow (2) node3841 ++ scaleRow (-4) node2905 ++ scaleRow (4) node5080 ++ scaleRow (-4) node5214)) = [] := by
  decide +kernel

theorem node5411_mem : rowEval varIndex node5411 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5411Raw node5411 (scaleRow (-4) node3036 ++ scaleRow (-4) node2465 ++ scaleRow (-2) node3105 ++ scaleRow (2) node4090 ++ scaleRow (-1) node5046 ++ scaleRow (-1) node5057 ++ scaleRow (4) node3555 ++ scaleRow (2) node5062 ++ scaleRow (2) node5072 ++ scaleRow (2) node4368 ++ scaleRow (2) node3835 ++ scaleRow (2) node3841 ++ scaleRow (-4) node2905 ++ scaleRow (4) node5080 ++ scaleRow (-4) node5214)
    (2) (-2) (by decide) node5411_check
  · rw [node5411Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0694_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node3036 node3036_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node2465 node2465_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3105 node3105_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4090 node4090_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5046 node5046_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5057 node5057_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (4) node3555 node3555_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5062 node5062_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5072 node5072_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4368 node4368_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3835 node3835_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3841 node3841_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node2905 node2905_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (4) node5080 node5080_mem) (rowEval_scale_mem varIndex candidateIdeal (-4) node5214 node5214_mem)))))))))))))))

def node5412 : WordRow := [([1, 8, 14, 14], 2), ([2, 5, 14, 14], -1), ([2, 8, 13, 14], -1), ([3, 4, 14, 14], -1), ([3, 8, 12, 14], -1), ([4, 8, 11, 14], -1), ([5, 8, 10, 14], -1), ([6, 8, 9, 14], -1), ([7, 8, 8, 14], -1)]

def node5412Raw : WordRow := multiplyRow 14 node0694

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5412_check :
    collect (scaleRow 1 node5412Raw ++ scaleRow (-(1 : ℤ)) node5412 ++
      ([])) = [] := by
  decide +kernel

theorem node5412_mem : rowEval varIndex node5412 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5412Raw node5412 ([])
    (1) (1) (by decide) node5412_check
  · rw [node5412Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0694_mem
  · exact candidateIdeal.zero_mem

def node5414 : WordRow := [([1, 8, 14, 16], 2), ([2, 5, 14, 16], -1), ([2, 8, 13, 16], -1), ([3, 4, 14, 16], -1), ([3, 8, 12, 16], -1), ([4, 8, 11, 16], -1), ([5, 8, 10, 16], -1), ([6, 8, 9, 16], -1), ([7, 8, 8, 16], -1)]

def node5414Raw : WordRow := multiplyRow 16 node0694

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5414_check :
    collect (scaleRow 1 node5414Raw ++ scaleRow (-(1 : ℤ)) node5414 ++
      ([])) = [] := by
  decide +kernel

theorem node5414_mem : rowEval varIndex node5414 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5414Raw node5414 ([])
    (1) (1) (by decide) node5414_check
  · rw [node5414Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0694_mem
  · exact candidateIdeal.zero_mem

def node5420 : WordRow := [([3, 8, 12, 14], 2), ([8, 8, 11, 12], 1), ([8, 9, 10, 12], 1)]

def node5420Raw : WordRow := multiplyRow 12 node0695

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5420_check :
    collect (scaleRow 1 node5420Raw ++ scaleRow (-(1 : ℤ)) node5420 ++
      ([])) = [] := by
  decide +kernel

theorem node5420_mem : rowEval varIndex node5420 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5420Raw node5420 ([])
    (1) (1) (by decide) node5420_check
  · rw [node5420Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0695_mem
  · exact candidateIdeal.zero_mem

def node5424 : WordRow := [([3, 8, 14, 16], 2), ([8, 8, 11, 16], 1), ([8, 9, 10, 16], 1)]

def node5424Raw : WordRow := multiplyRow 16 node0695

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5424_check :
    collect (scaleRow 1 node5424Raw ++ scaleRow (-(1 : ℤ)) node5424 ++
      ([])) = [] := by
  decide +kernel

theorem node5424_mem : rowEval varIndex node5424 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5424Raw node5424 ([])
    (1) (1) (by decide) node5424_check
  · rw [node5424Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0695_mem
  · exact candidateIdeal.zero_mem

def node5428 : WordRow := [([5, 8, 10, 14], 2), ([8, 8, 10, 13], 1), ([8, 9, 10, 12], 1)]

def node5428Raw : WordRow := multiplyRow 10 node0696

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5428_check :
    collect (scaleRow 1 node5428Raw ++ scaleRow (-(1 : ℤ)) node5428 ++
      ([])) = [] := by
  decide +kernel

theorem node5428_mem : rowEval varIndex node5428 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5428Raw node5428 ([])
    (1) (1) (by decide) node5428_check
  · rw [node5428Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0696_mem
  · exact candidateIdeal.zero_mem

def node5433 : WordRow := [([5, 8, 14, 16], 2), ([8, 8, 13, 16], 1), ([8, 9, 12, 16], 1)]

def node5433Raw : WordRow := multiplyRow 16 node0696

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5433_check :
    collect (scaleRow 1 node5433Raw ++ scaleRow (-(1 : ℤ)) node5433 ++
      ([])) = [] := by
  decide +kernel

theorem node5433_mem : rowEval varIndex node5433 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5433Raw node5433 ([])
    (1) (1) (by decide) node5433_check
  · rw [node5433Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0696_mem
  · exact candidateIdeal.zero_mem

def node5435 : WordRow := [([6, 6, 9, 14], 1), ([6, 7, 8, 14], -1), ([6, 8, 10, 13], -1), ([6, 8, 11, 12], -1)]

def node5435Raw : WordRow := multiplyRow 6 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5435_check :
    collect (scaleRow 1 node5435Raw ++ scaleRow (-(1 : ℤ)) node5435 ++
      ([])) = [] := by
  decide +kernel

theorem node5435_mem : rowEval varIndex node5435 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5435Raw node5435 ([])
    (1) (1) (by decide) node5435_check
  · rw [node5435Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · exact candidateIdeal.zero_mem

def node5436 : WordRow := [([7, 8, 8, 14], 1), ([8, 8, 10, 13], 1), ([8, 8, 11, 12], 1)]

def node5436Raw : WordRow := multiplyRow 8 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5436_check :
    collect (scaleRow 1 node5436Raw ++ scaleRow (-(-1 : ℤ)) node5436 ++
      (scaleRow (-1) node4644)) = [] := by
  decide +kernel

theorem node5436_mem : rowEval varIndex node5436 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5436Raw node5436 (scaleRow (-1) node4644)
    (1) (-1) (by decide) node5436_check
  · rw [node5436Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4644 node4644_mem)

def node5437 : WordRow := [([6, 9, 10, 14], 1), ([7, 8, 10, 14], -1), ([8, 10, 10, 13], -1), ([8, 10, 11, 12], -1)]

def node5437Raw : WordRow := multiplyRow 10 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5437_check :
    collect (scaleRow 1 node5437Raw ++ scaleRow (-(1 : ℤ)) node5437 ++
      ([])) = [] := by
  decide +kernel

theorem node5437_mem : rowEval varIndex node5437 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5437Raw node5437 ([])
    (1) (1) (by decide) node5437_check
  · rw [node5437Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · exact candidateIdeal.zero_mem

def node5439 : WordRow := [([6, 9, 12, 14], 1), ([7, 8, 12, 14], -1), ([8, 10, 12, 13], -1), ([8, 11, 12, 12], -1)]

def node5439Raw : WordRow := multiplyRow 12 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5439_check :
    collect (scaleRow 1 node5439Raw ++ scaleRow (-(1 : ℤ)) node5439 ++
      ([])) = [] := by
  decide +kernel

theorem node5439_mem : rowEval varIndex node5439 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5439Raw node5439 ([])
    (1) (1) (by decide) node5439_check
  · rw [node5439Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · exact candidateIdeal.zero_mem

def node5443 : WordRow := [([6, 9, 14, 16], 1), ([7, 8, 14, 16], -1), ([8, 10, 13, 16], -1), ([8, 11, 12, 16], -1)]

def node5443Raw : WordRow := multiplyRow 16 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5443_check :
    collect (scaleRow 1 node5443Raw ++ scaleRow (-(1 : ℤ)) node5443 ++
      ([])) = [] := by
  decide +kernel

theorem node5443_mem : rowEval varIndex node5443 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5443Raw node5443 ([])
    (1) (1) (by decide) node5443_check
  · rw [node5443Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · exact candidateIdeal.zero_mem

def node5444 : WordRow := [([6, 9, 14, 17], 1), ([7, 8, 14, 17], -1), ([8, 10, 13, 17], -1), ([8, 11, 12, 17], -1)]

def node5444Raw : WordRow := multiplyRow 17 node0697

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5444_check :
    collect (scaleRow 1 node5444Raw ++ scaleRow (-(1 : ℤ)) node5444 ++
      ([])) = [] := by
  decide +kernel

theorem node5444_mem : rowEval varIndex node5444 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5444Raw node5444 ([])
    (1) (1) (by decide) node5444_check
  · rw [node5444Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0697_mem
  · exact candidateIdeal.zero_mem

def node5457 : WordRow := [([8, 10, 12, 15], 1), ([9, 10, 12, 14], 1)]

def node5457Raw : WordRow := multiplyRow 12 node0700

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5457_check :
    collect (scaleRow 1 node5457Raw ++ scaleRow (-(1 : ℤ)) node5457 ++
      ([])) = [] := by
  decide +kernel

theorem node5457_mem : rowEval varIndex node5457 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5457Raw node5457 ([])
    (1) (1) (by decide) node5457_check
  · rw [node5457Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0700_mem
  · exact candidateIdeal.zero_mem

def node5484 : WordRow := [([8, 15, 16, 17], 1), ([9, 14, 16, 17], 1)]

def node5484Raw : WordRow := multiplyRow 17 node0706

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5484_check :
    collect (scaleRow 1 node5484Raw ++ scaleRow (-(1 : ℤ)) node5484 ++
      ([])) = [] := by
  decide +kernel

theorem node5484_mem : rowEval varIndex node5484 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5484Raw node5484 ([])
    (1) (1) (by decide) node5484_check
  · rw [node5484Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0706_mem
  · exact candidateIdeal.zero_mem

def node5486 : WordRow := [([7, 9, 10, 12], 1)]

def node5486Raw : WordRow := multiplyRow 6 node0708

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5486_check :
    collect (scaleRow 1 node5486Raw ++ scaleRow (-(-2 : ℤ)) node5486 ++
      (scaleRow (-1) node4203 ++ scaleRow (-1) node4531 ++ scaleRow (-1) node4211 ++ scaleRow (1) node4523 ++ scaleRow (1) node4256)) = [] := by
  decide +kernel

theorem node5486_mem : rowEval varIndex node5486 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5486Raw node5486 (scaleRow (-1) node4203 ++ scaleRow (-1) node4531 ++ scaleRow (-1) node4211 ++ scaleRow (1) node4523 ++ scaleRow (1) node4256)
    (1) (-2) (by decide) node5486_check
  · rw [node5486Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0708_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4203 node4203_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4531 node4531_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4211 node4211_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4523 node4523_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4256 node4256_mem)))))

def node5487 : WordRow := [([9, 10, 10, 13], 1), ([9, 10, 11, 12], 1)]

def node5487Raw : WordRow := multiplyRow 10 node0708

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5487_check :
    collect (scaleRow 1 node5487Raw ++ scaleRow (-(1 : ℤ)) node5487 ++
      (scaleRow (-1) node4963)) = [] := by
  decide +kernel

theorem node5487_mem : rowEval varIndex node5487 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5487Raw node5487 (scaleRow (-1) node4963)
    (1) (1) (by decide) node5487_check
  · rw [node5487Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0708_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4963 node4963_mem)

def node5488 : WordRow := [([9, 11, 12, 12], 1)]

def node5488Raw : WordRow := multiplyRow 12 node0708

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5488_check :
    collect (scaleRow 1 node5488Raw ++ scaleRow (-(1 : ℤ)) node5488 ++
      (scaleRow (-1) node5282 ++ scaleRow (-2) node5331)) = [] := by
  decide +kernel

theorem node5488_mem : rowEval varIndex node5488 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5488Raw node5488 (scaleRow (-1) node5282 ++ scaleRow (-2) node5331)
    (1) (1) (by decide) node5488_check
  · rw [node5488Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0708_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5282 node5282_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5331 node5331_mem))

def node5491 : WordRow := [([8, 11, 13, 16], 1), ([9, 10, 13, 16], 1), ([9, 11, 12, 16], 1)]

def node5491Raw : WordRow := multiplyRow 16 node0708

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5491_check :
    collect (scaleRow 1 node5491Raw ++ scaleRow (-(1 : ℤ)) node5491 ++
      ([])) = [] := by
  decide +kernel

theorem node5491_mem : rowEval varIndex node5491 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5491Raw node5491 ([])
    (1) (1) (by decide) node5491_check
  · rw [node5491Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0708_mem
  · exact candidateIdeal.zero_mem

def node5530 : WordRow := [([1, 10, 14, 14], 2), ([2, 7, 14, 14], -1), ([2, 10, 13, 14], -1), ([3, 6, 14, 14], -1), ([3, 10, 12, 14], -1), ([4, 10, 11, 14], -1), ([5, 10, 10, 14], -1), ([6, 9, 10, 14], -1), ([7, 8, 10, 14], -1)]

def node5530Raw : WordRow := multiplyRow 14 node0718

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5530_check :
    collect (scaleRow 1 node5530Raw ++ scaleRow (-(1 : ℤ)) node5530 ++
      ([])) = [] := by
  decide +kernel

theorem node5530_mem : rowEval varIndex node5530 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5530Raw node5530 ([])
    (1) (1) (by decide) node5530_check
  · rw [node5530Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0718_mem
  · exact candidateIdeal.zero_mem

def node5532 : WordRow := [([1, 10, 14, 16], 2), ([2, 7, 14, 16], -1), ([2, 10, 13, 16], -1), ([3, 6, 14, 16], -1), ([3, 10, 12, 16], -1), ([4, 10, 11, 16], -1), ([5, 10, 10, 16], -1), ([6, 9, 10, 16], -1), ([7, 8, 10, 16], -1)]

def node5532Raw : WordRow := multiplyRow 16 node0718

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5532_check :
    collect (scaleRow 1 node5532Raw ++ scaleRow (-(1 : ℤ)) node5532 ++
      ([])) = [] := by
  decide +kernel

theorem node5532_mem : rowEval varIndex node5532 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5532Raw node5532 ([])
    (1) (1) (by decide) node5532_check
  · rw [node5532Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0718_mem
  · exact candidateIdeal.zero_mem

def node5536 : WordRow := [([3, 10, 12, 14], 2), ([8, 10, 11, 12], 1), ([9, 10, 10, 12], 1)]

def node5536Raw : WordRow := multiplyRow 12 node0719

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5536_check :
    collect (scaleRow 1 node5536Raw ++ scaleRow (-(1 : ℤ)) node5536 ++
      ([])) = [] := by
  decide +kernel

theorem node5536_mem : rowEval varIndex node5536 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5536Raw node5536 ([])
    (1) (1) (by decide) node5536_check
  · rw [node5536Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0719_mem
  · exact candidateIdeal.zero_mem

def node5538 : WordRow := [([3, 10, 14, 16], 2), ([8, 10, 11, 16], 1), ([9, 10, 10, 16], 1)]

def node5538Raw : WordRow := multiplyRow 16 node0719

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5538_check :
    collect (scaleRow 1 node5538Raw ++ scaleRow (-(1 : ℤ)) node5538 ++
      ([])) = [] := by
  decide +kernel

theorem node5538_mem : rowEval varIndex node5538 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5538Raw node5538 ([])
    (1) (1) (by decide) node5538_check
  · rw [node5538Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0719_mem
  · exact candidateIdeal.zero_mem

def node5540 : WordRow := [([4, 4, 11, 14], 1), ([4, 5, 10, 14], -1), ([4, 8, 10, 13], -1), ([4, 9, 10, 12], -1)]

def node5540Raw : WordRow := multiplyRow 4 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5540_check :
    collect (scaleRow 1 node5540Raw ++ scaleRow (-(1 : ℤ)) node5540 ++
      ([])) = [] := by
  decide +kernel

theorem node5540_mem : rowEval varIndex node5540 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5540Raw node5540 ([])
    (1) (1) (by decide) node5540_check
  · rw [node5540Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · exact candidateIdeal.zero_mem

def node5542 : WordRow := [([4, 8, 11, 14], 1), ([5, 8, 10, 14], -1), ([8, 8, 10, 13], -1), ([8, 9, 10, 12], -1)]

def node5542Raw : WordRow := multiplyRow 8 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5542_check :
    collect (scaleRow 1 node5542Raw ++ scaleRow (-(1 : ℤ)) node5542 ++
      ([])) = [] := by
  decide +kernel

theorem node5542_mem : rowEval varIndex node5542 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5542Raw node5542 ([])
    (1) (1) (by decide) node5542_check
  · rw [node5542Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · exact candidateIdeal.zero_mem

def node5543 : WordRow := [([5, 10, 10, 14], 1), ([8, 10, 10, 13], 1), ([9, 10, 10, 12], 1)]

def node5543Raw : WordRow := multiplyRow 10 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5543_check :
    collect (scaleRow 1 node5543Raw ++ scaleRow (-(-1 : ℤ)) node5543 ++
      (scaleRow (-1) node4945)) = [] := by
  decide +kernel

theorem node5543_mem : rowEval varIndex node5543 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5543Raw node5543 (scaleRow (-1) node4945)
    (1) (-1) (by decide) node5543_check
  · rw [node5543Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4945 node4945_mem)

def node5544 : WordRow := [([4, 11, 12, 14], 1), ([5, 10, 12, 14], -1), ([8, 10, 12, 13], -1), ([9, 10, 12, 12], -1)]

def node5544Raw : WordRow := multiplyRow 12 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5544_check :
    collect (scaleRow 1 node5544Raw ++ scaleRow (-(1 : ℤ)) node5544 ++
      ([])) = [] := by
  decide +kernel

theorem node5544_mem : rowEval varIndex node5544 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5544Raw node5544 ([])
    (1) (1) (by decide) node5544_check
  · rw [node5544Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · exact candidateIdeal.zero_mem

def node5548 : WordRow := [([4, 11, 14, 16], 1), ([5, 10, 14, 16], -1), ([8, 10, 13, 16], -1), ([9, 10, 12, 16], -1)]

def node5548Raw : WordRow := multiplyRow 16 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5548_check :
    collect (scaleRow 1 node5548Raw ++ scaleRow (-(1 : ℤ)) node5548 ++
      ([])) = [] := by
  decide +kernel

theorem node5548_mem : rowEval varIndex node5548 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5548Raw node5548 ([])
    (1) (1) (by decide) node5548_check
  · rw [node5548Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · exact candidateIdeal.zero_mem

def node5549 : WordRow := [([4, 11, 14, 17], 1), ([5, 10, 14, 17], -1), ([8, 10, 13, 17], -1), ([9, 10, 12, 17], -1)]

def node5549Raw : WordRow := multiplyRow 17 node0720

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5549_check :
    collect (scaleRow 1 node5549Raw ++ scaleRow (-(1 : ℤ)) node5549 ++
      ([])) = [] := by
  decide +kernel

theorem node5549_mem : rowEval varIndex node5549 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5549Raw node5549 ([])
    (1) (1) (by decide) node5549_check
  · rw [node5549Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0720_mem
  · exact candidateIdeal.zero_mem

def node5553 : WordRow := [([7, 8, 10, 14], 2), ([8, 10, 10, 13], 1), ([8, 10, 11, 12], 1)]

def node5553Raw : WordRow := multiplyRow 8 node0722

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5553_check :
    collect (scaleRow 1 node5553Raw ++ scaleRow (-(1 : ℤ)) node5553 ++
      ([])) = [] := by
  decide +kernel

theorem node5553_mem : rowEval varIndex node5553 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5553Raw node5553 ([])
    (1) (1) (by decide) node5553_check
  · rw [node5553Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0722_mem
  · exact candidateIdeal.zero_mem

def node5558 : WordRow := [([7, 10, 14, 16], 2), ([10, 10, 13, 16], 1), ([10, 11, 12, 16], 1)]

def node5558Raw : WordRow := multiplyRow 16 node0722

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5558_check :
    collect (scaleRow 1 node5558Raw ++ scaleRow (-(1 : ℤ)) node5558 ++
      ([])) = [] := by
  decide +kernel

theorem node5558_mem : rowEval varIndex node5558 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5558Raw node5558 ([])
    (1) (1) (by decide) node5558_check
  · rw [node5558Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0722_mem
  · exact candidateIdeal.zero_mem

def node5567 : WordRow := [([8, 11, 14, 17], 1), ([9, 10, 14, 17], -1)]

def node5567Raw : WordRow := multiplyRow 17 node0723

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5567_check :
    collect (scaleRow 1 node5567Raw ++ scaleRow (-(1 : ℤ)) node5567 ++
      ([])) = [] := by
  decide +kernel

theorem node5567_mem : rowEval varIndex node5567 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5567Raw node5567 ([])
    (1) (1) (by decide) node5567_check
  · rw [node5567Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0723_mem
  · exact candidateIdeal.zero_mem

def node5593 : WordRow := [([10, 15, 16, 17], 1), ([11, 14, 16, 17], 1)]

def node5593Raw : WordRow := multiplyRow 17 node0730

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5593_check :
    collect (scaleRow 1 node5593Raw ++ scaleRow (-(1 : ℤ)) node5593 ++
      ([])) = [] := by
  decide +kernel

theorem node5593_mem : rowEval varIndex node5593 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5593Raw node5593 ([])
    (1) (1) (by decide) node5593_check
  · rw [node5593Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0730_mem
  · exact candidateIdeal.zero_mem

def node5617 : WordRow := [([1, 12, 14, 14], 2), ([2, 12, 13, 14], -1), ([3, 12, 12, 14], -1), ([4, 7, 14, 14], -1), ([4, 11, 12, 14], -1), ([5, 6, 14, 14], -1), ([5, 10, 12, 14], -1), ([6, 9, 12, 14], -1), ([7, 8, 12, 14], -1)]

def node5617Raw : WordRow := multiplyRow 14 node0738

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5617_check :
    collect (scaleRow 1 node5617Raw ++ scaleRow (-(1 : ℤ)) node5617 ++
      ([])) = [] := by
  decide +kernel

theorem node5617_mem : rowEval varIndex node5617 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5617Raw node5617 ([])
    (1) (1) (by decide) node5617_check
  · rw [node5617Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0738_mem
  · exact candidateIdeal.zero_mem

def node5618 : WordRow := [([1, 12, 14, 16], 2), ([2, 12, 13, 16], -1), ([3, 12, 12, 16], -1), ([4, 7, 14, 16], -1), ([4, 11, 12, 16], -1), ([5, 6, 14, 16], -1), ([5, 10, 12, 16], -1), ([6, 9, 12, 16], -1), ([7, 8, 12, 16], -1)]

def node5618Raw : WordRow := multiplyRow 16 node0738

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5618_check :
    collect (scaleRow 1 node5618Raw ++ scaleRow (-(1 : ℤ)) node5618 ++
      ([])) = [] := by
  decide +kernel

theorem node5618_mem : rowEval varIndex node5618 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5618Raw node5618 ([])
    (1) (1) (by decide) node5618_check
  · rw [node5618Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0738_mem
  · exact candidateIdeal.zero_mem

def node5620 : WordRow := [([2, 2, 13, 14], 1), ([2, 3, 12, 14], -1), ([2, 8, 11, 12], -1), ([2, 9, 10, 12], -1)]

def node5620Raw : WordRow := multiplyRow 2 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5620_check :
    collect (scaleRow 1 node5620Raw ++ scaleRow (-(1 : ℤ)) node5620 ++
      ([])) = [] := by
  decide +kernel

theorem node5620_mem : rowEval varIndex node5620 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5620Raw node5620 ([])
    (1) (1) (by decide) node5620_check
  · rw [node5620Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · exact candidateIdeal.zero_mem

def node5621 : WordRow := [([2, 8, 13, 14], 1), ([3, 8, 12, 14], -1), ([8, 8, 11, 12], -1), ([8, 9, 10, 12], -1)]

def node5621Raw : WordRow := multiplyRow 8 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5621_check :
    collect (scaleRow 1 node5621Raw ++ scaleRow (-(1 : ℤ)) node5621 ++
      ([])) = [] := by
  decide +kernel

theorem node5621_mem : rowEval varIndex node5621 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5621Raw node5621 ([])
    (1) (1) (by decide) node5621_check
  · rw [node5621Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · exact candidateIdeal.zero_mem

def node5622 : WordRow := [([2, 10, 13, 14], 1), ([3, 10, 12, 14], -1), ([8, 10, 11, 12], -1), ([9, 10, 10, 12], -1)]

def node5622Raw : WordRow := multiplyRow 10 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5622_check :
    collect (scaleRow 1 node5622Raw ++ scaleRow (-(1 : ℤ)) node5622 ++
      ([])) = [] := by
  decide +kernel

theorem node5622_mem : rowEval varIndex node5622 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5622Raw node5622 ([])
    (1) (1) (by decide) node5622_check
  · rw [node5622Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · exact candidateIdeal.zero_mem

def node5623 : WordRow := [([3, 12, 12, 14], 1), ([8, 11, 12, 12], 1), ([9, 10, 12, 12], 1)]

def node5623Raw : WordRow := multiplyRow 12 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5623_check :
    collect (scaleRow 1 node5623Raw ++ scaleRow (-(-1 : ℤ)) node5623 ++
      (scaleRow (-1) node5327)) = [] := by
  decide +kernel

theorem node5623_mem : rowEval varIndex node5623 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5623Raw node5623 (scaleRow (-1) node5327)
    (1) (-1) (by decide) node5623_check
  · rw [node5623Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5327 node5327_mem)

def node5626 : WordRow := [([2, 13, 14, 16], 1), ([3, 12, 14, 16], -1), ([8, 11, 12, 16], -1), ([9, 10, 12, 16], -1)]

def node5626Raw : WordRow := multiplyRow 16 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5626_check :
    collect (scaleRow 1 node5626Raw ++ scaleRow (-(1 : ℤ)) node5626 ++
      ([])) = [] := by
  decide +kernel

theorem node5626_mem : rowEval varIndex node5626 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5626Raw node5626 ([])
    (1) (1) (by decide) node5626_check
  · rw [node5626Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · exact candidateIdeal.zero_mem

def node5627 : WordRow := [([2, 13, 14, 17], 1), ([3, 12, 14, 17], -1), ([8, 11, 12, 17], -1), ([9, 10, 12, 17], -1)]

def node5627Raw : WordRow := multiplyRow 17 node0739

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5627_check :
    collect (scaleRow 1 node5627Raw ++ scaleRow (-(1 : ℤ)) node5627 ++
      ([])) = [] := by
  decide +kernel

theorem node5627_mem : rowEval varIndex node5627 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5627Raw node5627 ([])
    (1) (1) (by decide) node5627_check
  · rw [node5627Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0739_mem
  · exact candidateIdeal.zero_mem

def node5631 : WordRow := [([5, 10, 12, 14], 2), ([8, 10, 12, 13], 1), ([9, 10, 12, 12], 1)]

def node5631Raw : WordRow := multiplyRow 10 node0741

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5631_check :
    collect (scaleRow 1 node5631Raw ++ scaleRow (-(1 : ℤ)) node5631 ++
      ([])) = [] := by
  decide +kernel

theorem node5631_mem : rowEval varIndex node5631 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5631Raw node5631 ([])
    (1) (1) (by decide) node5631_check
  · rw [node5631Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0741_mem
  · exact candidateIdeal.zero_mem

def node5634 : WordRow := [([5, 12, 14, 16], 2), ([8, 12, 13, 16], 1), ([9, 12, 12, 16], 1)]

def node5634Raw : WordRow := multiplyRow 16 node0741

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5634_check :
    collect (scaleRow 1 node5634Raw ++ scaleRow (-(1 : ℤ)) node5634 ++
      ([])) = [] := by
  decide +kernel

theorem node5634_mem : rowEval varIndex node5634 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5634Raw node5634 ([])
    (1) (1) (by decide) node5634_check
  · rw [node5634Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0741_mem
  · exact candidateIdeal.zero_mem

def node5636 : WordRow := [([7, 8, 12, 14], 2), ([8, 10, 12, 13], 1), ([8, 11, 12, 12], 1)]

def node5636Raw : WordRow := multiplyRow 8 node0742

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5636_check :
    collect (scaleRow 1 node5636Raw ++ scaleRow (-(1 : ℤ)) node5636 ++
      ([])) = [] := by
  decide +kernel

theorem node5636_mem : rowEval varIndex node5636 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5636Raw node5636 ([])
    (1) (1) (by decide) node5636_check
  · rw [node5636Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0742_mem
  · exact candidateIdeal.zero_mem

def node5639 : WordRow := [([7, 12, 14, 16], 2), ([10, 12, 13, 16], 1), ([11, 12, 12, 16], 1)]

def node5639Raw : WordRow := multiplyRow 16 node0742

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5639_check :
    collect (scaleRow 1 node5639Raw ++ scaleRow (-(1 : ℤ)) node5639 ++
      ([])) = [] := by
  decide +kernel

theorem node5639_mem : rowEval varIndex node5639 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5639Raw node5639 ([])
    (1) (1) (by decide) node5639_check
  · rw [node5639Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0742_mem
  · exact candidateIdeal.zero_mem

def node5647 : WordRow := [([8, 13, 14, 17], 1), ([9, 12, 14, 17], -1)]

def node5647Raw : WordRow := multiplyRow 17 node0743

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5647_check :
    collect (scaleRow 1 node5647Raw ++ scaleRow (-(1 : ℤ)) node5647 ++
      ([])) = [] := by
  decide +kernel

theorem node5647_mem : rowEval varIndex node5647 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5647Raw node5647 ([])
    (1) (1) (by decide) node5647_check
  · rw [node5647Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0743_mem
  · exact candidateIdeal.zero_mem

def node5655 : WordRow := [([10, 13, 14, 17], 1), ([11, 12, 14, 17], -1)]

def node5655Raw : WordRow := multiplyRow 17 node0745

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5655_check :
    collect (scaleRow 1 node5655Raw ++ scaleRow (-(1 : ℤ)) node5655 ++
      ([])) = [] := by
  decide +kernel

theorem node5655_mem : rowEval varIndex node5655 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5655Raw node5655 ([])
    (1) (1) (by decide) node5655_check
  · rw [node5655Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0745_mem
  · exact candidateIdeal.zero_mem

def node5671 : WordRow := [([12, 15, 16, 17], 1), ([13, 14, 16, 17], 1)]

def node5671Raw : WordRow := multiplyRow 17 node0750

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5671_check :
    collect (scaleRow 1 node5671Raw ++ scaleRow (-(1 : ℤ)) node5671 ++
      ([])) = [] := by
  decide +kernel

theorem node5671_mem : rowEval varIndex node5671 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5671Raw node5671 ([])
    (1) (1) (by decide) node5671_check
  · rw [node5671Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0750_mem
  · exact candidateIdeal.zero_mem

def node5686 : WordRow := [([1, 14, 14, 14], 1), ([2, 13, 14, 14], -1), ([3, 12, 14, 14], -1), ([4, 11, 14, 14], -1), ([5, 10, 14, 14], -1), ([6, 9, 14, 14], -1), ([7, 8, 14, 14], -1)]

def node5686Raw : WordRow := multiplyRow 14 node0756

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5686_check :
    collect (scaleRow 1 node5686Raw ++ scaleRow (-(1 : ℤ)) node5686 ++
      ([])) = [] := by
  decide +kernel

theorem node5686_mem : rowEval varIndex node5686 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5686Raw node5686 ([])
    (1) (1) (by decide) node5686_check
  · rw [node5686Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0756_mem
  · exact candidateIdeal.zero_mem

def node5687 : WordRow := [([1, 14, 14, 16], 1), ([2, 13, 14, 16], -1), ([3, 12, 14, 16], -1), ([4, 11, 14, 16], -1), ([5, 10, 14, 16], -1), ([6, 9, 14, 16], -1), ([7, 8, 14, 16], -1)]

def node5687Raw : WordRow := multiplyRow 16 node0756

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5687_check :
    collect (scaleRow 1 node5687Raw ++ scaleRow (-(1 : ℤ)) node5687 ++
      ([])) = [] := by
  decide +kernel

theorem node5687_mem : rowEval varIndex node5687 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5687Raw node5687 ([])
    (1) (1) (by decide) node5687_check
  · rw [node5687Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0756_mem
  · exact candidateIdeal.zero_mem

def node5689 : WordRow := [([3, 12, 14, 14], 1), ([8, 11, 12, 14], 1), ([9, 10, 12, 14], 1)]

def node5689Raw : WordRow := multiplyRow 12 node0757

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5689_check :
    collect (scaleRow 1 node5689Raw ++ scaleRow (-(1 : ℤ)) node5689 ++
      ([])) = [] := by
  decide +kernel

theorem node5689_mem : rowEval varIndex node5689 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5689Raw node5689 ([])
    (1) (1) (by decide) node5689_check
  · rw [node5689Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0757_mem
  · exact candidateIdeal.zero_mem

def node5691 : WordRow := [([3, 14, 14, 16], 1), ([8, 11, 14, 16], 1), ([9, 10, 14, 16], 1)]

def node5691Raw : WordRow := multiplyRow 16 node0757

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5691_check :
    collect (scaleRow 1 node5691Raw ++ scaleRow (-(1 : ℤ)) node5691 ++
      ([])) = [] := by
  decide +kernel

theorem node5691_mem : rowEval varIndex node5691 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5691Raw node5691 ([])
    (1) (1) (by decide) node5691_check
  · rw [node5691Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0757_mem
  · exact candidateIdeal.zero_mem

def node5693 : WordRow := [([5, 10, 14, 14], 1), ([8, 10, 13, 14], 1), ([9, 10, 12, 14], 1)]

def node5693Raw : WordRow := multiplyRow 10 node0758

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5693_check :
    collect (scaleRow 1 node5693Raw ++ scaleRow (-(1 : ℤ)) node5693 ++
      ([])) = [] := by
  decide +kernel

theorem node5693_mem : rowEval varIndex node5693 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5693Raw node5693 ([])
    (1) (1) (by decide) node5693_check
  · rw [node5693Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0758_mem
  · exact candidateIdeal.zero_mem

def node5695 : WordRow := [([5, 14, 14, 16], 1), ([8, 13, 14, 16], 1), ([9, 12, 14, 16], 1)]

def node5695Raw : WordRow := multiplyRow 16 node0758

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5695_check :
    collect (scaleRow 1 node5695Raw ++ scaleRow (-(1 : ℤ)) node5695 ++
      ([])) = [] := by
  decide +kernel

theorem node5695_mem : rowEval varIndex node5695 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5695Raw node5695 ([])
    (1) (1) (by decide) node5695_check
  · rw [node5695Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0758_mem
  · exact candidateIdeal.zero_mem

def node5697 : WordRow := [([7, 8, 14, 14], 1), ([8, 10, 13, 14], 1), ([8, 11, 12, 14], 1)]

def node5697Raw : WordRow := multiplyRow 8 node0759

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5697_check :
    collect (scaleRow 1 node5697Raw ++ scaleRow (-(1 : ℤ)) node5697 ++
      ([])) = [] := by
  decide +kernel

theorem node5697_mem : rowEval varIndex node5697 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5697Raw node5697 ([])
    (1) (1) (by decide) node5697_check
  · rw [node5697Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0759_mem
  · exact candidateIdeal.zero_mem

def node5699 : WordRow := [([7, 14, 14, 16], 1), ([10, 13, 14, 16], 1), ([11, 12, 14, 16], 1)]

def node5699Raw : WordRow := multiplyRow 16 node0759

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5699_check :
    collect (scaleRow 1 node5699Raw ++ scaleRow (-(1 : ℤ)) node5699 ++
      ([])) = [] := by
  decide +kernel

theorem node5699_mem : rowEval varIndex node5699 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5699Raw node5699 ([])
    (1) (1) (by decide) node5699_check
  · rw [node5699Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0759_mem
  · exact candidateIdeal.zero_mem

def node5737 : WordRow := [([1, 2, 4, 6], 1)]

def node5737Raw : WordRow := multiplyRow 15 node0770

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5737_check :
    collect (scaleRow 1 node5737Raw ++ scaleRow (-(-6 : ℤ)) node5737 ++
      (scaleRow (-1) node3939 ++ scaleRow (1) node0884 ++ scaleRow (-1) node2938 ++ scaleRow (-1) node1205 ++ scaleRow (-1) node2486 ++ scaleRow (-1) node1491 ++ scaleRow (-1) node2236 ++ scaleRow (-1) node1744 ++ scaleRow (2) node0915 ++ scaleRow (2) node0942 ++ scaleRow (2) node0965 ++ scaleRow (-2) node1756 ++ scaleRow (-2) node1503 ++ scaleRow (-2) node1244)) = [] := by
  decide +kernel

theorem node5737_mem : rowEval varIndex node5737 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5737Raw node5737 (scaleRow (-1) node3939 ++ scaleRow (1) node0884 ++ scaleRow (-1) node2938 ++ scaleRow (-1) node1205 ++ scaleRow (-1) node2486 ++ scaleRow (-1) node1491 ++ scaleRow (-1) node2236 ++ scaleRow (-1) node1744 ++ scaleRow (2) node0915 ++ scaleRow (2) node0942 ++ scaleRow (2) node0965 ++ scaleRow (-2) node1756 ++ scaleRow (-2) node1503 ++ scaleRow (-2) node1244)
    (1) (-6) (by decide) node5737_check
  · rw [node5737Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0770_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3939 node3939_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node0884 node0884_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2938 node2938_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1205 node1205_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2486 node2486_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1491 node1491_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2236 node2236_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1744 node1744_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node0915 node0915_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node0942 node0942_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node0965 node0965_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1756 node1756_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1503 node1503_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1244 node1244_mem))))))))))))))

def node5740 : WordRow := [([0, 16, 17, 17], 1)]

def node5740Raw : WordRow := multiplyRow 0 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5740_check :
    collect (scaleRow 1 node5740Raw ++ scaleRow (-(1 : ℤ)) node5740 ++
      ([])) = [] := by
  decide +kernel

theorem node5740_mem : rowEval varIndex node5740 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5740Raw node5740 ([])
    (1) (1) (by decide) node5740_check
  · rw [node5740Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5742 : WordRow := [([2, 16, 17, 17], 1)]

def node5742Raw : WordRow := multiplyRow 2 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5742_check :
    collect (scaleRow 1 node5742Raw ++ scaleRow (-(1 : ℤ)) node5742 ++
      ([])) = [] := by
  decide +kernel

theorem node5742_mem : rowEval varIndex node5742 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5742Raw node5742 ([])
    (1) (1) (by decide) node5742_check
  · rw [node5742Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5744 : WordRow := [([4, 16, 17, 17], 1)]

def node5744Raw : WordRow := multiplyRow 4 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5744_check :
    collect (scaleRow 1 node5744Raw ++ scaleRow (-(1 : ℤ)) node5744 ++
      ([])) = [] := by
  decide +kernel

theorem node5744_mem : rowEval varIndex node5744 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5744Raw node5744 ([])
    (1) (1) (by decide) node5744_check
  · rw [node5744Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5746 : WordRow := [([6, 16, 17, 17], 1)]

def node5746Raw : WordRow := multiplyRow 6 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5746_check :
    collect (scaleRow 1 node5746Raw ++ scaleRow (-(1 : ℤ)) node5746 ++
      ([])) = [] := by
  decide +kernel

theorem node5746_mem : rowEval varIndex node5746 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5746Raw node5746 ([])
    (1) (1) (by decide) node5746_check
  · rw [node5746Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

def node5748 : WordRow := [([8, 16, 17, 17], 1)]

def node5748Raw : WordRow := multiplyRow 8 node0771

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5748_check :
    collect (scaleRow 1 node5748Raw ++ scaleRow (-(1 : ℤ)) node5748 ++
      ([])) = [] := by
  decide +kernel

theorem node5748_mem : rowEval varIndex node5748 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5748Raw node5748 ([])
    (1) (1) (by decide) node5748_check
  · rw [node5748Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0771_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node5748_mem
