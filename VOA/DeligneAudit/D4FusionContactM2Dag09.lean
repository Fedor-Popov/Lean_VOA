import VOA.DeligneAudit.D4FusionContactM2Dag08

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node2305 : WordRow := [([0, 6, 9, 10], 1), ([1, 6, 8, 10], 1), ([2, 5, 6, 10], -1), ([3, 4, 6, 10], -1)]

def node2305Raw : WordRow := multiplyRow 10 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2305_check :
    collect (scaleRow 1 node2305Raw ++ scaleRow (-(1 : ℤ)) node2305 ++
      ([])) = [] := by
  decide +kernel

theorem node2305_mem : rowEval varIndex node2305 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2305Raw node2305 ([])
    (1) (1) (by decide) node2305_check
  · rw [node2305Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2307 : WordRow := [([0, 6, 9, 12], 1), ([1, 6, 8, 12], 1), ([2, 5, 6, 12], -1), ([3, 4, 6, 12], -1)]

def node2307Raw : WordRow := multiplyRow 12 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2307_check :
    collect (scaleRow 1 node2307Raw ++ scaleRow (-(1 : ℤ)) node2307 ++
      ([])) = [] := by
  decide +kernel

theorem node2307_mem : rowEval varIndex node2307 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2307Raw node2307 ([])
    (1) (1) (by decide) node2307_check
  · rw [node2307Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2309 : WordRow := [([0, 6, 9, 14], 1), ([1, 6, 8, 14], 1), ([2, 5, 6, 14], -1), ([3, 4, 6, 14], -1)]

def node2309Raw : WordRow := multiplyRow 14 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2309_check :
    collect (scaleRow 1 node2309Raw ++ scaleRow (-(1 : ℤ)) node2309 ++
      ([])) = [] := by
  decide +kernel

theorem node2309_mem : rowEval varIndex node2309 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2309Raw node2309 ([])
    (1) (1) (by decide) node2309_check
  · rw [node2309Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2311 : WordRow := [([0, 6, 9, 16], 1), ([1, 6, 8, 16], 1), ([2, 5, 6, 16], -1), ([3, 4, 6, 16], -1)]

def node2311Raw : WordRow := multiplyRow 16 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2311_check :
    collect (scaleRow 1 node2311Raw ++ scaleRow (-(1 : ℤ)) node2311 ++
      ([])) = [] := by
  decide +kernel

theorem node2311_mem : rowEval varIndex node2311 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2311Raw node2311 ([])
    (1) (1) (by decide) node2311_check
  · rw [node2311Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2312 : WordRow := [([0, 6, 9, 17], 1), ([1, 6, 8, 17], 1), ([2, 5, 6, 17], -1), ([3, 4, 6, 17], -1)]

def node2312Raw : WordRow := multiplyRow 17 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2312_check :
    collect (scaleRow 1 node2312Raw ++ scaleRow (-(1 : ℤ)) node2312 ++
      ([])) = [] := by
  decide +kernel

theorem node2312_mem : rowEval varIndex node2312 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2312Raw node2312 ([])
    (1) (1) (by decide) node2312_check
  · rw [node2312Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2316 : WordRow := [([1, 6, 9, 10], 1), ([1, 7, 8, 10], -1), ([2, 5, 7, 10], 1), ([3, 4, 7, 10], 1)]

def node2316Raw : WordRow := multiplyRow 10 node0220

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2316_check :
    collect (scaleRow 1 node2316Raw ++ scaleRow (-(1 : ℤ)) node2316 ++
      ([])) = [] := by
  decide +kernel

theorem node2316_mem : rowEval varIndex node2316 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2316Raw node2316 ([])
    (1) (1) (by decide) node2316_check
  · rw [node2316Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0220_mem
  · exact candidateIdeal.zero_mem

def node2318 : WordRow := [([1, 6, 9, 12], 1), ([1, 7, 8, 12], -1), ([2, 5, 7, 12], 1), ([3, 4, 7, 12], 1)]

def node2318Raw : WordRow := multiplyRow 12 node0220

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2318_check :
    collect (scaleRow 1 node2318Raw ++ scaleRow (-(1 : ℤ)) node2318 ++
      ([])) = [] := by
  decide +kernel

theorem node2318_mem : rowEval varIndex node2318 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2318Raw node2318 ([])
    (1) (1) (by decide) node2318_check
  · rw [node2318Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0220_mem
  · exact candidateIdeal.zero_mem

def node2320 : WordRow := [([1, 6, 9, 14], 1), ([1, 7, 8, 14], -1), ([2, 5, 7, 14], 1), ([3, 4, 7, 14], 1)]

def node2320Raw : WordRow := multiplyRow 14 node0220

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2320_check :
    collect (scaleRow 1 node2320Raw ++ scaleRow (-(1 : ℤ)) node2320 ++
      ([])) = [] := by
  decide +kernel

theorem node2320_mem : rowEval varIndex node2320 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2320Raw node2320 ([])
    (1) (1) (by decide) node2320_check
  · rw [node2320Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0220_mem
  · exact candidateIdeal.zero_mem

def node2332 : WordRow := [([0, 8, 9, 16], 1), ([1, 8, 8, 16], 1), ([2, 5, 8, 16], -1), ([3, 4, 8, 16], -1)]

def node2332Raw : WordRow := multiplyRow 16 node0221

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2332_check :
    collect (scaleRow 1 node2332Raw ++ scaleRow (-(1 : ℤ)) node2332 ++
      ([])) = [] := by
  decide +kernel

theorem node2332_mem : rowEval varIndex node2332 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2332Raw node2332 ([])
    (1) (1) (by decide) node2332_check
  · rw [node2332Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0221_mem
  · exact candidateIdeal.zero_mem

def node2349 : WordRow := [([0, 9, 10, 16], 1), ([1, 8, 10, 16], 1), ([2, 5, 10, 16], -1), ([3, 4, 10, 16], -1)]

def node2349Raw : WordRow := multiplyRow 16 node0223

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2349_check :
    collect (scaleRow 1 node2349Raw ++ scaleRow (-(1 : ℤ)) node2349 ++
      ([])) = [] := by
  decide +kernel

theorem node2349_mem : rowEval varIndex node2349 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2349Raw node2349 ([])
    (1) (1) (by decide) node2349_check
  · rw [node2349Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0223_mem
  · exact candidateIdeal.zero_mem

def node2350 : WordRow := [([0, 9, 10, 17], 1), ([1, 8, 10, 17], 1), ([2, 5, 10, 17], -1), ([3, 4, 10, 17], -1)]

def node2350Raw : WordRow := multiplyRow 17 node0223

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2350_check :
    collect (scaleRow 1 node2350Raw ++ scaleRow (-(1 : ℤ)) node2350 ++
      ([])) = [] := by
  decide +kernel

theorem node2350_mem : rowEval varIndex node2350 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2350Raw node2350 ([])
    (1) (1) (by decide) node2350_check
  · rw [node2350Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0223_mem
  · exact candidateIdeal.zero_mem

def node2356 : WordRow := [([0, 9, 11, 16], 1), ([1, 8, 11, 16], 1), ([2, 5, 11, 16], -1), ([3, 4, 11, 16], -1)]

def node2356Raw : WordRow := multiplyRow 16 node0224

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2356_check :
    collect (scaleRow 1 node2356Raw ++ scaleRow (-(1 : ℤ)) node2356 ++
      ([])) = [] := by
  decide +kernel

theorem node2356_mem : rowEval varIndex node2356 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2356Raw node2356 ([])
    (1) (1) (by decide) node2356_check
  · rw [node2356Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0224_mem
  · exact candidateIdeal.zero_mem

def node2362 : WordRow := [([0, 9, 12, 16], 1), ([1, 8, 12, 16], 1), ([2, 5, 12, 16], -1), ([3, 4, 12, 16], -1)]

def node2362Raw : WordRow := multiplyRow 16 node0225

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2362_check :
    collect (scaleRow 1 node2362Raw ++ scaleRow (-(1 : ℤ)) node2362 ++
      ([])) = [] := by
  decide +kernel

theorem node2362_mem : rowEval varIndex node2362 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2362Raw node2362 ([])
    (1) (1) (by decide) node2362_check
  · rw [node2362Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0225_mem
  · exact candidateIdeal.zero_mem

def node2363 : WordRow := [([0, 9, 12, 17], 1), ([1, 8, 12, 17], 1), ([2, 5, 12, 17], -1), ([3, 4, 12, 17], -1)]

def node2363Raw : WordRow := multiplyRow 17 node0225

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2363_check :
    collect (scaleRow 1 node2363Raw ++ scaleRow (-(1 : ℤ)) node2363 ++
      ([])) = [] := by
  decide +kernel

theorem node2363_mem : rowEval varIndex node2363 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2363Raw node2363 ([])
    (1) (1) (by decide) node2363_check
  · rw [node2363Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0225_mem
  · exact candidateIdeal.zero_mem

def node2367 : WordRow := [([0, 9, 13, 16], 1), ([1, 8, 13, 16], 1), ([2, 5, 13, 16], -1), ([3, 4, 13, 16], -1)]

def node2367Raw : WordRow := multiplyRow 16 node0226

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2367_check :
    collect (scaleRow 1 node2367Raw ++ scaleRow (-(1 : ℤ)) node2367 ++
      ([])) = [] := by
  decide +kernel

theorem node2367_mem : rowEval varIndex node2367 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2367Raw node2367 ([])
    (1) (1) (by decide) node2367_check
  · rw [node2367Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0226_mem
  · exact candidateIdeal.zero_mem

def node2371 : WordRow := [([0, 9, 14, 16], 1), ([1, 8, 14, 16], 1), ([2, 5, 14, 16], -1), ([3, 4, 14, 16], -1)]

def node2371Raw : WordRow := multiplyRow 16 node0227

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2371_check :
    collect (scaleRow 1 node2371Raw ++ scaleRow (-(1 : ℤ)) node2371 ++
      ([])) = [] := by
  decide +kernel

theorem node2371_mem : rowEval varIndex node2371 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2371Raw node2371 ([])
    (1) (1) (by decide) node2371_check
  · rw [node2371Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0227_mem
  · exact candidateIdeal.zero_mem

def node2377 : WordRow := [([0, 9, 16, 17], 1), ([1, 8, 16, 17], 1), ([2, 5, 16, 17], -1), ([3, 4, 16, 17], -1)]

def node2377Raw : WordRow := multiplyRow 17 node0229

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2377_check :
    collect (scaleRow 1 node2377Raw ++ scaleRow (-(1 : ℤ)) node2377 ++
      ([])) = [] := by
  decide +kernel

theorem node2377_mem : rowEval varIndex node2377 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2377Raw node2377 ([])
    (1) (1) (by decide) node2377_check
  · rw [node2377Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0229_mem
  · exact candidateIdeal.zero_mem

def node2381 : WordRow := [([2, 5, 5, 6], 1), ([3, 4, 5, 6], 2)]

def node2381Raw : WordRow := multiplyRow 6 node0231

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2381_check :
    collect (scaleRow 1 node2381Raw ++ scaleRow (-(1 : ℤ)) node2381 ++
      ([])) = [] := by
  decide +kernel

theorem node2381_mem : rowEval varIndex node2381 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2381Raw node2381 ([])
    (1) (1) (by decide) node2381_check
  · rw [node2381Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0231_mem
  · exact candidateIdeal.zero_mem

def node2385 : WordRow := [([2, 5, 5, 10], 1), ([3, 4, 5, 10], 2)]

def node2385Raw : WordRow := multiplyRow 10 node0231

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2385_check :
    collect (scaleRow 1 node2385Raw ++ scaleRow (-(1 : ℤ)) node2385 ++
      ([])) = [] := by
  decide +kernel

theorem node2385_mem : rowEval varIndex node2385 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2385Raw node2385 ([])
    (1) (1) (by decide) node2385_check
  · rw [node2385Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0231_mem
  · exact candidateIdeal.zero_mem

def node2406 : WordRow := [([2, 5, 6, 7], 1), ([3, 4, 6, 7], 1), ([3, 5, 6, 6], 1)]

def node2406Raw : WordRow := multiplyRow 6 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2406_check :
    collect (scaleRow 1 node2406Raw ++ scaleRow (-(1 : ℤ)) node2406 ++
      ([])) = [] := by
  decide +kernel

theorem node2406_mem : rowEval varIndex node2406 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2406Raw node2406 ([])
    (1) (1) (by decide) node2406_check
  · rw [node2406Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2408 : WordRow := [([2, 5, 7, 8], 1), ([3, 4, 7, 8], 1), ([3, 5, 6, 8], 1)]

def node2408Raw : WordRow := multiplyRow 8 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2408_check :
    collect (scaleRow 1 node2408Raw ++ scaleRow (-(1 : ℤ)) node2408 ++
      ([])) = [] := by
  decide +kernel

theorem node2408_mem : rowEval varIndex node2408 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2408Raw node2408 ([])
    (1) (1) (by decide) node2408_check
  · rw [node2408Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2410 : WordRow := [([2, 5, 7, 10], 1), ([3, 4, 7, 10], 1), ([3, 5, 6, 10], 1)]

def node2410Raw : WordRow := multiplyRow 10 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2410_check :
    collect (scaleRow 1 node2410Raw ++ scaleRow (-(1 : ℤ)) node2410 ++
      ([])) = [] := by
  decide +kernel

theorem node2410_mem : rowEval varIndex node2410 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2410Raw node2410 ([])
    (1) (1) (by decide) node2410_check
  · rw [node2410Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2412 : WordRow := [([2, 5, 7, 12], 1), ([3, 4, 7, 12], 1), ([3, 5, 6, 12], 1)]

def node2412Raw : WordRow := multiplyRow 12 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2412_check :
    collect (scaleRow 1 node2412Raw ++ scaleRow (-(1 : ℤ)) node2412 ++
      ([])) = [] := by
  decide +kernel

theorem node2412_mem : rowEval varIndex node2412 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2412Raw node2412 ([])
    (1) (1) (by decide) node2412_check
  · rw [node2412Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2414 : WordRow := [([2, 5, 7, 14], 1), ([3, 4, 7, 14], 1), ([3, 5, 6, 14], 1)]

def node2414Raw : WordRow := multiplyRow 14 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2414_check :
    collect (scaleRow 1 node2414Raw ++ scaleRow (-(1 : ℤ)) node2414 ++
      ([])) = [] := by
  decide +kernel

theorem node2414_mem : rowEval varIndex node2414 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2414Raw node2414 ([])
    (1) (1) (by decide) node2414_check
  · rw [node2414Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2416 : WordRow := [([2, 5, 7, 16], 1), ([3, 4, 7, 16], 1), ([3, 5, 6, 16], 1)]

def node2416Raw : WordRow := multiplyRow 16 node0233

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2416_check :
    collect (scaleRow 1 node2416Raw ++ scaleRow (-(1 : ℤ)) node2416 ++
      ([])) = [] := by
  decide +kernel

theorem node2416_mem : rowEval varIndex node2416 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2416Raw node2416 ([])
    (1) (1) (by decide) node2416_check
  · rw [node2416Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0233_mem
  · exact candidateIdeal.zero_mem

def node2450 : WordRow := [([1, 9, 10, 12], 1), ([3, 5, 10, 12], -1)]

def node2450Raw : WordRow := multiplyRow 12 node0237

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2450_check :
    collect (scaleRow 1 node2450Raw ++ scaleRow (-(1 : ℤ)) node2450 ++
      ([])) = [] := by
  decide +kernel

theorem node2450_mem : rowEval varIndex node2450 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2450Raw node2450 ([])
    (1) (1) (by decide) node2450_check
  · rw [node2450Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0237_mem
  · exact candidateIdeal.zero_mem

def node2452 : WordRow := [([1, 9, 10, 14], 1), ([3, 5, 10, 14], -1)]

def node2452Raw : WordRow := multiplyRow 14 node0237

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2452_check :
    collect (scaleRow 1 node2452Raw ++ scaleRow (-(1 : ℤ)) node2452 ++
      ([])) = [] := by
  decide +kernel

theorem node2452_mem : rowEval varIndex node2452 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2452Raw node2452 ([])
    (1) (1) (by decide) node2452_check
  · rw [node2452Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0237_mem
  · exact candidateIdeal.zero_mem

def node2465 : WordRow := [([1, 9, 12, 14], 1), ([3, 5, 12, 14], -1)]

def node2465Raw : WordRow := multiplyRow 14 node0239

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2465_check :
    collect (scaleRow 1 node2465Raw ++ scaleRow (-(1 : ℤ)) node2465 ++
      ([])) = [] := by
  decide +kernel

theorem node2465_mem : rowEval varIndex node2465 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2465Raw node2465 ([])
    (1) (1) (by decide) node2465_check
  · rw [node2465Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0239_mem
  · exact candidateIdeal.zero_mem

def node2486 : WordRow := [([0, 0, 4, 11], 1), ([0, 1, 4, 10], 1), ([0, 2, 4, 7], -1), ([0, 3, 4, 6], -1)]

def node2486Raw : WordRow := multiplyRow 4 node0245

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2486_check :
    collect (scaleRow 1 node2486Raw ++ scaleRow (-(1 : ℤ)) node2486 ++
      ([])) = [] := by
  decide +kernel

theorem node2486_mem : rowEval varIndex node2486 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2486Raw node2486 ([])
    (1) (1) (by decide) node2486_check
  · rw [node2486Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0245_mem
  · exact candidateIdeal.zero_mem

def node2496 : WordRow := [([0, 0, 11, 16], 1), ([0, 1, 10, 16], 1), ([0, 2, 7, 16], -1), ([0, 3, 6, 16], -1)]

def node2496Raw : WordRow := multiplyRow 16 node0245

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2496_check :
    collect (scaleRow 1 node2496Raw ++ scaleRow (-(1 : ℤ)) node2496 ++
      ([])) = [] := by
  decide +kernel

theorem node2496_mem : rowEval varIndex node2496 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2496Raw node2496 ([])
    (1) (1) (by decide) node2496_check
  · rw [node2496Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0245_mem
  · exact candidateIdeal.zero_mem

def node2499 : WordRow := [([0, 2, 4, 11], 1), ([1, 2, 4, 10], 1), ([2, 2, 4, 7], -1), ([2, 3, 4, 6], -1)]

def node2499Raw : WordRow := multiplyRow 4 node0246

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2499_check :
    collect (scaleRow 1 node2499Raw ++ scaleRow (-(1 : ℤ)) node2499 ++
      ([])) = [] := by
  decide +kernel

theorem node2499_mem : rowEval varIndex node2499 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2499Raw node2499 ([])
    (1) (1) (by decide) node2499_check
  · rw [node2499Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0246_mem
  · exact candidateIdeal.zero_mem

def node2510 : WordRow := [([0, 2, 11, 16], 1), ([1, 2, 10, 16], 1), ([2, 2, 7, 16], -1), ([2, 3, 6, 16], -1)]

def node2510Raw : WordRow := multiplyRow 16 node0246

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2510_check :
    collect (scaleRow 1 node2510Raw ++ scaleRow (-(1 : ℤ)) node2510 ++
      ([])) = [] := by
  decide +kernel

theorem node2510_mem : rowEval varIndex node2510 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2510Raw node2510 ([])
    (1) (1) (by decide) node2510_check
  · rw [node2510Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0246_mem
  · exact candidateIdeal.zero_mem

def node2522 : WordRow := [([0, 4, 4, 11], 1), ([1, 4, 4, 10], 1), ([2, 4, 4, 7], -1), ([3, 4, 4, 6], -1)]

def node2522Raw : WordRow := multiplyRow 4 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2522_check :
    collect (scaleRow 1 node2522Raw ++ scaleRow (-(1 : ℤ)) node2522 ++
      ([])) = [] := by
  decide +kernel

theorem node2522_mem : rowEval varIndex node2522 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2522Raw node2522 ([])
    (1) (1) (by decide) node2522_check
  · rw [node2522Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2523 : WordRow := [([1, 4, 4, 11], 1), ([1, 4, 5, 10], -1), ([2, 4, 5, 7], 1), ([3, 4, 5, 6], 1)]

def node2523Raw : WordRow := multiplyRow 5 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2523_check :
    collect (scaleRow 1 node2523Raw ++ scaleRow (-(-1 : ℤ)) node2523 ++
      (scaleRow (-1) node1536)) = [] := by
  decide +kernel

theorem node2523_mem : rowEval varIndex node2523 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2523Raw node2523 (scaleRow (-1) node1536)
    (1) (-1) (by decide) node2523_check
  · rw [node2523Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node1536 node1536_mem)

def node2524 : WordRow := [([0, 4, 6, 11], 1), ([1, 4, 6, 10], 1), ([2, 4, 6, 7], -1), ([3, 4, 6, 6], -1)]

def node2524Raw : WordRow := multiplyRow 6 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2524_check :
    collect (scaleRow 1 node2524Raw ++ scaleRow (-(1 : ℤ)) node2524 ++
      ([])) = [] := by
  decide +kernel

theorem node2524_mem : rowEval varIndex node2524 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2524Raw node2524 ([])
    (1) (1) (by decide) node2524_check
  · rw [node2524Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2526 : WordRow := [([0, 4, 8, 11], 1), ([1, 4, 8, 10], 1), ([2, 4, 7, 8], -1), ([3, 4, 6, 8], -1)]

def node2526Raw : WordRow := multiplyRow 8 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2526_check :
    collect (scaleRow 1 node2526Raw ++ scaleRow (-(1 : ℤ)) node2526 ++
      ([])) = [] := by
  decide +kernel

theorem node2526_mem : rowEval varIndex node2526 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2526Raw node2526 ([])
    (1) (1) (by decide) node2526_check
  · rw [node2526Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2527 : WordRow := [([1, 4, 8, 11], 1), ([1, 4, 9, 10], -1), ([2, 4, 5, 11], -1), ([2, 4, 7, 9], 1), ([3, 4, 4, 11], -1), ([3, 4, 6, 9], 1)]

def node2527Raw : WordRow := multiplyRow 9 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2527_check :
    collect (scaleRow 1 node2527Raw ++ scaleRow (-(-1 : ℤ)) node2527 ++
      (scaleRow (-1) node2281)) = [] := by
  decide +kernel

theorem node2527_mem : rowEval varIndex node2527 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2527Raw node2527 (scaleRow (-1) node2281)
    (1) (-1) (by decide) node2527_check
  · rw [node2527Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node2281 node2281_mem)

def node2528 : WordRow := [([0, 4, 10, 11], 1), ([1, 4, 10, 10], 1), ([2, 4, 7, 10], -1), ([3, 4, 6, 10], -1)]

def node2528Raw : WordRow := multiplyRow 10 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2528_check :
    collect (scaleRow 1 node2528Raw ++ scaleRow (-(1 : ℤ)) node2528 ++
      ([])) = [] := by
  decide +kernel

theorem node2528_mem : rowEval varIndex node2528 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2528Raw node2528 ([])
    (1) (1) (by decide) node2528_check
  · rw [node2528Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2530 : WordRow := [([0, 4, 11, 12], 1), ([1, 4, 10, 12], 1), ([2, 4, 7, 12], -1), ([3, 4, 6, 12], -1)]

def node2530Raw : WordRow := multiplyRow 12 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2530_check :
    collect (scaleRow 1 node2530Raw ++ scaleRow (-(1 : ℤ)) node2530 ++
      ([])) = [] := by
  decide +kernel

theorem node2530_mem : rowEval varIndex node2530 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2530Raw node2530 ([])
    (1) (1) (by decide) node2530_check
  · rw [node2530Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2532 : WordRow := [([0, 4, 11, 14], 1), ([1, 4, 10, 14], 1), ([2, 4, 7, 14], -1), ([3, 4, 6, 14], -1)]

def node2532Raw : WordRow := multiplyRow 14 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2532_check :
    collect (scaleRow 1 node2532Raw ++ scaleRow (-(1 : ℤ)) node2532 ++
      ([])) = [] := by
  decide +kernel

theorem node2532_mem : rowEval varIndex node2532 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2532Raw node2532 ([])
    (1) (1) (by decide) node2532_check
  · rw [node2532Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2534 : WordRow := [([0, 4, 11, 16], 1), ([1, 4, 10, 16], 1), ([2, 4, 7, 16], -1), ([3, 4, 6, 16], -1)]

def node2534Raw : WordRow := multiplyRow 16 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2534_check :
    collect (scaleRow 1 node2534Raw ++ scaleRow (-(1 : ℤ)) node2534 ++
      ([])) = [] := by
  decide +kernel

theorem node2534_mem : rowEval varIndex node2534 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2534Raw node2534 ([])
    (1) (1) (by decide) node2534_check
  · rw [node2534Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2535 : WordRow := [([0, 4, 11, 17], 1), ([1, 4, 10, 17], 1), ([2, 4, 7, 17], -1), ([3, 4, 6, 17], -1)]

def node2535Raw : WordRow := multiplyRow 17 node0248

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2535_check :
    collect (scaleRow 1 node2535Raw ++ scaleRow (-(1 : ℤ)) node2535 ++
      ([])) = [] := by
  decide +kernel

theorem node2535_mem : rowEval varIndex node2535 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2535Raw node2535 ([])
    (1) (1) (by decide) node2535_check
  · rw [node2535Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0248_mem
  · exact candidateIdeal.zero_mem

def node2538 : WordRow := [([2, 4, 5, 11], 1), ([2, 4, 7, 9], -1), ([2, 5, 5, 10], -1), ([2, 5, 7, 8], 1), ([3, 4, 4, 11], 1), ([3, 4, 5, 10], -1), ([3, 4, 6, 9], -1), ([3, 5, 6, 8], 1)]

def node2538Raw : WordRow := multiplyRow 8 node0249

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2538_check :
    collect (scaleRow 1 node2538Raw ++ scaleRow (-(1 : ℤ)) node2538 ++
      (scaleRow (-1) node2527 ++ scaleRow (-1) node2293)) = [] := by
  decide +kernel

theorem node2538_mem : rowEval varIndex node2538 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2538Raw node2538 (scaleRow (-1) node2527 ++ scaleRow (-1) node2293)
    (1) (1) (by decide) node2538_check
  · rw [node2538Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0249_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2527 node2527_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2293 node2293_mem))

def node2544 : WordRow := [([1, 4, 11, 14], 1), ([1, 5, 10, 14], -1), ([2, 5, 7, 14], 1), ([3, 5, 6, 14], 1)]

def node2544Raw : WordRow := multiplyRow 14 node0249

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2544_check :
    collect (scaleRow 1 node2544Raw ++ scaleRow (-(1 : ℤ)) node2544 ++
      ([])) = [] := by
  decide +kernel

theorem node2544_mem : rowEval varIndex node2544 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2544Raw node2544 ([])
    (1) (1) (by decide) node2544_check
  · rw [node2544Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0249_mem
  · exact candidateIdeal.zero_mem

def node2558 : WordRow := [([0, 6, 11, 16], 1), ([1, 6, 10, 16], 1), ([2, 6, 7, 16], -1), ([3, 6, 6, 16], -1)]

def node2558Raw : WordRow := multiplyRow 16 node0250

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2558_check :
    collect (scaleRow 1 node2558Raw ++ scaleRow (-(1 : ℤ)) node2558 ++
      ([])) = [] := by
  decide +kernel

theorem node2558_mem : rowEval varIndex node2558 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2558Raw node2558 ([])
    (1) (1) (by decide) node2558_check
  · rw [node2558Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0250_mem
  · exact candidateIdeal.zero_mem

def node2576 : WordRow := [([0, 8, 11, 13], 1), ([1, 8, 10, 13], 1), ([2, 7, 8, 13], -1), ([3, 6, 8, 13], -1)]

def node2576Raw : WordRow := multiplyRow 13 node0252

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2576_check :
    collect (scaleRow 1 node2576Raw ++ scaleRow (-(1 : ℤ)) node2576 ++
      ([])) = [] := by
  decide +kernel

theorem node2576_mem : rowEval varIndex node2576 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2576Raw node2576 ([])
    (1) (1) (by decide) node2576_check
  · rw [node2576Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0252_mem
  · exact candidateIdeal.zero_mem

def node2579 : WordRow := [([0, 8, 11, 16], 1), ([1, 8, 10, 16], 1), ([2, 7, 8, 16], -1), ([3, 6, 8, 16], -1)]

def node2579Raw : WordRow := multiplyRow 16 node0252

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2579_check :
    collect (scaleRow 1 node2579Raw ++ scaleRow (-(1 : ℤ)) node2579 ++
      ([])) = [] := by
  decide +kernel

theorem node2579_mem : rowEval varIndex node2579 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2579Raw node2579 ([])
    (1) (1) (by decide) node2579_check
  · rw [node2579Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0252_mem
  · exact candidateIdeal.zero_mem

def node2580 : WordRow := [([0, 8, 11, 17], 1), ([1, 8, 10, 17], 1), ([2, 7, 8, 17], -1), ([3, 6, 8, 17], -1)]

def node2580Raw : WordRow := multiplyRow 17 node0252

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2580_check :
    collect (scaleRow 1 node2580Raw ++ scaleRow (-(1 : ℤ)) node2580 ++
      ([])) = [] := by
  decide +kernel

theorem node2580_mem : rowEval varIndex node2580 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2580Raw node2580 ([])
    (1) (1) (by decide) node2580_check
  · rw [node2580Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0252_mem
  · exact candidateIdeal.zero_mem

def node2584 : WordRow := [([1, 8, 11, 12], 1), ([1, 9, 10, 12], -1), ([2, 5, 11, 12], -1), ([2, 7, 9, 12], 1), ([3, 4, 11, 12], -1), ([3, 6, 9, 12], 1)]

def node2584Raw : WordRow := multiplyRow 12 node0253

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2584_check :
    collect (scaleRow 1 node2584Raw ++ scaleRow (-(1 : ℤ)) node2584 ++
      ([])) = [] := by
  decide +kernel

theorem node2584_mem : rowEval varIndex node2584 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2584Raw node2584 ([])
    (1) (1) (by decide) node2584_check
  · rw [node2584Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0253_mem
  · exact candidateIdeal.zero_mem

def node2586 : WordRow := [([1, 8, 11, 14], 1), ([1, 9, 10, 14], -1), ([2, 5, 11, 14], -1), ([2, 7, 9, 14], 1), ([3, 4, 11, 14], -1), ([3, 6, 9, 14], 1)]

def node2586Raw : WordRow := multiplyRow 14 node0253

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2586_check :
    collect (scaleRow 1 node2586Raw ++ scaleRow (-(1 : ℤ)) node2586 ++
      ([])) = [] := by
  decide +kernel

theorem node2586_mem : rowEval varIndex node2586 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2586Raw node2586 ([])
    (1) (1) (by decide) node2586_check
  · rw [node2586Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0253_mem
  · exact candidateIdeal.zero_mem

def node2596 : WordRow := [([0, 10, 11, 16], 1), ([1, 10, 10, 16], 1), ([2, 7, 10, 16], -1), ([3, 6, 10, 16], -1)]

def node2596Raw : WordRow := multiplyRow 16 node0254

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2596_check :
    collect (scaleRow 1 node2596Raw ++ scaleRow (-(1 : ℤ)) node2596 ++
      ([])) = [] := by
  decide +kernel

theorem node2596_mem : rowEval varIndex node2596 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2596Raw node2596 ([])
    (1) (1) (by decide) node2596_check
  · rw [node2596Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0254_mem
  · exact candidateIdeal.zero_mem

def node2609 : WordRow := [([0, 11, 12, 16], 1), ([1, 10, 12, 16], 1), ([2, 7, 12, 16], -1), ([3, 6, 12, 16], -1)]

def node2609Raw : WordRow := multiplyRow 16 node0256

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2609_check :
    collect (scaleRow 1 node2609Raw ++ scaleRow (-(1 : ℤ)) node2609 ++
      ([])) = [] := by
  decide +kernel

theorem node2609_mem : rowEval varIndex node2609 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2609Raw node2609 ([])
    (1) (1) (by decide) node2609_check
  · rw [node2609Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0256_mem
  · exact candidateIdeal.zero_mem

def node2610 : WordRow := [([0, 11, 12, 17], 1), ([1, 10, 12, 17], 1), ([2, 7, 12, 17], -1), ([3, 6, 12, 17], -1)]

def node2610Raw : WordRow := multiplyRow 17 node0256

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2610_check :
    collect (scaleRow 1 node2610Raw ++ scaleRow (-(1 : ℤ)) node2610 ++
      ([])) = [] := by
  decide +kernel

theorem node2610_mem : rowEval varIndex node2610 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2610Raw node2610 ([])
    (1) (1) (by decide) node2610_check
  · rw [node2610Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0256_mem
  · exact candidateIdeal.zero_mem

def node2614 : WordRow := [([0, 11, 13, 16], 1), ([1, 10, 13, 16], 1), ([2, 7, 13, 16], -1), ([3, 6, 13, 16], -1)]

def node2614Raw : WordRow := multiplyRow 16 node0257

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2614_check :
    collect (scaleRow 1 node2614Raw ++ scaleRow (-(1 : ℤ)) node2614 ++
      ([])) = [] := by
  decide +kernel

theorem node2614_mem : rowEval varIndex node2614 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2614Raw node2614 ([])
    (1) (1) (by decide) node2614_check
  · rw [node2614Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0257_mem
  · exact candidateIdeal.zero_mem

def node2618 : WordRow := [([0, 11, 14, 16], 1), ([1, 10, 14, 16], 1), ([2, 7, 14, 16], -1), ([3, 6, 14, 16], -1)]

def node2618Raw : WordRow := multiplyRow 16 node0258

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2618_check :
    collect (scaleRow 1 node2618Raw ++ scaleRow (-(1 : ℤ)) node2618 ++
      ([])) = [] := by
  decide +kernel

theorem node2618_mem : rowEval varIndex node2618 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2618Raw node2618 ([])
    (1) (1) (by decide) node2618_check
  · rw [node2618Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0258_mem
  · exact candidateIdeal.zero_mem

def node2624 : WordRow := [([0, 11, 16, 17], 1), ([1, 10, 16, 17], 1), ([2, 7, 16, 17], -1), ([3, 6, 16, 17], -1)]

def node2624Raw : WordRow := multiplyRow 17 node0260

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2624_check :
    collect (scaleRow 1 node2624Raw ++ scaleRow (-(1 : ℤ)) node2624 ++
      ([])) = [] := by
  decide +kernel

theorem node2624_mem : rowEval varIndex node2624 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2624Raw node2624 ([])
    (1) (1) (by decide) node2624_check
  · rw [node2624Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0260_mem
  · exact candidateIdeal.zero_mem

def node2653 : WordRow := [([2, 5, 11, 12], 1), ([2, 7, 9, 12], -1), ([3, 4, 11, 12], 1), ([3, 5, 10, 12], 1), ([3, 6, 9, 12], -1), ([3, 7, 8, 12], -1)]

def node2653Raw : WordRow := multiplyRow 12 node0264

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2653_check :
    collect (scaleRow 1 node2653Raw ++ scaleRow (-(1 : ℤ)) node2653 ++
      ([])) = [] := by
  decide +kernel

theorem node2653_mem : rowEval varIndex node2653 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2653Raw node2653 ([])
    (1) (1) (by decide) node2653_check
  · rw [node2653Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0264_mem
  · exact candidateIdeal.zero_mem

def node2655 : WordRow := [([2, 5, 11, 14], 1), ([2, 7, 9, 14], -1), ([3, 4, 11, 14], 1), ([3, 5, 10, 14], 1), ([3, 6, 9, 14], -1), ([3, 7, 8, 14], -1)]

def node2655Raw : WordRow := multiplyRow 14 node0264

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2655_check :
    collect (scaleRow 1 node2655Raw ++ scaleRow (-(1 : ℤ)) node2655 ++
      ([])) = [] := by
  decide +kernel

theorem node2655_mem : rowEval varIndex node2655 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2655Raw node2655 ([])
    (1) (1) (by decide) node2655_check
  · rw [node2655Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0264_mem
  · exact candidateIdeal.zero_mem

def node2657 : WordRow := [([2, 5, 11, 16], 1), ([2, 7, 9, 16], -1), ([3, 4, 11, 16], 1), ([3, 5, 10, 16], 1), ([3, 6, 9, 16], -1), ([3, 7, 8, 16], -1)]

def node2657Raw : WordRow := multiplyRow 16 node0264

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2657_check :
    collect (scaleRow 1 node2657Raw ++ scaleRow (-(1 : ℤ)) node2657 ++
      ([])) = [] := by
  decide +kernel

theorem node2657_mem : rowEval varIndex node2657 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2657Raw node2657 ([])
    (1) (1) (by decide) node2657_check
  · rw [node2657Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0264_mem
  · exact candidateIdeal.zero_mem

def node2709 : WordRow := [([1, 4, 4, 10], 1)]

def node2709Raw : WordRow := multiplyRow 10 node0274

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2709_check :
    collect (scaleRow 1 node2709Raw ++ scaleRow (-(1 : ℤ)) node2709 ++
      ([])) = [] := by
  decide +kernel

theorem node2709_mem : rowEval varIndex node2709 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2709Raw node2709 ([])
    (1) (1) (by decide) node2709_check
  · rw [node2709Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0274_mem
  · exact candidateIdeal.zero_mem

def node2710 : WordRow := [([3, 4, 4, 7], 1)]

def node2710Raw : WordRow := multiplyRow 11 node0274

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2710_check :
    collect (scaleRow 1 node2710Raw ++ scaleRow (-(1 : ℤ)) node2710 ++
      (scaleRow (-1) node2523 ++ scaleRow (-1) node1640 ++ scaleRow (1) node2289 ++ scaleRow (1) node2381)) = [] := by
  decide +kernel

theorem node2710_mem : rowEval varIndex node2710 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2710Raw node2710 (scaleRow (-1) node2523 ++ scaleRow (-1) node1640 ++ scaleRow (1) node2289 ++ scaleRow (1) node2381)
    (1) (1) (by decide) node2710_check
  · rw [node2710Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0274_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2523 node2523_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1640 node1640_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node2289 node2289_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node2381 node2381_mem))))

def node2723 : WordRow := [([2, 4, 5, 10], 1)]

def node2723Raw : WordRow := multiplyRow 10 node0275

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2723_check :
    collect (scaleRow 1 node2723Raw ++ scaleRow (-(1 : ℤ)) node2723 ++
      ([])) = [] := by
  decide +kernel

theorem node2723_mem : rowEval varIndex node2723 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2723Raw node2723 ([])
    (1) (1) (by decide) node2723_check
  · rw [node2723Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0275_mem
  · exact candidateIdeal.zero_mem

def node2724 : WordRow := [([2, 4, 7, 9], 1), ([2, 5, 5, 10], 1), ([2, 5, 7, 8], -1), ([3, 4, 4, 11], -1), ([3, 4, 5, 10], 1), ([3, 4, 6, 9], 1), ([3, 5, 6, 8], -1)]

def node2724Raw : WordRow := multiplyRow 11 node0275

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2724_check :
    collect (scaleRow 1 node2724Raw ++ scaleRow (-(1 : ℤ)) node2724 ++
      (scaleRow (-1) node2538)) = [] := by
  decide +kernel

theorem node2724_mem : rowEval varIndex node2724 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2724Raw node2724 (scaleRow (-1) node2538)
    (1) (1) (by decide) node2724_check
  · rw [node2724Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0275_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node2538 node2538_mem)

def node2730 : WordRow := [([2, 4, 5, 17], 1)]

def node2730Raw : WordRow := multiplyRow 17 node0275

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2730_check :
    collect (scaleRow 1 node2730Raw ++ scaleRow (-(1 : ℤ)) node2730 ++
      ([])) = [] := by
  decide +kernel

theorem node2730_mem : rowEval varIndex node2730 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2730Raw node2730 ([])
    (1) (1) (by decide) node2730_check
  · rw [node2730Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0275_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node2730_mem
