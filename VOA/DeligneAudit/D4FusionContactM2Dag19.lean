import VOA.DeligneAudit.D4FusionContactM2Dag18

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node6431 : WordRow := [([0, 16, 16, 17], 3), ([1, 16, 16, 16], 1)]

def node6431Raw : WordRow := differentiateRow (images 20) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6431_check :
    collect (scaleRow 1 node6431Raw ++ scaleRow (-(1 : ℤ)) node6431 ++
      ([])) = [] := by
  decide +kernel

theorem node6431_mem : rowEval varIndex node6431 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6431Raw node6431 ([])
    (1) (1) (by decide) node6431_check
  · rw [node6431Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6432 : WordRow := [([2, 16, 16, 17], 3), ([3, 16, 16, 16], 1)]

def node6432Raw : WordRow := differentiateRow (images 22) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6432_check :
    collect (scaleRow 1 node6432Raw ++ scaleRow (-(1 : ℤ)) node6432 ++
      ([])) = [] := by
  decide +kernel

theorem node6432_mem : rowEval varIndex node6432 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6432Raw node6432 ([])
    (1) (1) (by decide) node6432_check
  · rw [node6432Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6433 : WordRow := [([4, 16, 16, 17], 3), ([5, 16, 16, 16], 1)]

def node6433Raw : WordRow := differentiateRow (images 24) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6433_check :
    collect (scaleRow 1 node6433Raw ++ scaleRow (-(1 : ℤ)) node6433 ++
      ([])) = [] := by
  decide +kernel

theorem node6433_mem : rowEval varIndex node6433 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6433Raw node6433 ([])
    (1) (1) (by decide) node6433_check
  · rw [node6433Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6434 : WordRow := [([6, 16, 16, 17], 3), ([7, 16, 16, 16], 1)]

def node6434Raw : WordRow := differentiateRow (images 26) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6434_check :
    collect (scaleRow 1 node6434Raw ++ scaleRow (-(1 : ℤ)) node6434 ++
      ([])) = [] := by
  decide +kernel

theorem node6434_mem : rowEval varIndex node6434 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6434Raw node6434 ([])
    (1) (1) (by decide) node6434_check
  · rw [node6434Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6435 : WordRow := [([8, 16, 16, 17], 3), ([9, 16, 16, 16], 1)]

def node6435Raw : WordRow := differentiateRow (images 28) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6435_check :
    collect (scaleRow 1 node6435Raw ++ scaleRow (-(1 : ℤ)) node6435 ++
      ([])) = [] := by
  decide +kernel

theorem node6435_mem : rowEval varIndex node6435 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6435Raw node6435 ([])
    (1) (1) (by decide) node6435_check
  · rw [node6435Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6436 : WordRow := [([10, 16, 16, 17], 3), ([11, 16, 16, 16], 1)]

def node6436Raw : WordRow := differentiateRow (images 30) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6436_check :
    collect (scaleRow 1 node6436Raw ++ scaleRow (-(1 : ℤ)) node6436 ++
      ([])) = [] := by
  decide +kernel

theorem node6436_mem : rowEval varIndex node6436 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6436Raw node6436 ([])
    (1) (1) (by decide) node6436_check
  · rw [node6436Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6437 : WordRow := [([12, 16, 16, 17], 3), ([13, 16, 16, 16], 1)]

def node6437Raw : WordRow := differentiateRow (images 32) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6437_check :
    collect (scaleRow 1 node6437Raw ++ scaleRow (-(1 : ℤ)) node6437 ++
      ([])) = [] := by
  decide +kernel

theorem node6437_mem : rowEval varIndex node6437 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6437Raw node6437 ([])
    (1) (1) (by decide) node6437_check
  · rw [node6437Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6438 : WordRow := [([14, 16, 16, 17], 3), ([15, 16, 16, 16], 1)]

def node6438Raw : WordRow := differentiateRow (images 34) node6430

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6438_check :
    collect (scaleRow 1 node6438Raw ++ scaleRow (-(1 : ℤ)) node6438 ++
      ([])) = [] := by
  decide +kernel

theorem node6438_mem : rowEval varIndex node6438 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6438Raw node6438 ([])
    (1) (1) (by decide) node6438_check
  · rw [node6438Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6430_mem
  · exact candidateIdeal.zero_mem

def node6439 : WordRow := [([0, 0, 16, 17], 1), ([0, 1, 16, 16], 1)]

def node6439Raw : WordRow := differentiateRow (images 20) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6439_check :
    collect (scaleRow 1 node6439Raw ++ scaleRow (-(6 : ℤ)) node6439 ++
      ([])) = [] := by
  decide +kernel

theorem node6439_mem : rowEval varIndex node6439 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6439Raw node6439 ([])
    (1) (6) (by decide) node6439_check
  · rw [node6439Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6440 : WordRow := [([0, 2, 16, 17], 2), ([0, 3, 16, 16], 1), ([1, 2, 16, 16], 1)]

def node6440Raw : WordRow := differentiateRow (images 22) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6440_check :
    collect (scaleRow 1 node6440Raw ++ scaleRow (-(3 : ℤ)) node6440 ++
      ([])) = [] := by
  decide +kernel

theorem node6440_mem : rowEval varIndex node6440 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6440Raw node6440 ([])
    (1) (3) (by decide) node6440_check
  · rw [node6440Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6441 : WordRow := [([0, 4, 16, 17], 2), ([0, 5, 16, 16], 1), ([1, 4, 16, 16], 1)]

def node6441Raw : WordRow := differentiateRow (images 24) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6441_check :
    collect (scaleRow 1 node6441Raw ++ scaleRow (-(3 : ℤ)) node6441 ++
      ([])) = [] := by
  decide +kernel

theorem node6441_mem : rowEval varIndex node6441 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6441Raw node6441 ([])
    (1) (3) (by decide) node6441_check
  · rw [node6441Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6442 : WordRow := [([0, 6, 16, 17], 2), ([0, 7, 16, 16], 1), ([1, 6, 16, 16], 1)]

def node6442Raw : WordRow := differentiateRow (images 26) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6442_check :
    collect (scaleRow 1 node6442Raw ++ scaleRow (-(3 : ℤ)) node6442 ++
      ([])) = [] := by
  decide +kernel

theorem node6442_mem : rowEval varIndex node6442 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6442Raw node6442 ([])
    (1) (3) (by decide) node6442_check
  · rw [node6442Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6443 : WordRow := [([0, 8, 16, 17], 2), ([0, 9, 16, 16], 1), ([1, 8, 16, 16], 1)]

def node6443Raw : WordRow := differentiateRow (images 28) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6443_check :
    collect (scaleRow 1 node6443Raw ++ scaleRow (-(3 : ℤ)) node6443 ++
      ([])) = [] := by
  decide +kernel

theorem node6443_mem : rowEval varIndex node6443 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6443Raw node6443 ([])
    (1) (3) (by decide) node6443_check
  · rw [node6443Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6444 : WordRow := [([0, 10, 16, 17], 2), ([0, 11, 16, 16], 1), ([1, 10, 16, 16], 1)]

def node6444Raw : WordRow := differentiateRow (images 30) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6444_check :
    collect (scaleRow 1 node6444Raw ++ scaleRow (-(3 : ℤ)) node6444 ++
      ([])) = [] := by
  decide +kernel

theorem node6444_mem : rowEval varIndex node6444 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6444Raw node6444 ([])
    (1) (3) (by decide) node6444_check
  · rw [node6444Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6445 : WordRow := [([0, 12, 16, 17], 2), ([0, 13, 16, 16], 1), ([1, 12, 16, 16], 1)]

def node6445Raw : WordRow := differentiateRow (images 32) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6445_check :
    collect (scaleRow 1 node6445Raw ++ scaleRow (-(3 : ℤ)) node6445 ++
      ([])) = [] := by
  decide +kernel

theorem node6445_mem : rowEval varIndex node6445 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6445Raw node6445 ([])
    (1) (3) (by decide) node6445_check
  · rw [node6445Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6446 : WordRow := [([0, 14, 16, 17], 2), ([0, 15, 16, 16], 1), ([1, 14, 16, 16], 1)]

def node6446Raw : WordRow := differentiateRow (images 34) node6431

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6446_check :
    collect (scaleRow 1 node6446Raw ++ scaleRow (-(3 : ℤ)) node6446 ++
      ([])) = [] := by
  decide +kernel

theorem node6446_mem : rowEval varIndex node6446 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6446Raw node6446 ([])
    (1) (3) (by decide) node6446_check
  · rw [node6446Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6431_mem
  · exact candidateIdeal.zero_mem

def node6447 : WordRow := [([2, 2, 16, 17], 1), ([2, 3, 16, 16], 1)]

def node6447Raw : WordRow := differentiateRow (images 22) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6447_check :
    collect (scaleRow 1 node6447Raw ++ scaleRow (-(6 : ℤ)) node6447 ++
      ([])) = [] := by
  decide +kernel

theorem node6447_mem : rowEval varIndex node6447 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6447Raw node6447 ([])
    (1) (6) (by decide) node6447_check
  · rw [node6447Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6448 : WordRow := [([2, 4, 16, 17], 2), ([2, 5, 16, 16], 1), ([3, 4, 16, 16], 1)]

def node6448Raw : WordRow := differentiateRow (images 24) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6448_check :
    collect (scaleRow 1 node6448Raw ++ scaleRow (-(3 : ℤ)) node6448 ++
      ([])) = [] := by
  decide +kernel

theorem node6448_mem : rowEval varIndex node6448 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6448Raw node6448 ([])
    (1) (3) (by decide) node6448_check
  · rw [node6448Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6449 : WordRow := [([2, 6, 16, 17], 2), ([2, 7, 16, 16], 1), ([3, 6, 16, 16], 1)]

def node6449Raw : WordRow := differentiateRow (images 26) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6449_check :
    collect (scaleRow 1 node6449Raw ++ scaleRow (-(3 : ℤ)) node6449 ++
      ([])) = [] := by
  decide +kernel

theorem node6449_mem : rowEval varIndex node6449 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6449Raw node6449 ([])
    (1) (3) (by decide) node6449_check
  · rw [node6449Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6450 : WordRow := [([2, 8, 16, 17], 2), ([2, 9, 16, 16], 1), ([3, 8, 16, 16], 1)]

def node6450Raw : WordRow := differentiateRow (images 28) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6450_check :
    collect (scaleRow 1 node6450Raw ++ scaleRow (-(3 : ℤ)) node6450 ++
      ([])) = [] := by
  decide +kernel

theorem node6450_mem : rowEval varIndex node6450 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6450Raw node6450 ([])
    (1) (3) (by decide) node6450_check
  · rw [node6450Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6451 : WordRow := [([2, 10, 16, 17], 2), ([2, 11, 16, 16], 1), ([3, 10, 16, 16], 1)]

def node6451Raw : WordRow := differentiateRow (images 30) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6451_check :
    collect (scaleRow 1 node6451Raw ++ scaleRow (-(3 : ℤ)) node6451 ++
      ([])) = [] := by
  decide +kernel

theorem node6451_mem : rowEval varIndex node6451 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6451Raw node6451 ([])
    (1) (3) (by decide) node6451_check
  · rw [node6451Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6452 : WordRow := [([2, 12, 16, 17], 2), ([2, 13, 16, 16], 1), ([3, 12, 16, 16], 1)]

def node6452Raw : WordRow := differentiateRow (images 32) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6452_check :
    collect (scaleRow 1 node6452Raw ++ scaleRow (-(3 : ℤ)) node6452 ++
      ([])) = [] := by
  decide +kernel

theorem node6452_mem : rowEval varIndex node6452 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6452Raw node6452 ([])
    (1) (3) (by decide) node6452_check
  · rw [node6452Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6453 : WordRow := [([2, 14, 16, 17], 2), ([2, 15, 16, 16], 1), ([3, 14, 16, 16], 1)]

def node6453Raw : WordRow := differentiateRow (images 34) node6432

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6453_check :
    collect (scaleRow 1 node6453Raw ++ scaleRow (-(3 : ℤ)) node6453 ++
      ([])) = [] := by
  decide +kernel

theorem node6453_mem : rowEval varIndex node6453 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6453Raw node6453 ([])
    (1) (3) (by decide) node6453_check
  · rw [node6453Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6432_mem
  · exact candidateIdeal.zero_mem

def node6454 : WordRow := [([4, 4, 16, 17], 1), ([4, 5, 16, 16], 1)]

def node6454Raw : WordRow := differentiateRow (images 24) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6454_check :
    collect (scaleRow 1 node6454Raw ++ scaleRow (-(6 : ℤ)) node6454 ++
      ([])) = [] := by
  decide +kernel

theorem node6454_mem : rowEval varIndex node6454 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6454Raw node6454 ([])
    (1) (6) (by decide) node6454_check
  · rw [node6454Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6455 : WordRow := [([4, 6, 16, 17], 2), ([4, 7, 16, 16], 1), ([5, 6, 16, 16], 1)]

def node6455Raw : WordRow := differentiateRow (images 26) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6455_check :
    collect (scaleRow 1 node6455Raw ++ scaleRow (-(3 : ℤ)) node6455 ++
      ([])) = [] := by
  decide +kernel

theorem node6455_mem : rowEval varIndex node6455 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6455Raw node6455 ([])
    (1) (3) (by decide) node6455_check
  · rw [node6455Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6456 : WordRow := [([4, 8, 16, 17], 2), ([4, 9, 16, 16], 1), ([5, 8, 16, 16], 1)]

def node6456Raw : WordRow := differentiateRow (images 28) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6456_check :
    collect (scaleRow 1 node6456Raw ++ scaleRow (-(3 : ℤ)) node6456 ++
      ([])) = [] := by
  decide +kernel

theorem node6456_mem : rowEval varIndex node6456 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6456Raw node6456 ([])
    (1) (3) (by decide) node6456_check
  · rw [node6456Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6457 : WordRow := [([4, 10, 16, 17], 2), ([4, 11, 16, 16], 1), ([5, 10, 16, 16], 1)]

def node6457Raw : WordRow := differentiateRow (images 30) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6457_check :
    collect (scaleRow 1 node6457Raw ++ scaleRow (-(3 : ℤ)) node6457 ++
      ([])) = [] := by
  decide +kernel

theorem node6457_mem : rowEval varIndex node6457 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6457Raw node6457 ([])
    (1) (3) (by decide) node6457_check
  · rw [node6457Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6458 : WordRow := [([4, 12, 16, 17], 2), ([4, 13, 16, 16], 1), ([5, 12, 16, 16], 1)]

def node6458Raw : WordRow := differentiateRow (images 32) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6458_check :
    collect (scaleRow 1 node6458Raw ++ scaleRow (-(3 : ℤ)) node6458 ++
      ([])) = [] := by
  decide +kernel

theorem node6458_mem : rowEval varIndex node6458 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6458Raw node6458 ([])
    (1) (3) (by decide) node6458_check
  · rw [node6458Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6459 : WordRow := [([4, 14, 16, 17], 2), ([4, 15, 16, 16], 1), ([5, 14, 16, 16], 1)]

def node6459Raw : WordRow := differentiateRow (images 34) node6433

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6459_check :
    collect (scaleRow 1 node6459Raw ++ scaleRow (-(3 : ℤ)) node6459 ++
      ([])) = [] := by
  decide +kernel

theorem node6459_mem : rowEval varIndex node6459 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6459Raw node6459 ([])
    (1) (3) (by decide) node6459_check
  · rw [node6459Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6433_mem
  · exact candidateIdeal.zero_mem

def node6460 : WordRow := [([6, 6, 16, 17], 1), ([6, 7, 16, 16], 1)]

def node6460Raw : WordRow := differentiateRow (images 26) node6434

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6460_check :
    collect (scaleRow 1 node6460Raw ++ scaleRow (-(6 : ℤ)) node6460 ++
      ([])) = [] := by
  decide +kernel

theorem node6460_mem : rowEval varIndex node6460 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6460Raw node6460 ([])
    (1) (6) (by decide) node6460_check
  · rw [node6460Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6434_mem
  · exact candidateIdeal.zero_mem

def node6461 : WordRow := [([6, 8, 16, 17], 2), ([6, 9, 16, 16], 1), ([7, 8, 16, 16], 1)]

def node6461Raw : WordRow := differentiateRow (images 28) node6434

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6461_check :
    collect (scaleRow 1 node6461Raw ++ scaleRow (-(3 : ℤ)) node6461 ++
      ([])) = [] := by
  decide +kernel

theorem node6461_mem : rowEval varIndex node6461 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6461Raw node6461 ([])
    (1) (3) (by decide) node6461_check
  · rw [node6461Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6434_mem
  · exact candidateIdeal.zero_mem

def node6462 : WordRow := [([6, 10, 16, 17], 2), ([6, 11, 16, 16], 1), ([7, 10, 16, 16], 1)]

def node6462Raw : WordRow := differentiateRow (images 30) node6434

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6462_check :
    collect (scaleRow 1 node6462Raw ++ scaleRow (-(3 : ℤ)) node6462 ++
      ([])) = [] := by
  decide +kernel

theorem node6462_mem : rowEval varIndex node6462 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6462Raw node6462 ([])
    (1) (3) (by decide) node6462_check
  · rw [node6462Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6434_mem
  · exact candidateIdeal.zero_mem

def node6463 : WordRow := [([6, 12, 16, 17], 2), ([6, 13, 16, 16], 1), ([7, 12, 16, 16], 1)]

def node6463Raw : WordRow := differentiateRow (images 32) node6434

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6463_check :
    collect (scaleRow 1 node6463Raw ++ scaleRow (-(3 : ℤ)) node6463 ++
      ([])) = [] := by
  decide +kernel

theorem node6463_mem : rowEval varIndex node6463 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6463Raw node6463 ([])
    (1) (3) (by decide) node6463_check
  · rw [node6463Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6434_mem
  · exact candidateIdeal.zero_mem

def node6464 : WordRow := [([6, 14, 16, 17], 2), ([6, 15, 16, 16], 1), ([7, 14, 16, 16], 1)]

def node6464Raw : WordRow := differentiateRow (images 34) node6434

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6464_check :
    collect (scaleRow 1 node6464Raw ++ scaleRow (-(3 : ℤ)) node6464 ++
      ([])) = [] := by
  decide +kernel

theorem node6464_mem : rowEval varIndex node6464 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6464Raw node6464 ([])
    (1) (3) (by decide) node6464_check
  · rw [node6464Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6434_mem
  · exact candidateIdeal.zero_mem

def node6465 : WordRow := [([8, 8, 16, 17], 1), ([8, 9, 16, 16], 1)]

def node6465Raw : WordRow := differentiateRow (images 28) node6435

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6465_check :
    collect (scaleRow 1 node6465Raw ++ scaleRow (-(6 : ℤ)) node6465 ++
      ([])) = [] := by
  decide +kernel

theorem node6465_mem : rowEval varIndex node6465 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6465Raw node6465 ([])
    (1) (6) (by decide) node6465_check
  · rw [node6465Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6435_mem
  · exact candidateIdeal.zero_mem

def node6466 : WordRow := [([8, 10, 16, 17], 2), ([8, 11, 16, 16], 1), ([9, 10, 16, 16], 1)]

def node6466Raw : WordRow := differentiateRow (images 30) node6435

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6466_check :
    collect (scaleRow 1 node6466Raw ++ scaleRow (-(3 : ℤ)) node6466 ++
      ([])) = [] := by
  decide +kernel

theorem node6466_mem : rowEval varIndex node6466 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6466Raw node6466 ([])
    (1) (3) (by decide) node6466_check
  · rw [node6466Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6435_mem
  · exact candidateIdeal.zero_mem

def node6467 : WordRow := [([8, 12, 16, 17], 2), ([8, 13, 16, 16], 1), ([9, 12, 16, 16], 1)]

def node6467Raw : WordRow := differentiateRow (images 32) node6435

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6467_check :
    collect (scaleRow 1 node6467Raw ++ scaleRow (-(3 : ℤ)) node6467 ++
      ([])) = [] := by
  decide +kernel

theorem node6467_mem : rowEval varIndex node6467 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6467Raw node6467 ([])
    (1) (3) (by decide) node6467_check
  · rw [node6467Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6435_mem
  · exact candidateIdeal.zero_mem

def node6468 : WordRow := [([8, 14, 16, 17], 2), ([8, 15, 16, 16], 1), ([9, 14, 16, 16], 1)]

def node6468Raw : WordRow := differentiateRow (images 34) node6435

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6468_check :
    collect (scaleRow 1 node6468Raw ++ scaleRow (-(3 : ℤ)) node6468 ++
      ([])) = [] := by
  decide +kernel

theorem node6468_mem : rowEval varIndex node6468 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6468Raw node6468 ([])
    (1) (3) (by decide) node6468_check
  · rw [node6468Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6435_mem
  · exact candidateIdeal.zero_mem

def node6469 : WordRow := [([10, 10, 16, 17], 1), ([10, 11, 16, 16], 1)]

def node6469Raw : WordRow := differentiateRow (images 30) node6436

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6469_check :
    collect (scaleRow 1 node6469Raw ++ scaleRow (-(6 : ℤ)) node6469 ++
      ([])) = [] := by
  decide +kernel

theorem node6469_mem : rowEval varIndex node6469 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6469Raw node6469 ([])
    (1) (6) (by decide) node6469_check
  · rw [node6469Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6436_mem
  · exact candidateIdeal.zero_mem

def node6470 : WordRow := [([10, 12, 16, 17], 2), ([10, 13, 16, 16], 1), ([11, 12, 16, 16], 1)]

def node6470Raw : WordRow := differentiateRow (images 32) node6436

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6470_check :
    collect (scaleRow 1 node6470Raw ++ scaleRow (-(3 : ℤ)) node6470 ++
      ([])) = [] := by
  decide +kernel

theorem node6470_mem : rowEval varIndex node6470 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6470Raw node6470 ([])
    (1) (3) (by decide) node6470_check
  · rw [node6470Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6436_mem
  · exact candidateIdeal.zero_mem

def node6471 : WordRow := [([10, 14, 16, 17], 2), ([10, 15, 16, 16], 1), ([11, 14, 16, 16], 1)]

def node6471Raw : WordRow := differentiateRow (images 34) node6436

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6471_check :
    collect (scaleRow 1 node6471Raw ++ scaleRow (-(3 : ℤ)) node6471 ++
      ([])) = [] := by
  decide +kernel

theorem node6471_mem : rowEval varIndex node6471 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6471Raw node6471 ([])
    (1) (3) (by decide) node6471_check
  · rw [node6471Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6436_mem
  · exact candidateIdeal.zero_mem

def node6472 : WordRow := [([12, 12, 16, 17], 1), ([12, 13, 16, 16], 1)]

def node6472Raw : WordRow := differentiateRow (images 32) node6437

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6472_check :
    collect (scaleRow 1 node6472Raw ++ scaleRow (-(6 : ℤ)) node6472 ++
      ([])) = [] := by
  decide +kernel

theorem node6472_mem : rowEval varIndex node6472 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6472Raw node6472 ([])
    (1) (6) (by decide) node6472_check
  · rw [node6472Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6437_mem
  · exact candidateIdeal.zero_mem

def node6473 : WordRow := [([12, 14, 16, 17], 2), ([12, 15, 16, 16], 1), ([13, 14, 16, 16], 1)]

def node6473Raw : WordRow := differentiateRow (images 34) node6437

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6473_check :
    collect (scaleRow 1 node6473Raw ++ scaleRow (-(3 : ℤ)) node6473 ++
      ([])) = [] := by
  decide +kernel

theorem node6473_mem : rowEval varIndex node6473 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6473Raw node6473 ([])
    (1) (3) (by decide) node6473_check
  · rw [node6473Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6437_mem
  · exact candidateIdeal.zero_mem

def node6474 : WordRow := [([14, 14, 16, 17], 1), ([14, 15, 16, 16], 1)]

def node6474Raw : WordRow := differentiateRow (images 34) node6438

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6474_check :
    collect (scaleRow 1 node6474Raw ++ scaleRow (-(6 : ℤ)) node6474 ++
      ([])) = [] := by
  decide +kernel

theorem node6474_mem : rowEval varIndex node6474 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6474Raw node6474 ([])
    (1) (6) (by decide) node6474_check
  · rw [node6474Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6438_mem
  · exact candidateIdeal.zero_mem

def node6475 : WordRow := [([0, 2, 4, 17], 2), ([0, 2, 5, 16], 1), ([0, 3, 4, 16], 1)]

def node6475Raw : WordRow := differentiateRow (images 28) node6439

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6475_check :
    collect (scaleRow 1 node6475Raw ++ scaleRow (-(1 : ℤ)) node6475 ++
      (scaleRow (-1) node5947 ++ scaleRow (-1) node2245 ++ scaleRow (-1) node0994)) = [] := by
  decide +kernel

theorem node6475_mem : rowEval varIndex node6475 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6475Raw node6475 (scaleRow (-1) node5947 ++ scaleRow (-1) node2245 ++ scaleRow (-1) node0994)
    (1) (1) (by decide) node6475_check
  · rw [node6475Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6439_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5947 node5947_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2245 node2245_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node0994 node0994_mem)))

def node6476 : WordRow := [([0, 2, 6, 17], 2), ([0, 2, 7, 16], 1), ([0, 3, 6, 16], 1)]

def node6476Raw : WordRow := differentiateRow (images 30) node6439

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6476_check :
    collect (scaleRow 1 node6476Raw ++ scaleRow (-(1 : ℤ)) node6476 ++
      (scaleRow (-1) node5955 ++ scaleRow (-1) node2496 ++ scaleRow (-1) node1011)) = [] := by
  decide +kernel

theorem node6476_mem : rowEval varIndex node6476 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6476Raw node6476 (scaleRow (-1) node5955 ++ scaleRow (-1) node2496 ++ scaleRow (-1) node1011)
    (1) (1) (by decide) node6476_check
  · rw [node6476Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6439_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5955 node5955_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2496 node2496_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1011 node1011_mem)))

def node6477 : WordRow := [([0, 4, 6, 17], 2), ([0, 4, 7, 16], 1), ([0, 5, 6, 16], 1)]

def node6477Raw : WordRow := differentiateRow (images 32) node6439

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6477_check :
    collect (scaleRow 1 node6477Raw ++ scaleRow (-(1 : ℤ)) node6477 ++
      (scaleRow (-1) node5972 ++ scaleRow (-1) node2949 ++ scaleRow (-1) node1024)) = [] := by
  decide +kernel

theorem node6477_mem : rowEval varIndex node6477 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6477Raw node6477 (scaleRow (-1) node5972 ++ scaleRow (-1) node2949 ++ scaleRow (-1) node1024)
    (1) (1) (by decide) node6477_check
  · rw [node6477Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6439_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5972 node5972_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2949 node2949_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1024 node1024_mem)))

def node6478 : WordRow := [([0, 2, 12, 17], 2), ([0, 2, 13, 16], 1), ([0, 3, 12, 16], 1), ([0, 4, 10, 17], 2), ([0, 4, 11, 16], 1), ([0, 5, 10, 16], 1), ([0, 6, 8, 17], 2), ([0, 6, 9, 16], 1), ([0, 7, 8, 16], 1), ([2, 4, 6, 17], -2)]

def node6478Raw : WordRow := differentiateRow (images 34) node6439

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6478_check :
    collect (scaleRow 1 node6478Raw ++ scaleRow (-(1 : ℤ)) node6478 ++
      (scaleRow (-1) node6120 ++ scaleRow (-1) node3951 ++ scaleRow (-1) node1033)) = [] := by
  decide +kernel

theorem node6478_mem : rowEval varIndex node6478 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6478Raw node6478 (scaleRow (-1) node6120 ++ scaleRow (-1) node3951 ++ scaleRow (-1) node1033)
    (1) (1) (by decide) node6478_check
  · rw [node6478Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6439_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6120 node6120_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3951 node3951_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1033 node1033_mem)))

def node6479 : WordRow := [([2, 2, 4, 17], 1), ([2, 2, 5, 16], 1), ([2, 3, 4, 16], 1)]

def node6479Raw : WordRow := differentiateRow (images 28) node6440

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6479_check :
    collect (scaleRow 1 node6479Raw ++ scaleRow (-(1 : ℤ)) node6479 ++
      (scaleRow (-1) node6095 ++ scaleRow (-2) node2260 ++ scaleRow (-2) node1300 ++ scaleRow (1) node3366)) = [] := by
  decide +kernel

theorem node6479_mem : rowEval varIndex node6479 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6479Raw node6479 (scaleRow (-1) node6095 ++ scaleRow (-2) node2260 ++ scaleRow (-2) node1300 ++ scaleRow (1) node3366)
    (1) (1) (by decide) node6479_check
  · rw [node6479Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6440_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6095 node6095_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2260 node2260_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1300 node1300_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3366 node3366_mem))))

def node6480 : WordRow := [([2, 2, 6, 17], 1), ([2, 2, 7, 16], 1), ([2, 3, 6, 16], 1)]

def node6480Raw : WordRow := differentiateRow (images 30) node6440

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6480_check :
    collect (scaleRow 1 node6480Raw ++ scaleRow (-(1 : ℤ)) node6480 ++
      (scaleRow (-1) node6103 ++ scaleRow (-2) node2510 ++ scaleRow (-2) node1317 ++ scaleRow (1) node3586)) = [] := by
  decide +kernel

theorem node6480_mem : rowEval varIndex node6480 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6480Raw node6480 (scaleRow (-1) node6103 ++ scaleRow (-2) node2510 ++ scaleRow (-2) node1317 ++ scaleRow (1) node3586)
    (1) (1) (by decide) node6480_check
  · rw [node6480Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6440_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6103 node6103_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2510 node2510_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1317 node1317_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3586 node3586_mem))))

def node6481 : WordRow := [([0, 4, 10, 17], 2), ([0, 4, 11, 16], 1), ([0, 5, 10, 16], 1), ([0, 6, 8, 17], 2), ([0, 6, 9, 16], 1), ([0, 7, 8, 16], 1), ([2, 4, 6, 17], -2), ([2, 4, 7, 16], -1), ([2, 5, 6, 16], -1)]

def node6481Raw : WordRow := differentiateRow (images 32) node6440

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6481_check :
    collect (scaleRow 1 node6481Raw ++ scaleRow (-(-1 : ℤ)) node6481 ++
      (scaleRow (-1) node6478 ++ scaleRow (-1) node2963 ++ scaleRow (-1) node1330)) = [] := by
  decide +kernel

theorem node6481_mem : rowEval varIndex node6481 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6481Raw node6481 (scaleRow (-1) node6478 ++ scaleRow (-1) node2963 ++ scaleRow (-1) node1330)
    (1) (-1) (by decide) node6481_check
  · rw [node6481Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6440_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6478 node6478_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2963 node2963_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1330 node1330_mem)))

def node6482 : WordRow := [([0, 8, 10, 17], 2), ([1, 2, 14, 16], 2), ([2, 2, 12, 17], -1), ([2, 2, 13, 16], -2), ([2, 3, 12, 16], -2), ([2, 4, 10, 17], -2), ([2, 4, 11, 16], -2), ([2, 5, 10, 16], -2), ([2, 6, 8, 17], -2), ([2, 6, 9, 16], -2), ([2, 7, 8, 16], -2)]

def node6482Raw : WordRow := differentiateRow (images 34) node6440

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6482_check :
    collect (scaleRow 1 node6482Raw ++ scaleRow (-(-1 : ℤ)) node6482 ++
      (scaleRow (-1) node6190 ++ scaleRow (-2) node3965 ++ scaleRow (-2) node1339)) = [] := by
  decide +kernel

theorem node6482_mem : rowEval varIndex node6482 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6482Raw node6482 (scaleRow (-1) node6190 ++ scaleRow (-2) node3965 ++ scaleRow (-2) node1339)
    (1) (-1) (by decide) node6482_check
  · rw [node6482Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6440_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6190 node6190_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3965 node3965_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1339 node1339_mem)))

def node6483 : WordRow := [([2, 4, 4, 17], 1), ([2, 4, 5, 16], 1), ([3, 4, 4, 16], 1)]

def node6483Raw : WordRow := differentiateRow (images 28) node6441

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6483_check :
    collect (scaleRow 1 node6483Raw ++ scaleRow (-(1 : ℤ)) node6483 ++
      (scaleRow (-1) node6112 ++ scaleRow (-2) node2286 ++ scaleRow (-2) node1587 ++ scaleRow (1) node3758)) = [] := by
  decide +kernel

theorem node6483_mem : rowEval varIndex node6483 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6483Raw node6483 (scaleRow (-1) node6112 ++ scaleRow (-2) node2286 ++ scaleRow (-2) node1587 ++ scaleRow (1) node3758)
    (1) (1) (by decide) node6483_check
  · rw [node6483Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6441_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6112 node6112_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2286 node2286_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1587 node1587_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3758 node3758_mem))))

def node6484 : WordRow := [([0, 6, 8, 17], 2), ([0, 6, 9, 16], 1), ([0, 7, 8, 16], 1), ([2, 4, 6, 17], -2), ([2, 4, 7, 16], -2), ([2, 5, 6, 16], -1), ([3, 4, 6, 16], -1)]

def node6484Raw : WordRow := differentiateRow (images 30) node6441

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6484_check :
    collect (scaleRow 1 node6484Raw ++ scaleRow (-(-1 : ℤ)) node6484 ++
      (scaleRow (-1) node6481 ++ scaleRow (-1) node2534 ++ scaleRow (-1) node1604)) = [] := by
  decide +kernel

theorem node6484_mem : rowEval varIndex node6484 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6484Raw node6484 (scaleRow (-1) node6481 ++ scaleRow (-1) node2534 ++ scaleRow (-1) node1604)
    (1) (-1) (by decide) node6484_check
  · rw [node6484Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6441_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6481 node6481_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2534 node2534_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1604 node1604_mem)))

def node6485 : WordRow := [([4, 4, 6, 17], 1), ([4, 4, 7, 16], 1), ([4, 5, 6, 16], 1)]

def node6485Raw : WordRow := differentiateRow (images 32) node6441

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6485_check :
    collect (scaleRow 1 node6485Raw ++ scaleRow (-(1 : ℤ)) node6485 ++
      (scaleRow (-1) node6144 ++ scaleRow (-2) node2986 ++ scaleRow (-2) node1617 ++ scaleRow (1) node4316)) = [] := by
  decide +kernel

theorem node6485_mem : rowEval varIndex node6485 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6485Raw node6485 (scaleRow (-1) node6144 ++ scaleRow (-2) node2986 ++ scaleRow (-2) node1617 ++ scaleRow (1) node4316)
    (1) (1) (by decide) node6485_check
  · rw [node6485Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6441_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6144 node6144_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2986 node2986_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1617 node1617_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4316 node4316_mem))))

def node6486 : WordRow := [([0, 8, 12, 17], 2), ([1, 4, 14, 16], 2), ([2, 4, 12, 17], -2), ([2, 4, 13, 16], -2), ([3, 4, 12, 16], -2), ([4, 4, 10, 17], -1), ([4, 4, 11, 16], -2), ([4, 5, 10, 16], -2), ([4, 6, 8, 17], -2), ([4, 6, 9, 16], -2), ([4, 7, 8, 16], -2)]

def node6486Raw : WordRow := differentiateRow (images 34) node6441

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6486_check :
    collect (scaleRow 1 node6486Raw ++ scaleRow (-(-1 : ℤ)) node6486 ++
      (scaleRow (-1) node6213 ++ scaleRow (-2) node3984 ++ scaleRow (-2) node1626)) = [] := by
  decide +kernel

theorem node6486_mem : rowEval varIndex node6486 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6486Raw node6486 (scaleRow (-1) node6213 ++ scaleRow (-2) node3984 ++ scaleRow (-2) node1626)
    (1) (-1) (by decide) node6486_check
  · rw [node6486Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6441_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6213 node6213_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3984 node3984_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1626 node1626_mem)))

def node6487 : WordRow := [([2, 4, 6, 17], 1), ([2, 4, 7, 16], 1), ([2, 5, 6, 16], 1), ([3, 4, 6, 16], 1)]

def node6487Raw : WordRow := differentiateRow (images 28) node6442

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6487_check :
    collect (scaleRow 1 node6487Raw ++ scaleRow (-(2 : ℤ)) node6487 ++
      (scaleRow (-1) node6484 ++ scaleRow (-1) node2311 ++ scaleRow (-1) node1839)) = [] := by
  decide +kernel

theorem node6487_mem : rowEval varIndex node6487 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6487Raw node6487 (scaleRow (-1) node6484 ++ scaleRow (-1) node2311 ++ scaleRow (-1) node1839)
    (1) (2) (by decide) node6487_check
  · rw [node6487Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6442_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6484 node6484_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2311 node2311_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1839 node1839_mem)))

def node6488 : WordRow := [([2, 6, 6, 17], 1), ([2, 6, 7, 16], 1), ([3, 6, 6, 16], 1)]

def node6488Raw : WordRow := differentiateRow (images 30) node6442

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6488_check :
    collect (scaleRow 1 node6488Raw ++ scaleRow (-(1 : ℤ)) node6488 ++
      (scaleRow (-1) node6128 ++ scaleRow (-2) node2558 ++ scaleRow (-2) node1856 ++ scaleRow (1) node4149)) = [] := by
  decide +kernel

theorem node6488_mem : rowEval varIndex node6488 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6488Raw node6488 (scaleRow (-1) node6128 ++ scaleRow (-2) node2558 ++ scaleRow (-2) node1856 ++ scaleRow (1) node4149)
    (1) (1) (by decide) node6488_check
  · rw [node6488Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6442_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6128 node6128_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2558 node2558_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1856 node1856_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4149 node4149_mem))))

def node6489 : WordRow := [([4, 6, 6, 17], 1), ([4, 6, 7, 16], 1), ([5, 6, 6, 16], 1)]

def node6489Raw : WordRow := differentiateRow (images 32) node6442

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6489_check :
    collect (scaleRow 1 node6489Raw ++ scaleRow (-(1 : ℤ)) node6489 ++
      (scaleRow (-1) node6152 ++ scaleRow (-2) node3008 ++ scaleRow (-2) node1869 ++ scaleRow (1) node4476)) = [] := by
  decide +kernel

theorem node6489_mem : rowEval varIndex node6489 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6489Raw node6489 (scaleRow (-1) node6152 ++ scaleRow (-2) node3008 ++ scaleRow (-2) node1869 ++ scaleRow (1) node4476)
    (1) (1) (by decide) node6489_check
  · rw [node6489Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6442_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6152 node6152_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3008 node3008_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node1869 node1869_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4476 node4476_mem))))

def node6490 : WordRow := [([0, 10, 12, 17], 2), ([1, 6, 14, 16], 2), ([2, 6, 12, 17], -2), ([2, 6, 13, 16], -2), ([3, 6, 12, 16], -2), ([4, 6, 10, 17], -2), ([4, 6, 11, 16], -2), ([5, 6, 10, 16], -2), ([6, 6, 8, 17], -1), ([6, 6, 9, 16], -2), ([6, 7, 8, 16], -2)]

def node6490Raw : WordRow := differentiateRow (images 34) node6442

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6490_check :
    collect (scaleRow 1 node6490Raw ++ scaleRow (-(-1 : ℤ)) node6490 ++
      (scaleRow (-1) node6221 ++ scaleRow (-2) node4003 ++ scaleRow (-2) node1878)) = [] := by
  decide +kernel

theorem node6490_mem : rowEval varIndex node6490 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6490Raw node6490 (scaleRow (-1) node6221 ++ scaleRow (-2) node4003 ++ scaleRow (-2) node1878)
    (1) (-1) (by decide) node6490_check
  · rw [node6490Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6442_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6221 node6221_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4003 node4003_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node1878 node1878_mem)))

def node6491 : WordRow := [([2, 4, 8, 17], 2), ([2, 5, 8, 16], 1), ([3, 4, 8, 16], 1)]

def node6491Raw : WordRow := differentiateRow (images 28) node6443

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6491_check :
    collect (scaleRow 1 node6491Raw ++ scaleRow (-(2 : ℤ)) node6491 ++
      (scaleRow (-2) node6182 ++ scaleRow (-4) node2332 ++ scaleRow (2) node4616)) = [] := by
  decide +kernel

theorem node6491_mem : rowEval varIndex node6491 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6491Raw node6491 (scaleRow (-2) node6182 ++ scaleRow (-4) node2332 ++ scaleRow (2) node4616)
    (1) (2) (by decide) node6491_check
  · rw [node6491Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6443_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node6182 node6182_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-4) node2332 node2332_mem) (rowEval_scale_mem varIndex candidateIdeal (2) node4616 node4616_mem)))

def node6492 : WordRow := [([2, 2, 12, 17], 1), ([2, 2, 13, 16], 1), ([2, 3, 12, 16], 1), ([2, 4, 10, 17], 2), ([2, 4, 11, 16], 1), ([2, 5, 10, 16], 2), ([2, 6, 8, 17], 2), ([2, 6, 9, 16], 1), ([2, 7, 8, 16], 2), ([3, 4, 10, 16], 1), ([3, 6, 8, 16], 1)]

def node6492Raw : WordRow := differentiateRow (images 30) node6443

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6492_check :
    collect (scaleRow 1 node6492Raw ++ scaleRow (-(1 : ℤ)) node6492 ++
      (scaleRow (-1) node6482 ++ scaleRow (-2) node2579 ++ scaleRow (-2) node2349 ++ scaleRow (1) node4775)) = [] := by
  decide +kernel

theorem node6492_mem : rowEval varIndex node6492 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6492Raw node6492 (scaleRow (-1) node6482 ++ scaleRow (-2) node2579 ++ scaleRow (-2) node2349 ++ scaleRow (1) node4775)
    (1) (1) (by decide) node6492_check
  · rw [node6492Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6443_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6482 node6482_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2579 node2579_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2349 node2349_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4775 node4775_mem))))

def node6493 : WordRow := [([2, 4, 12, 17], 2), ([2, 4, 13, 16], 1), ([2, 5, 12, 16], 1), ([3, 4, 12, 16], 2), ([4, 4, 10, 17], 1), ([4, 4, 11, 16], 1), ([4, 5, 10, 16], 1), ([4, 6, 8, 17], 2), ([4, 6, 9, 16], 1), ([4, 7, 8, 16], 2), ([5, 6, 8, 16], 1)]

def node6493Raw : WordRow := differentiateRow (images 32) node6443

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6493_check :
    collect (scaleRow 1 node6493Raw ++ scaleRow (-(1 : ℤ)) node6493 ++
      (scaleRow (-1) node6486 ++ scaleRow (-2) node3029 ++ scaleRow (-2) node2362 ++ scaleRow (1) node5047)) = [] := by
  decide +kernel

theorem node6493_mem : rowEval varIndex node6493 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6493Raw node6493 (scaleRow (-1) node6486 ++ scaleRow (-2) node3029 ++ scaleRow (-2) node2362 ++ scaleRow (1) node5047)
    (1) (1) (by decide) node6493_check
  · rw [node6493Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6443_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6486 node6486_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node3029 node3029_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2362 node2362_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5047 node5047_mem))))

def node6494 : WordRow := [([2, 4, 14, 17], 2), ([2, 5, 14, 16], 1), ([2, 8, 12, 17], 2), ([2, 8, 13, 16], 1), ([3, 4, 14, 16], 1), ([3, 8, 12, 16], 1), ([4, 8, 10, 17], 2), ([4, 8, 11, 16], 1), ([5, 8, 10, 16], 1), ([6, 8, 8, 17], 1), ([6, 8, 9, 16], 1), ([7, 8, 8, 16], 1)]

def node6494Raw : WordRow := differentiateRow (images 34) node6443

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6494_check :
    collect (scaleRow 1 node6494Raw ++ scaleRow (-(1 : ℤ)) node6494 ++
      (scaleRow (-1) node6281 ++ scaleRow (-2) node4022 ++ scaleRow (-2) node2371 ++ scaleRow (1) node5414)) = [] := by
  decide +kernel

theorem node6494_mem : rowEval varIndex node6494 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6494Raw node6494 (scaleRow (-1) node6281 ++ scaleRow (-2) node4022 ++ scaleRow (-2) node2371 ++ scaleRow (1) node5414)
    (1) (1) (by decide) node6494_check
  · rw [node6494Raw,rowEval_images]
    exact candidateIdeal_deriv _ node6443_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6281 node6281_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node4022 node4022_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-2) node2371 node2371_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5414 node5414_mem))))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node6494_mem
