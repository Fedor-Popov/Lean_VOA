import VOA.DeligneAudit.D4FusionContactM2Dag09

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node2733 : WordRow := [([3, 4, 5, 10], 1)]

def node2733Raw : WordRow := multiplyRow 10 node0276

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2733_check :
    collect (scaleRow 1 node2733Raw ++ scaleRow (-(1 : ℤ)) node2733 ++
      ([])) = [] := by
  decide +kernel

theorem node2733_mem : rowEval varIndex node2733 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2733Raw node2733 ([])
    (1) (1) (by decide) node2733_check
  · rw [node2733Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0276_mem
  · exact candidateIdeal.zero_mem

def node2814 : WordRow := [([4, 5, 10, 14], 1)]

def node2814Raw : WordRow := multiplyRow 14 node0283

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2814_check :
    collect (scaleRow 1 node2814Raw ++ scaleRow (-(1 : ℤ)) node2814 ++
      ([])) = [] := by
  decide +kernel

theorem node2814_mem : rowEval varIndex node2814 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2814Raw node2814 ([])
    (1) (1) (by decide) node2814_check
  · rw [node2814Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0283_mem
  · exact candidateIdeal.zero_mem

def node2815 : WordRow := [([4, 5, 10, 15], 1)]

def node2815Raw : WordRow := multiplyRow 15 node0283

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2815_check :
    collect (scaleRow 1 node2815Raw ++ scaleRow (-(1 : ℤ)) node2815 ++
      ([])) = [] := by
  decide +kernel

theorem node2815_mem : rowEval varIndex node2815 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2815Raw node2815 ([])
    (1) (1) (by decide) node2815_check
  · rw [node2815Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0283_mem
  · exact candidateIdeal.zero_mem

def node2816 : WordRow := [([4, 5, 10, 16], 1)]

def node2816Raw : WordRow := multiplyRow 16 node0283

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2816_check :
    collect (scaleRow 1 node2816Raw ++ scaleRow (-(1 : ℤ)) node2816 ++
      ([])) = [] := by
  decide +kernel

theorem node2816_mem : rowEval varIndex node2816 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2816Raw node2816 ([])
    (1) (1) (by decide) node2816_check
  · rw [node2816Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0283_mem
  · exact candidateIdeal.zero_mem

def node2821 : WordRow := [([4, 5, 11, 14], 1)]

def node2821Raw : WordRow := multiplyRow 14 node0284

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2821_check :
    collect (scaleRow 1 node2821Raw ++ scaleRow (-(1 : ℤ)) node2821 ++
      ([])) = [] := by
  decide +kernel

theorem node2821_mem : rowEval varIndex node2821 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2821Raw node2821 ([])
    (1) (1) (by decide) node2821_check
  · rw [node2821Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0284_mem
  · exact candidateIdeal.zero_mem

def node2838 : WordRow := [([4, 5, 14, 16], 1)]

def node2838Raw : WordRow := multiplyRow 16 node0287

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2838_check :
    collect (scaleRow 1 node2838Raw ++ scaleRow (-(1 : ℤ)) node2838 ++
      ([])) = [] := by
  decide +kernel

theorem node2838_mem : rowEval varIndex node2838 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2838Raw node2838 ([])
    (1) (1) (by decide) node2838_check
  · rw [node2838Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0287_mem
  · exact candidateIdeal.zero_mem

def node2905 : WordRow := [([5, 5, 10, 14], 1)]

def node2905Raw : WordRow := multiplyRow 14 node0296

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2905_check :
    collect (scaleRow 1 node2905Raw ++ scaleRow (-(1 : ℤ)) node2905 ++
      ([])) = [] := by
  decide +kernel

theorem node2905_mem : rowEval varIndex node2905 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2905Raw node2905 ([])
    (1) (1) (by decide) node2905_check
  · rw [node2905Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0296_mem
  · exact candidateIdeal.zero_mem

def node2938 : WordRow := [([0, 0, 2, 13], 1), ([0, 1, 2, 12], 1), ([0, 2, 4, 7], -1), ([0, 2, 5, 6], -1)]

def node2938Raw : WordRow := multiplyRow 2 node0304

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2938_check :
    collect (scaleRow 1 node2938Raw ++ scaleRow (-(1 : ℤ)) node2938 ++
      ([])) = [] := by
  decide +kernel

theorem node2938_mem : rowEval varIndex node2938 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2938Raw node2938 ([])
    (1) (1) (by decide) node2938_check
  · rw [node2938Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0304_mem
  · exact candidateIdeal.zero_mem

def node2949 : WordRow := [([0, 0, 13, 16], 1), ([0, 1, 12, 16], 1), ([0, 4, 7, 16], -1), ([0, 5, 6, 16], -1)]

def node2949Raw : WordRow := multiplyRow 16 node0304

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2949_check :
    collect (scaleRow 1 node2949Raw ++ scaleRow (-(1 : ℤ)) node2949 ++
      ([])) = [] := by
  decide +kernel

theorem node2949_mem : rowEval varIndex node2949 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2949Raw node2949 ([])
    (1) (1) (by decide) node2949_check
  · rw [node2949Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0304_mem
  · exact candidateIdeal.zero_mem

def node2951 : WordRow := [([0, 2, 2, 13], 1), ([1, 2, 2, 12], 1), ([2, 2, 4, 7], -1), ([2, 2, 5, 6], -1)]

def node2951Raw : WordRow := multiplyRow 2 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2951_check :
    collect (scaleRow 1 node2951Raw ++ scaleRow (-(1 : ℤ)) node2951 ++
      ([])) = [] := by
  decide +kernel

theorem node2951_mem : rowEval varIndex node2951 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2951Raw node2951 ([])
    (1) (1) (by decide) node2951_check
  · rw [node2951Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2952 : WordRow := [([0, 2, 4, 13], 1), ([1, 2, 4, 12], 1), ([2, 4, 4, 7], -1), ([2, 4, 5, 6], -1)]

def node2952Raw : WordRow := multiplyRow 4 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2952_check :
    collect (scaleRow 1 node2952Raw ++ scaleRow (-(1 : ℤ)) node2952 ++
      ([])) = [] := by
  decide +kernel

theorem node2952_mem : rowEval varIndex node2952 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2952Raw node2952 ([])
    (1) (1) (by decide) node2952_check
  · rw [node2952Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2953 : WordRow := [([0, 2, 6, 13], 1), ([1, 2, 6, 12], 1), ([2, 4, 6, 7], -1), ([2, 5, 6, 6], -1)]

def node2953Raw : WordRow := multiplyRow 6 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2953_check :
    collect (scaleRow 1 node2953Raw ++ scaleRow (-(1 : ℤ)) node2953 ++
      ([])) = [] := by
  decide +kernel

theorem node2953_mem : rowEval varIndex node2953 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2953Raw node2953 ([])
    (1) (1) (by decide) node2953_check
  · rw [node2953Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2955 : WordRow := [([0, 2, 8, 13], 1), ([1, 2, 8, 12], 1), ([2, 4, 7, 8], -1), ([2, 5, 6, 8], -1)]

def node2955Raw : WordRow := multiplyRow 8 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2955_check :
    collect (scaleRow 1 node2955Raw ++ scaleRow (-(1 : ℤ)) node2955 ++
      ([])) = [] := by
  decide +kernel

theorem node2955_mem : rowEval varIndex node2955 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2955Raw node2955 ([])
    (1) (1) (by decide) node2955_check
  · rw [node2955Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2957 : WordRow := [([0, 2, 10, 13], 1), ([1, 2, 10, 12], 1), ([2, 4, 7, 10], -1), ([2, 5, 6, 10], -1)]

def node2957Raw : WordRow := multiplyRow 10 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2957_check :
    collect (scaleRow 1 node2957Raw ++ scaleRow (-(1 : ℤ)) node2957 ++
      ([])) = [] := by
  decide +kernel

theorem node2957_mem : rowEval varIndex node2957 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2957Raw node2957 ([])
    (1) (1) (by decide) node2957_check
  · rw [node2957Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2959 : WordRow := [([0, 2, 12, 13], 1), ([1, 2, 12, 12], 1), ([2, 4, 7, 12], -1), ([2, 5, 6, 12], -1)]

def node2959Raw : WordRow := multiplyRow 12 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2959_check :
    collect (scaleRow 1 node2959Raw ++ scaleRow (-(1 : ℤ)) node2959 ++
      ([])) = [] := by
  decide +kernel

theorem node2959_mem : rowEval varIndex node2959 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2959Raw node2959 ([])
    (1) (1) (by decide) node2959_check
  · rw [node2959Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2961 : WordRow := [([0, 2, 13, 14], 1), ([1, 2, 12, 14], 1), ([2, 4, 7, 14], -1), ([2, 5, 6, 14], -1)]

def node2961Raw : WordRow := multiplyRow 14 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2961_check :
    collect (scaleRow 1 node2961Raw ++ scaleRow (-(1 : ℤ)) node2961 ++
      ([])) = [] := by
  decide +kernel

theorem node2961_mem : rowEval varIndex node2961 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2961Raw node2961 ([])
    (1) (1) (by decide) node2961_check
  · rw [node2961Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2963 : WordRow := [([0, 2, 13, 16], 1), ([1, 2, 12, 16], 1), ([2, 4, 7, 16], -1), ([2, 5, 6, 16], -1)]

def node2963Raw : WordRow := multiplyRow 16 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2963_check :
    collect (scaleRow 1 node2963Raw ++ scaleRow (-(1 : ℤ)) node2963 ++
      ([])) = [] := by
  decide +kernel

theorem node2963_mem : rowEval varIndex node2963 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2963Raw node2963 ([])
    (1) (1) (by decide) node2963_check
  · rw [node2963Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2964 : WordRow := [([0, 2, 13, 17], 1), ([1, 2, 12, 17], 1), ([2, 4, 7, 17], -1), ([2, 5, 6, 17], -1)]

def node2964Raw : WordRow := multiplyRow 17 node0305

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2964_check :
    collect (scaleRow 1 node2964Raw ++ scaleRow (-(1 : ℤ)) node2964 ++
      ([])) = [] := by
  decide +kernel

theorem node2964_mem : rowEval varIndex node2964 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2964Raw node2964 ([])
    (1) (1) (by decide) node2964_check
  · rw [node2964Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0305_mem
  · exact candidateIdeal.zero_mem

def node2986 : WordRow := [([0, 4, 13, 16], 1), ([1, 4, 12, 16], 1), ([4, 4, 7, 16], -1), ([4, 5, 6, 16], -1)]

def node2986Raw : WordRow := multiplyRow 16 node0307

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2986_check :
    collect (scaleRow 1 node2986Raw ++ scaleRow (-(1 : ℤ)) node2986 ++
      ([])) = [] := by
  decide +kernel

theorem node2986_mem : rowEval varIndex node2986 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2986Raw node2986 ([])
    (1) (1) (by decide) node2986_check
  · rw [node2986Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0307_mem
  · exact candidateIdeal.zero_mem

def node3008 : WordRow := [([0, 6, 13, 16], 1), ([1, 6, 12, 16], 1), ([4, 6, 7, 16], -1), ([5, 6, 6, 16], -1)]

def node3008Raw : WordRow := multiplyRow 16 node0309

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3008_check :
    collect (scaleRow 1 node3008Raw ++ scaleRow (-(1 : ℤ)) node3008 ++
      ([])) = [] := by
  decide +kernel

theorem node3008_mem : rowEval varIndex node3008 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3008Raw node3008 ([])
    (1) (1) (by decide) node3008_check
  · rw [node3008Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0309_mem
  · exact candidateIdeal.zero_mem

def node3024 : WordRow := [([1, 8, 10, 13], 1), ([1, 8, 11, 12], -1), ([2, 7, 8, 13], -1), ([3, 6, 8, 13], -1), ([4, 7, 8, 11], 1), ([5, 6, 8, 11], 1)]

def node3024Raw : WordRow := multiplyRow 11 node0311

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3024_check :
    collect (scaleRow 1 node3024Raw ++ scaleRow (-(-1 : ℤ)) node3024 ++
      (scaleRow (-1) node2576)) = [] := by
  decide +kernel

theorem node3024_mem : rowEval varIndex node3024 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3024Raw node3024 (scaleRow (-1) node2576)
    (1) (-1) (by decide) node3024_check
  · rw [node3024Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0311_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node2576 node2576_mem)

def node3028 : WordRow := [([0, 8, 13, 15], 1), ([1, 8, 12, 15], 1), ([4, 7, 8, 15], -1), ([5, 6, 8, 15], -1)]

def node3028Raw : WordRow := multiplyRow 15 node0311

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3028_check :
    collect (scaleRow 1 node3028Raw ++ scaleRow (-(1 : ℤ)) node3028 ++
      ([])) = [] := by
  decide +kernel

theorem node3028_mem : rowEval varIndex node3028 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3028Raw node3028 ([])
    (1) (1) (by decide) node3028_check
  · rw [node3028Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0311_mem
  · exact candidateIdeal.zero_mem

def node3029 : WordRow := [([0, 8, 13, 16], 1), ([1, 8, 12, 16], 1), ([4, 7, 8, 16], -1), ([5, 6, 8, 16], -1)]

def node3029Raw : WordRow := multiplyRow 16 node0311

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3029_check :
    collect (scaleRow 1 node3029Raw ++ scaleRow (-(1 : ℤ)) node3029 ++
      ([])) = [] := by
  decide +kernel

theorem node3029_mem : rowEval varIndex node3029 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3029Raw node3029 ([])
    (1) (1) (by decide) node3029_check
  · rw [node3029Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0311_mem
  · exact candidateIdeal.zero_mem

def node3030 : WordRow := [([0, 8, 13, 17], 1), ([1, 8, 12, 17], 1), ([4, 7, 8, 17], -1), ([5, 6, 8, 17], -1)]

def node3030Raw : WordRow := multiplyRow 17 node0311

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3030_check :
    collect (scaleRow 1 node3030Raw ++ scaleRow (-(1 : ℤ)) node3030 ++
      ([])) = [] := by
  decide +kernel

theorem node3030_mem : rowEval varIndex node3030 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3030Raw node3030 ([])
    (1) (1) (by decide) node3030_check
  · rw [node3030Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0311_mem
  · exact candidateIdeal.zero_mem

def node3032 : WordRow := [([2, 5, 10, 13], 1), ([2, 5, 11, 12], -1), ([2, 7, 8, 13], -1), ([2, 7, 9, 12], 1), ([3, 4, 10, 13], 1), ([3, 4, 11, 12], -1), ([3, 6, 8, 13], -1), ([3, 6, 9, 12], 1), ([4, 7, 8, 11], 1), ([4, 7, 9, 10], -1), ([5, 6, 8, 11], 1), ([5, 6, 9, 10], -1)]

def node3032Raw : WordRow := multiplyRow 10 node0312

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3032_check :
    collect (scaleRow 1 node3032Raw ++ scaleRow (-(-1 : ℤ)) node3032 ++
      (scaleRow (-1) node3024 ++ scaleRow (-1) node2584)) = [] := by
  decide +kernel

theorem node3032_mem : rowEval varIndex node3032 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3032Raw node3032 (scaleRow (-1) node3024 ++ scaleRow (-1) node2584)
    (1) (-1) (by decide) node3032_check
  · rw [node3032Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0312_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3024 node3024_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2584 node2584_mem))

def node3036 : WordRow := [([1, 8, 13, 14], 1), ([1, 9, 12, 14], -1), ([2, 5, 13, 14], -1), ([3, 4, 13, 14], -1), ([4, 7, 9, 14], 1), ([5, 6, 9, 14], 1)]

def node3036Raw : WordRow := multiplyRow 14 node0312

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3036_check :
    collect (scaleRow 1 node3036Raw ++ scaleRow (-(1 : ℤ)) node3036 ++
      ([])) = [] := by
  decide +kernel

theorem node3036_mem : rowEval varIndex node3036 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3036Raw node3036 ([])
    (1) (1) (by decide) node3036_check
  · rw [node3036Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0312_mem
  · exact candidateIdeal.zero_mem

def node3046 : WordRow := [([0, 10, 13, 16], 1), ([1, 10, 12, 16], 1), ([4, 7, 10, 16], -1), ([5, 6, 10, 16], -1)]

def node3046Raw : WordRow := multiplyRow 16 node0313

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3046_check :
    collect (scaleRow 1 node3046Raw ++ scaleRow (-(1 : ℤ)) node3046 ++
      ([])) = [] := by
  decide +kernel

theorem node3046_mem : rowEval varIndex node3046 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3046Raw node3046 ([])
    (1) (1) (by decide) node3046_check
  · rw [node3046Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0313_mem
  · exact candidateIdeal.zero_mem

def node3047 : WordRow := [([0, 10, 13, 17], 1), ([1, 10, 12, 17], 1), ([4, 7, 10, 17], -1), ([5, 6, 10, 17], -1)]

def node3047Raw : WordRow := multiplyRow 17 node0313

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3047_check :
    collect (scaleRow 1 node3047Raw ++ scaleRow (-(1 : ℤ)) node3047 ++
      ([])) = [] := by
  decide +kernel

theorem node3047_mem : rowEval varIndex node3047 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3047Raw node3047 ([])
    (1) (1) (by decide) node3047_check
  · rw [node3047Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0313_mem
  · exact candidateIdeal.zero_mem

def node3059 : WordRow := [([0, 12, 13, 16], 1), ([1, 12, 12, 16], 1), ([4, 7, 12, 16], -1), ([5, 6, 12, 16], -1)]

def node3059Raw : WordRow := multiplyRow 16 node0315

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3059_check :
    collect (scaleRow 1 node3059Raw ++ scaleRow (-(1 : ℤ)) node3059 ++
      ([])) = [] := by
  decide +kernel

theorem node3059_mem : rowEval varIndex node3059 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3059Raw node3059 ([])
    (1) (1) (by decide) node3059_check
  · rw [node3059Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0315_mem
  · exact candidateIdeal.zero_mem

def node3068 : WordRow := [([0, 13, 14, 16], 1), ([1, 12, 14, 16], 1), ([4, 7, 14, 16], -1), ([5, 6, 14, 16], -1)]

def node3068Raw : WordRow := multiplyRow 16 node0317

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3068_check :
    collect (scaleRow 1 node3068Raw ++ scaleRow (-(1 : ℤ)) node3068 ++
      ([])) = [] := by
  decide +kernel

theorem node3068_mem : rowEval varIndex node3068 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3068Raw node3068 ([])
    (1) (1) (by decide) node3068_check
  · rw [node3068Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0317_mem
  · exact candidateIdeal.zero_mem

def node3074 : WordRow := [([0, 13, 16, 17], 1), ([1, 12, 16, 17], 1), ([4, 7, 16, 17], -1), ([5, 6, 16, 17], -1)]

def node3074Raw : WordRow := multiplyRow 17 node0319

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3074_check :
    collect (scaleRow 1 node3074Raw ++ scaleRow (-(1 : ℤ)) node3074 ++
      ([])) = [] := by
  decide +kernel

theorem node3074_mem : rowEval varIndex node3074 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3074Raw node3074 ([])
    (1) (1) (by decide) node3074_check
  · rw [node3074Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0319_mem
  · exact candidateIdeal.zero_mem

def node3101 : WordRow := [([2, 7, 8, 13], 1), ([3, 6, 8, 13], 1), ([3, 7, 8, 12], 1), ([4, 7, 8, 11], -1), ([5, 6, 8, 11], -1), ([5, 7, 8, 10], -1)]

def node3101Raw : WordRow := multiplyRow 10 node0323

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3101_check :
    collect (scaleRow 1 node3101Raw ++ scaleRow (-(1 : ℤ)) node3101 ++
      (scaleRow (-1) node3032 ++ scaleRow (-1) node2653)) = [] := by
  decide +kernel

theorem node3101_mem : rowEval varIndex node3101 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3101Raw node3101 (scaleRow (-1) node3032 ++ scaleRow (-1) node2653)
    (1) (1) (by decide) node3101_check
  · rw [node3101Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0323_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3032 node3032_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2653 node2653_mem))

def node3105 : WordRow := [([2, 5, 13, 14], 1), ([3, 4, 13, 14], 1), ([3, 5, 12, 14], 1), ([4, 7, 9, 14], -1), ([5, 6, 9, 14], -1), ([5, 7, 8, 14], -1)]

def node3105Raw : WordRow := multiplyRow 14 node0323

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3105_check :
    collect (scaleRow 1 node3105Raw ++ scaleRow (-(1 : ℤ)) node3105 ++
      ([])) = [] := by
  decide +kernel

theorem node3105_mem : rowEval varIndex node3105 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3105Raw node3105 ([])
    (1) (1) (by decide) node3105_check
  · rw [node3105Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0323_mem
  · exact candidateIdeal.zero_mem

def node3157 : WordRow := [([1, 6, 6, 8], 1)]

def node3157Raw : WordRow := multiplyRow 8 node0333

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3157_check :
    collect (scaleRow 1 node3157Raw ++ scaleRow (-(1 : ℤ)) node3157 ++
      ([])) = [] := by
  decide +kernel

theorem node3157_mem : rowEval varIndex node3157 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3157Raw node3157 ([])
    (1) (1) (by decide) node3157_check
  · rw [node3157Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0333_mem
  · exact candidateIdeal.zero_mem

def node3158 : WordRow := [([3, 5, 6, 6], 1)]

def node3158Raw : WordRow := multiplyRow 9 node0333

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3158_check :
    collect (scaleRow 1 node3158Raw ++ scaleRow (-(1 : ℤ)) node3158 ++
      (scaleRow (-1) node2302 ++ scaleRow (-1) node1888 ++ scaleRow (1) node2406)) = [] := by
  decide +kernel

theorem node3158_mem : rowEval varIndex node3158 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3158Raw node3158 (scaleRow (-1) node2302 ++ scaleRow (-1) node1888 ++ scaleRow (1) node2406)
    (1) (1) (by decide) node3158_check
  · rw [node3158Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0333_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2302 node2302_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1888 node1888_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node2406 node2406_mem)))

def node3171 : WordRow := [([2, 6, 7, 9], 1)]

def node3171Raw : WordRow := multiplyRow 9 node0334

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3171_check :
    collect (scaleRow 1 node3171Raw ++ scaleRow (-(1 : ℤ)) node3171 ++
      ([])) = [] := by
  decide +kernel

theorem node3171_mem : rowEval varIndex node3171 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3171Raw node3171 ([])
    (1) (1) (by decide) node3171_check
  · rw [node3171Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0334_mem
  · exact candidateIdeal.zero_mem

def node3179 : WordRow := [([2, 6, 7, 17], 1)]

def node3179Raw : WordRow := multiplyRow 17 node0334

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3179_check :
    collect (scaleRow 1 node3179Raw ++ scaleRow (-(1 : ℤ)) node3179 ++
      ([])) = [] := by
  decide +kernel

theorem node3179_mem : rowEval varIndex node3179 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3179Raw node3179 ([])
    (1) (1) (by decide) node3179_check
  · rw [node3179Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0334_mem
  · exact candidateIdeal.zero_mem

def node3201 : WordRow := [([4, 6, 7, 17], 1)]

def node3201Raw : WordRow := multiplyRow 17 node0336

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3201_check :
    collect (scaleRow 1 node3201Raw ++ scaleRow (-(1 : ℤ)) node3201 ++
      ([])) = [] := by
  decide +kernel

theorem node3201_mem : rowEval varIndex node3201 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3201Raw node3201 ([])
    (1) (1) (by decide) node3201_check
  · rw [node3201Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0336_mem
  · exact candidateIdeal.zero_mem

def node3240 : WordRow := [([6, 7, 8, 14], 1)]

def node3240Raw : WordRow := multiplyRow 14 node0340

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3240_check :
    collect (scaleRow 1 node3240Raw ++ scaleRow (-(1 : ℤ)) node3240 ++
      ([])) = [] := by
  decide +kernel

theorem node3240_mem : rowEval varIndex node3240 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3240Raw node3240 ([])
    (1) (1) (by decide) node3240_check
  · rw [node3240Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0340_mem
  · exact candidateIdeal.zero_mem

def node3281 : WordRow := [([6, 7, 14, 16], 1)]

def node3281Raw : WordRow := multiplyRow 16 node0346

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3281_check :
    collect (scaleRow 1 node3281Raw ++ scaleRow (-(1 : ℤ)) node3281 ++
      ([])) = [] := by
  decide +kernel

theorem node3281_mem : rowEval varIndex node3281 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3281Raw node3281 ([])
    (1) (1) (by decide) node3281_check
  · rw [node3281Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0346_mem
  · exact candidateIdeal.zero_mem

def node3357 : WordRow := [([1, 2, 6, 8], 2), ([2, 2, 5, 6], -1), ([2, 3, 4, 6], -1)]

def node3357Raw : WordRow := multiplyRow 6 node0361

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3357_check :
    collect (scaleRow 1 node3357Raw ++ scaleRow (-(1 : ℤ)) node3357 ++
      ([])) = [] := by
  decide +kernel

theorem node3357_mem : rowEval varIndex node3357 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3357Raw node3357 ([])
    (1) (1) (by decide) node3357_check
  · rw [node3357Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0361_mem
  · exact candidateIdeal.zero_mem

def node3362 : WordRow := [([1, 2, 8, 12], 2), ([2, 2, 5, 12], -1), ([2, 3, 4, 12], -1)]

def node3362Raw : WordRow := multiplyRow 12 node0361

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3362_check :
    collect (scaleRow 1 node3362Raw ++ scaleRow (-(1 : ℤ)) node3362 ++
      ([])) = [] := by
  decide +kernel

theorem node3362_mem : rowEval varIndex node3362 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3362Raw node3362 ([])
    (1) (1) (by decide) node3362_check
  · rw [node3362Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0361_mem
  · exact candidateIdeal.zero_mem

def node3366 : WordRow := [([1, 2, 8, 16], 2), ([2, 2, 5, 16], -1), ([2, 3, 4, 16], -1)]

def node3366Raw : WordRow := multiplyRow 16 node0361

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3366_check :
    collect (scaleRow 1 node3366Raw ++ scaleRow (-(1 : ℤ)) node3366 ++
      ([])) = [] := by
  decide +kernel

theorem node3366_mem : rowEval varIndex node3366 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3366Raw node3366 ([])
    (1) (1) (by decide) node3366_check
  · rw [node3366Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0361_mem
  · exact candidateIdeal.zero_mem

def node3382 : WordRow := [([2, 4, 6, 9], 1), ([3, 4, 6, 8], 1)]

def node3382Raw : WordRow := multiplyRow 6 node0363

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3382_check :
    collect (scaleRow 1 node3382Raw ++ scaleRow (-(1 : ℤ)) node3382 ++
      ([])) = [] := by
  decide +kernel

theorem node3382_mem : rowEval varIndex node3382 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3382Raw node3382 ([])
    (1) (1) (by decide) node3382_check
  · rw [node3382Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0363_mem
  · exact candidateIdeal.zero_mem

def node3383 : WordRow := [([3, 4, 4, 11], 1), ([3, 4, 5, 10], 1), ([3, 4, 6, 9], -1)]

def node3383Raw : WordRow := multiplyRow 7 node0363

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3383_check :
    collect (scaleRow 1 node3383Raw ++ scaleRow (-(1 : ℤ)) node3383 ++
      (scaleRow (-1) node2724 ++ scaleRow (1) node2385 ++ scaleRow (-1) node2408)) = [] := by
  decide +kernel

theorem node3383_mem : rowEval varIndex node3383 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3383Raw node3383 (scaleRow (-1) node2724 ++ scaleRow (1) node2385 ++ scaleRow (-1) node2408)
    (1) (1) (by decide) node3383_check
  · rw [node3383Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0363_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2724 node2724_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node2385 node2385_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2408 node2408_mem)))

def node3410 : WordRow := [([2, 6, 9, 13], 1), ([3, 6, 8, 13], 1)]

def node3410Raw : WordRow := multiplyRow 13 node0365

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3410_check :
    collect (scaleRow 1 node3410Raw ++ scaleRow (-(1 : ℤ)) node3410 ++
      ([])) = [] := by
  decide +kernel

theorem node3410_mem : rowEval varIndex node3410 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3410Raw node3410 ([])
    (1) (1) (by decide) node3410_check
  · rw [node3410Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0365_mem
  · exact candidateIdeal.zero_mem

def node3411 : WordRow := [([2, 6, 9, 14], 1), ([3, 6, 8, 14], 1)]

def node3411Raw : WordRow := multiplyRow 14 node0365

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3411_check :
    collect (scaleRow 1 node3411Raw ++ scaleRow (-(1 : ℤ)) node3411 ++
      ([])) = [] := by
  decide +kernel

theorem node3411_mem : rowEval varIndex node3411 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3411Raw node3411 ([])
    (1) (1) (by decide) node3411_check
  · rw [node3411Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0365_mem
  · exact candidateIdeal.zero_mem

def node3414 : WordRow := [([2, 6, 9, 17], 1), ([3, 6, 8, 17], 1)]

def node3414Raw : WordRow := multiplyRow 17 node0365

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3414_check :
    collect (scaleRow 1 node3414Raw ++ scaleRow (-(1 : ℤ)) node3414 ++
      ([])) = [] := by
  decide +kernel

theorem node3414_mem : rowEval varIndex node3414 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3414Raw node3414 ([])
    (1) (1) (by decide) node3414_check
  · rw [node3414Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0365_mem
  · exact candidateIdeal.zero_mem

def node3419 : WordRow := [([2, 7, 9, 12], 1), ([3, 7, 8, 12], 1)]

def node3419Raw : WordRow := multiplyRow 12 node0366

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3419_check :
    collect (scaleRow 1 node3419Raw ++ scaleRow (-(1 : ℤ)) node3419 ++
      ([])) = [] := by
  decide +kernel

theorem node3419_mem : rowEval varIndex node3419 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3419Raw node3419 ([])
    (1) (1) (by decide) node3419_check
  · rw [node3419Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0366_mem
  · exact candidateIdeal.zero_mem

def node3421 : WordRow := [([2, 7, 9, 14], 1), ([3, 7, 8, 14], 1)]

def node3421Raw : WordRow := multiplyRow 14 node0366

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3421_check :
    collect (scaleRow 1 node3421Raw ++ scaleRow (-(1 : ℤ)) node3421 ++
      ([])) = [] := by
  decide +kernel

theorem node3421_mem : rowEval varIndex node3421 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3421Raw node3421 ([])
    (1) (1) (by decide) node3421_check
  · rw [node3421Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0366_mem
  · exact candidateIdeal.zero_mem

def node3423 : WordRow := [([2, 7, 9, 16], 1), ([3, 7, 8, 16], 1)]

def node3423Raw : WordRow := multiplyRow 16 node0366

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3423_check :
    collect (scaleRow 1 node3423Raw ++ scaleRow (-(1 : ℤ)) node3423 ++
      ([])) = [] := by
  decide +kernel

theorem node3423_mem : rowEval varIndex node3423 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3423Raw node3423 ([])
    (1) (1) (by decide) node3423_check
  · rw [node3423Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0366_mem
  · exact candidateIdeal.zero_mem

def node3447 : WordRow := [([2, 9, 10, 13], 1), ([3, 8, 10, 13], 1)]

def node3447Raw : WordRow := multiplyRow 13 node0369

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3447_check :
    collect (scaleRow 1 node3447Raw ++ scaleRow (-(1 : ℤ)) node3447 ++
      ([])) = [] := by
  decide +kernel

theorem node3447_mem : rowEval varIndex node3447 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3447Raw node3447 ([])
    (1) (1) (by decide) node3447_check
  · rw [node3447Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0369_mem
  · exact candidateIdeal.zero_mem

def node3451 : WordRow := [([2, 9, 10, 17], 1), ([3, 8, 10, 17], 1)]

def node3451Raw : WordRow := multiplyRow 17 node0369

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3451_check :
    collect (scaleRow 1 node3451Raw ++ scaleRow (-(1 : ℤ)) node3451 ++
      ([])) = [] := by
  decide +kernel

theorem node3451_mem : rowEval varIndex node3451 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3451Raw node3451 ([])
    (1) (1) (by decide) node3451_check
  · rw [node3451Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0369_mem
  · exact candidateIdeal.zero_mem

def node3453 : WordRow := [([2, 9, 11, 12], 1), ([3, 8, 11, 12], 1)]

def node3453Raw : WordRow := multiplyRow 12 node0370

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3453_check :
    collect (scaleRow 1 node3453Raw ++ scaleRow (-(1 : ℤ)) node3453 ++
      ([])) = [] := by
  decide +kernel

theorem node3453_mem : rowEval varIndex node3453 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3453Raw node3453 ([])
    (1) (1) (by decide) node3453_check
  · rw [node3453Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0370_mem
  · exact candidateIdeal.zero_mem

def node3457 : WordRow := [([2, 9, 11, 16], 1), ([3, 8, 11, 16], 1)]

def node3457Raw : WordRow := multiplyRow 16 node0370

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3457_check :
    collect (scaleRow 1 node3457Raw ++ scaleRow (-(1 : ℤ)) node3457 ++
      ([])) = [] := by
  decide +kernel

theorem node3457_mem : rowEval varIndex node3457 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3457Raw node3457 ([])
    (1) (1) (by decide) node3457_check
  · rw [node3457Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0370_mem
  · exact candidateIdeal.zero_mem

def node3459 : WordRow := [([2, 9, 12, 12], 1), ([3, 8, 12, 12], 1)]

def node3459Raw : WordRow := multiplyRow 12 node0371

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3459_check :
    collect (scaleRow 1 node3459Raw ++ scaleRow (-(1 : ℤ)) node3459 ++
      ([])) = [] := by
  decide +kernel

theorem node3459_mem : rowEval varIndex node3459 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3459Raw node3459 ([])
    (1) (1) (by decide) node3459_check
  · rw [node3459Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0371_mem
  · exact candidateIdeal.zero_mem

def node3460 : WordRow := [([2, 9, 12, 13], 1), ([3, 8, 12, 13], 1)]

def node3460Raw : WordRow := multiplyRow 13 node0371

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3460_check :
    collect (scaleRow 1 node3460Raw ++ scaleRow (-(1 : ℤ)) node3460 ++
      ([])) = [] := by
  decide +kernel

theorem node3460_mem : rowEval varIndex node3460 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3460Raw node3460 ([])
    (1) (1) (by decide) node3460_check
  · rw [node3460Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0371_mem
  · exact candidateIdeal.zero_mem

def node3461 : WordRow := [([2, 9, 12, 14], 1), ([3, 8, 12, 14], 1)]

def node3461Raw : WordRow := multiplyRow 14 node0371

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3461_check :
    collect (scaleRow 1 node3461Raw ++ scaleRow (-(1 : ℤ)) node3461 ++
      ([])) = [] := by
  decide +kernel

theorem node3461_mem : rowEval varIndex node3461 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3461Raw node3461 ([])
    (1) (1) (by decide) node3461_check
  · rw [node3461Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0371_mem
  · exact candidateIdeal.zero_mem

def node3463 : WordRow := [([2, 9, 12, 16], 1), ([3, 8, 12, 16], 1)]

def node3463Raw : WordRow := multiplyRow 16 node0371

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3463_check :
    collect (scaleRow 1 node3463Raw ++ scaleRow (-(1 : ℤ)) node3463 ++
      ([])) = [] := by
  decide +kernel

theorem node3463_mem : rowEval varIndex node3463 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3463Raw node3463 ([])
    (1) (1) (by decide) node3463_check
  · rw [node3463Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0371_mem
  · exact candidateIdeal.zero_mem

def node3464 : WordRow := [([2, 9, 12, 17], 1), ([3, 8, 12, 17], 1)]

def node3464Raw : WordRow := multiplyRow 17 node0371

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3464_check :
    collect (scaleRow 1 node3464Raw ++ scaleRow (-(1 : ℤ)) node3464 ++
      ([])) = [] := by
  decide +kernel

theorem node3464_mem : rowEval varIndex node3464 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3464Raw node3464 ([])
    (1) (1) (by decide) node3464_check
  · rw [node3464Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0371_mem
  · exact candidateIdeal.zero_mem

def node3468 : WordRow := [([2, 9, 13, 16], 1), ([3, 8, 13, 16], 1)]

def node3468Raw : WordRow := multiplyRow 16 node0372

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3468_check :
    collect (scaleRow 1 node3468Raw ++ scaleRow (-(1 : ℤ)) node3468 ++
      ([])) = [] := by
  decide +kernel

theorem node3468_mem : rowEval varIndex node3468 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3468Raw node3468 ([])
    (1) (1) (by decide) node3468_check
  · rw [node3468Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0372_mem
  · exact candidateIdeal.zero_mem

def node3472 : WordRow := [([2, 9, 14, 16], 1), ([3, 8, 14, 16], 1)]

def node3472Raw : WordRow := multiplyRow 16 node0373

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3472_check :
    collect (scaleRow 1 node3472Raw ++ scaleRow (-(1 : ℤ)) node3472 ++
      ([])) = [] := by
  decide +kernel

theorem node3472_mem : rowEval varIndex node3472 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3472Raw node3472 ([])
    (1) (1) (by decide) node3472_check
  · rw [node3472Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0373_mem
  · exact candidateIdeal.zero_mem

def node3478 : WordRow := [([2, 9, 16, 17], 1), ([3, 8, 16, 17], 1)]

def node3478Raw : WordRow := multiplyRow 17 node0375

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3478_check :
    collect (scaleRow 1 node3478Raw ++ scaleRow (-(1 : ℤ)) node3478 ++
      ([])) = [] := by
  decide +kernel

theorem node3478_mem : rowEval varIndex node3478 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3478Raw node3478 ([])
    (1) (1) (by decide) node3478_check
  · rw [node3478Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0375_mem
  · exact candidateIdeal.zero_mem

def node3481 : WordRow := [([3, 4, 6, 9], 1)]

def node3481Raw : WordRow := multiplyRow 6 node0377

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node3481_check :
    collect (scaleRow 1 node3481Raw ++ scaleRow (-(1 : ℤ)) node3481 ++
      ([])) = [] := by
  decide +kernel

theorem node3481_mem : rowEval varIndex node3481 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node3481Raw node3481 ([])
    (1) (1) (by decide) node3481_check
  · rw [node3481Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0377_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node3481_mem
