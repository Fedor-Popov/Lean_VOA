import VOA.DeligneAudit.D4FusionContactM2Dag16

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node5921 : WordRow := [([3, 14, 16, 17], 2), ([8, 11, 16, 17], 1), ([9, 10, 16, 17], 1)]

def node5921Raw : WordRow := multiplyRow 2 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5921_check :
    collect (scaleRow 1 node5921Raw ++ scaleRow (-(-2 : ℤ)) node5921 ++
      (scaleRow (-1) node5838 ++ scaleRow (-2) node4871)) = [] := by
  decide +kernel

theorem node5921_mem : rowEval varIndex node5921 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5921Raw node5921 (scaleRow (-1) node5838 ++ scaleRow (-2) node4871)
    (1) (-2) (by decide) node5921_check
  · rw [node5921Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5838 node5838_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node4871 node4871_mem))

def node5922 : WordRow := [([5, 14, 16, 17], 2), ([8, 13, 16, 17], 1), ([9, 12, 16, 17], 1)]

def node5922Raw : WordRow := multiplyRow 4 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5922_check :
    collect (scaleRow 1 node5922Raw ++ scaleRow (-(-2 : ℤ)) node5922 ++
      (scaleRow (-1) node5857 ++ scaleRow (-2) node5139)) = [] := by
  decide +kernel

theorem node5922_mem : rowEval varIndex node5922 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5922Raw node5922 (scaleRow (-1) node5857 ++ scaleRow (-2) node5139)
    (1) (-2) (by decide) node5922_check
  · rw [node5922Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5857 node5857_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5139 node5139_mem))

def node5923 : WordRow := [([7, 14, 16, 17], 2), ([10, 13, 16, 17], 1), ([11, 12, 16, 17], 1)]

def node5923Raw : WordRow := multiplyRow 6 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5923_check :
    collect (scaleRow 1 node5923Raw ++ scaleRow (-(-2 : ℤ)) node5923 ++
      (scaleRow (-1) node5876 ++ scaleRow (-2) node5279)) = [] := by
  decide +kernel

theorem node5923_mem : rowEval varIndex node5923 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5923Raw node5923 (scaleRow (-1) node5876 ++ scaleRow (-2) node5279)
    (1) (-2) (by decide) node5923_check
  · rw [node5923Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5876 node5876_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5279 node5279_mem))

def node5924 : WordRow := [([9, 14, 16, 17], 1)]

def node5924Raw : WordRow := multiplyRow 8 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5924_check :
    collect (scaleRow 1 node5924Raw ++ scaleRow (-(-4 : ℤ)) node5924 ++
      (scaleRow (-1) node5891 ++ scaleRow (-2) node5484)) = [] := by
  decide +kernel

theorem node5924_mem : rowEval varIndex node5924 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5924Raw node5924 (scaleRow (-1) node5891 ++ scaleRow (-2) node5484)
    (1) (-4) (by decide) node5924_check
  · rw [node5924Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5891 node5891_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5484 node5484_mem))

def node5925 : WordRow := [([11, 14, 16, 17], 1)]

def node5925Raw : WordRow := multiplyRow 10 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5925_check :
    collect (scaleRow 1 node5925Raw ++ scaleRow (-(-4 : ℤ)) node5925 ++
      (scaleRow (-1) node5904 ++ scaleRow (-2) node5593)) = [] := by
  decide +kernel

theorem node5925_mem : rowEval varIndex node5925 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5925Raw node5925 (scaleRow (-1) node5904 ++ scaleRow (-2) node5593)
    (1) (-4) (by decide) node5925_check
  · rw [node5925Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5904 node5904_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5593 node5593_mem))

def node5926 : WordRow := [([13, 14, 16, 17], 1)]

def node5926Raw : WordRow := multiplyRow 12 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5926_check :
    collect (scaleRow 1 node5926Raw ++ scaleRow (-(-4 : ℤ)) node5926 ++
      (scaleRow (-1) node5917 ++ scaleRow (-2) node5671)) = [] := by
  decide +kernel

theorem node5926_mem : rowEval varIndex node5926 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5926Raw node5926 (scaleRow (-1) node5917 ++ scaleRow (-2) node5671)
    (1) (-4) (by decide) node5926_check
  · rw [node5926Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5917 node5917_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node5671 node5671_mem))

def node5928 : WordRow := [([15, 16, 16, 17], 1)]

def node5928Raw : WordRow := multiplyRow 16 node0790

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5928_check :
    collect (scaleRow 1 node5928Raw ++ scaleRow (-(2 : ℤ)) node5928 ++
      (scaleRow (-1) node5754)) = [] := by
  decide +kernel

theorem node5928_mem : rowEval varIndex node5928 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5928Raw node5928 (scaleRow (-1) node5754)
    (1) (2) (by decide) node5928_check
  · rw [node5928Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0790_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5754 node5754_mem)

def node5940 : WordRow := [([0, 2, 4, 6], 1)]

def node5940Raw : WordRow := multiplyRow 6 node0793

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5940_check :
    collect (scaleRow 1 node5940Raw ++ scaleRow (-(-2 : ℤ)) node5940 ++
      (scaleRow (-1) node5795)) = [] := by
  decide +kernel

theorem node5940_mem : rowEval varIndex node5940 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5940Raw node5940 (scaleRow (-1) node5795)
    (1) (-2) (by decide) node5940_check
  · rw [node5940Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0793_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5795 node5795_mem)

def node5945 : WordRow := [([2, 4, 7, 8], 1), ([3, 4, 6, 8], 1)]

def node5945Raw : WordRow := multiplyRow 15 node0793

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5945_check :
    collect (scaleRow 1 node5945Raw ++ scaleRow (-(2 : ℤ)) node5945 ++
      (scaleRow (-1) node3943 ++ scaleRow (1) node0992 ++ scaleRow (2) node3954 ++ scaleRow (-1) node2955 ++ scaleRow (-1) node1296 ++ scaleRow (-1) node2526 ++ scaleRow (-1) node1581 ++ scaleRow (-1) node2303 ++ scaleRow (-1) node1831 ++ scaleRow (-1) node4766 ++ scaleRow (1) node3362 ++ scaleRow (2) node3752 ++ scaleRow (2) node4608 ++ scaleRow (1) node4318 ++ scaleRow (2) node2016 ++ scaleRow (1) node3600 ++ scaleRow (2) node2723 ++ scaleRow (1) node3382)) = [] := by
  decide +kernel

theorem node5945_mem : rowEval varIndex node5945 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5945Raw node5945 (scaleRow (-1) node3943 ++ scaleRow (1) node0992 ++ scaleRow (2) node3954 ++ scaleRow (-1) node2955 ++ scaleRow (-1) node1296 ++ scaleRow (-1) node2526 ++ scaleRow (-1) node1581 ++ scaleRow (-1) node2303 ++ scaleRow (-1) node1831 ++ scaleRow (-1) node4766 ++ scaleRow (1) node3362 ++ scaleRow (2) node3752 ++ scaleRow (2) node4608 ++ scaleRow (1) node4318 ++ scaleRow (2) node2016 ++ scaleRow (1) node3600 ++ scaleRow (2) node2723 ++ scaleRow (1) node3382)
    (1) (2) (by decide) node5945_check
  · rw [node5945Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0793_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3943 node3943_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node0992 node0992_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3954 node3954_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2955 node2955_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1296 node1296_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2526 node2526_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1581 node1581_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2303 node2303_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1831 node1831_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4766 node4766_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3362 node3362_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3752 node3752_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4608 node4608_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4318 node4318_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2016 node2016_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3600 node3600_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2723 node2723_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3382 node3382_mem))))))))))))))))))

def node5947 : WordRow := [([0, 0, 8, 17], 1), ([0, 2, 4, 17], -2)]

def node5947Raw : WordRow := multiplyRow 17 node0793

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5947_check :
    collect (scaleRow 1 node5947Raw ++ scaleRow (-(1 : ℤ)) node5947 ++
      ([])) = [] := by
  decide +kernel

theorem node5947_mem : rowEval varIndex node5947 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5947Raw node5947 ([])
    (1) (1) (by decide) node5947_check
  · rw [node5947Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0793_mem
  · exact candidateIdeal.zero_mem

def node5953 : WordRow := [([2, 5, 6, 10], 2), ([2, 6, 6, 9], -1), ([2, 6, 7, 8], -2), ([3, 4, 6, 10], 2), ([3, 6, 6, 8], -1)]

def node5953Raw : WordRow := multiplyRow 15 node0794

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5953_check :
    collect (scaleRow 1 node5953Raw ++ scaleRow (-(1 : ℤ)) node5953 ++
      (scaleRow (-1) node3945 ++ scaleRow (1) node1009 ++ scaleRow (2) node3955 ++ scaleRow (-1) node2957 ++ scaleRow (-1) node1313 ++ scaleRow (-1) node2528 ++ scaleRow (-1) node1598 ++ scaleRow (-1) node2305 ++ scaleRow (-1) node1833 ++ scaleRow (-1) node4767 ++ scaleRow (1) node3582 ++ scaleRow (2) node4921 ++ scaleRow (2) node4143 ++ scaleRow (1) node4478 ++ scaleRow (2) node2041 ++ scaleRow (1) node3601)) = [] := by
  decide +kernel

theorem node5953_mem : rowEval varIndex node5953 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5953Raw node5953 (scaleRow (-1) node3945 ++ scaleRow (1) node1009 ++ scaleRow (2) node3955 ++ scaleRow (-1) node2957 ++ scaleRow (-1) node1313 ++ scaleRow (-1) node2528 ++ scaleRow (-1) node1598 ++ scaleRow (-1) node2305 ++ scaleRow (-1) node1833 ++ scaleRow (-1) node4767 ++ scaleRow (1) node3582 ++ scaleRow (2) node4921 ++ scaleRow (2) node4143 ++ scaleRow (1) node4478 ++ scaleRow (2) node2041 ++ scaleRow (1) node3601)
    (1) (1) (by decide) node5953_check
  · rw [node5953Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0794_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3945 node3945_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node1009 node1009_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3955 node3955_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2957 node2957_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1313 node1313_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2528 node2528_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1598 node1598_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2305 node2305_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1833 node1833_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4767 node4767_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node3582 node3582_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4921 node4921_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4143 node4143_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4478 node4478_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node2041 node2041_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3601 node3601_mem))))))))))))))))

def node5955 : WordRow := [([0, 0, 10, 17], 1), ([0, 2, 6, 17], -2)]

def node5955Raw : WordRow := multiplyRow 17 node0794

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5955_check :
    collect (scaleRow 1 node5955Raw ++ scaleRow (-(1 : ℤ)) node5955 ++
      ([])) = [] := by
  decide +kernel

theorem node5955_mem : rowEval varIndex node5955 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5955Raw node5955 ([])
    (1) (1) (by decide) node5955_check
  · rw [node5955Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0794_mem
  · exact candidateIdeal.zero_mem

def node5970 : WordRow := [([2, 5, 6, 12], 2), ([3, 4, 6, 12], 2), ([4, 4, 6, 11], -1), ([4, 4, 7, 10], -1), ([4, 5, 6, 10], -2), ([4, 6, 6, 9], -1), ([4, 6, 7, 8], -2), ([5, 6, 6, 8], -1)]

def node5970Raw : WordRow := multiplyRow 15 node0796

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5970_check :
    collect (scaleRow 1 node5970Raw ++ scaleRow (-(1 : ℤ)) node5970 ++
      (scaleRow (-1) node3947 ++ scaleRow (1) node1022 ++ scaleRow (-1) node2959 ++ scaleRow (-1) node1326 ++ scaleRow (2) node3974 ++ scaleRow (-1) node2530 ++ scaleRow (-1) node1600 ++ scaleRow (-1) node2307 ++ scaleRow (-1) node1835 ++ scaleRow (2) node5313 ++ scaleRow (-1) node5039 ++ scaleRow (1) node4310 ++ scaleRow (2) node4470 ++ scaleRow (1) node4320)) = [] := by
  decide +kernel

theorem node5970_mem : rowEval varIndex node5970 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5970Raw node5970 (scaleRow (-1) node3947 ++ scaleRow (1) node1022 ++ scaleRow (-1) node2959 ++ scaleRow (-1) node1326 ++ scaleRow (2) node3974 ++ scaleRow (-1) node2530 ++ scaleRow (-1) node1600 ++ scaleRow (-1) node2307 ++ scaleRow (-1) node1835 ++ scaleRow (2) node5313 ++ scaleRow (-1) node5039 ++ scaleRow (1) node4310 ++ scaleRow (2) node4470 ++ scaleRow (1) node4320)
    (1) (1) (by decide) node5970_check
  · rw [node5970Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0796_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3947 node3947_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node1022 node1022_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2959 node2959_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1326 node1326_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node3974 node3974_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2530 node2530_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1600 node1600_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2307 node2307_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1835 node1835_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node5313 node5313_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5039 node5039_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (1) node4310 node4310_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (2) node4470 node4470_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4320 node4320_mem))))))))))))))

def node5972 : WordRow := [([0, 0, 12, 17], 1), ([0, 4, 6, 17], -2)]

def node5972Raw : WordRow := multiplyRow 17 node0796

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5972_check :
    collect (scaleRow 1 node5972Raw ++ scaleRow (-(1 : ℤ)) node5972 ++
      ([])) = [] := by
  decide +kernel

theorem node5972_mem : rowEval varIndex node5972 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5972Raw node5972 ([])
    (1) (1) (by decide) node5972_check
  · rw [node5972Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0796_mem
  · exact candidateIdeal.zero_mem

def node5981 : WordRow := [([1, 2, 4, 17], 2), ([1, 2, 5, 16], 1)]

def node5981Raw : WordRow := multiplyRow 0 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5981_check :
    collect (scaleRow 1 node5981Raw ++ scaleRow (-(-1 : ℤ)) node5981 ++
      (scaleRow (-1) node1514 ++ scaleRow (-1) node1255 ++ scaleRow (-1) node1267)) = [] := by
  decide +kernel

theorem node5981_mem : rowEval varIndex node5981 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5981Raw node5981 (scaleRow (-1) node1514 ++ scaleRow (-1) node1255 ++ scaleRow (-1) node1267)
    (1) (-1) (by decide) node5981_check
  · rw [node5981Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1514 node1514_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1255 node1255_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1267 node1267_mem)))

def node5983 : WordRow := [([3, 4, 4, 17], 1), ([3, 4, 5, 16], 1)]

def node5983Raw : WordRow := multiplyRow 4 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5983_check :
    collect (scaleRow 1 node5983Raw ++ scaleRow (-(1 : ℤ)) node5983 ++
      (scaleRow (-1) node2730)) = [] := by
  decide +kernel

theorem node5983_mem : rowEval varIndex node5983 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5983Raw node5983 (scaleRow (-1) node2730)
    (1) (1) (by decide) node5983_check
  · rw [node5983Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node2730 node2730_mem)

def node5984 : WordRow := [([2, 5, 6, 17], 1), ([3, 4, 6, 17], 1), ([3, 5, 6, 16], 1)]

def node5984Raw : WordRow := multiplyRow 6 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5984_check :
    collect (scaleRow 1 node5984Raw ++ scaleRow (-(1 : ℤ)) node5984 ++
      ([])) = [] := by
  decide +kernel

theorem node5984_mem : rowEval varIndex node5984 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5984Raw node5984 ([])
    (1) (1) (by decide) node5984_check
  · rw [node5984Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · exact candidateIdeal.zero_mem

def node5986 : WordRow := [([3, 4, 8, 17], 2), ([3, 5, 8, 16], 1)]

def node5986Raw : WordRow := multiplyRow 8 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5986_check :
    collect (scaleRow 1 node5986Raw ++ scaleRow (-(1 : ℤ)) node5986 ++
      (scaleRow (-1) node3773)) = [] := by
  decide +kernel

theorem node5986_mem : rowEval varIndex node5986 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5986Raw node5986 (scaleRow (-1) node3773)
    (1) (1) (by decide) node5986_check
  · rw [node5986Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node3773 node3773_mem)

def node5987 : WordRow := [([2, 5, 10, 17], 1), ([3, 4, 10, 17], 1), ([3, 5, 10, 16], 1)]

def node5987Raw : WordRow := multiplyRow 10 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5987_check :
    collect (scaleRow 1 node5987Raw ++ scaleRow (-(1 : ℤ)) node5987 ++
      ([])) = [] := by
  decide +kernel

theorem node5987_mem : rowEval varIndex node5987 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5987Raw node5987 ([])
    (1) (1) (by decide) node5987_check
  · rw [node5987Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · exact candidateIdeal.zero_mem

def node5989 : WordRow := [([2, 5, 12, 17], 1), ([3, 4, 12, 17], 1), ([3, 5, 12, 16], 1)]

def node5989Raw : WordRow := multiplyRow 12 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5989_check :
    collect (scaleRow 1 node5989Raw ++ scaleRow (-(1 : ℤ)) node5989 ++
      ([])) = [] := by
  decide +kernel

theorem node5989_mem : rowEval varIndex node5989 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5989Raw node5989 ([])
    (1) (1) (by decide) node5989_check
  · rw [node5989Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · exact candidateIdeal.zero_mem

def node5991 : WordRow := [([2, 8, 13, 17], 1), ([2, 9, 12, 17], 1), ([3, 4, 14, 17], -2), ([3, 5, 14, 16], -1), ([4, 8, 11, 17], -1), ([4, 9, 10, 17], -1)]

def node5991Raw : WordRow := multiplyRow 14 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5991_check :
    collect (scaleRow 1 node5991Raw ++ scaleRow (-(-1 : ℤ)) node5991 ++
      (scaleRow (-1) node5061)) = [] := by
  decide +kernel

theorem node5991_mem : rowEval varIndex node5991 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5991Raw node5991 (scaleRow (-1) node5061)
    (1) (-1) (by decide) node5991_check
  · rw [node5991Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5061 node5061_mem)

def node5993 : WordRow := [([3, 4, 16, 17], 2), ([3, 5, 16, 16], 1)]

def node5993Raw : WordRow := multiplyRow 16 node0798

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5993_check :
    collect (scaleRow 1 node5993Raw ++ scaleRow (-(1 : ℤ)) node5993 ++
      (scaleRow (-1) node5846)) = [] := by
  decide +kernel

theorem node5993_mem : rowEval varIndex node5993 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5993Raw node5993 (scaleRow (-1) node5846)
    (1) (1) (by decide) node5993_check
  · rw [node5993Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0798_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5846 node5846_mem)

def node5994 : WordRow := [([1, 2, 6, 17], 2), ([1, 2, 7, 16], 1)]

def node5994Raw : WordRow := multiplyRow 0 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5994_check :
    collect (scaleRow 1 node5994Raw ++ scaleRow (-(-1 : ℤ)) node5994 ++
      (scaleRow (-1) node1769 ++ scaleRow (-1) node1280 ++ scaleRow (-1) node1290)) = [] := by
  decide +kernel

theorem node5994_mem : rowEval varIndex node5994 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5994Raw node5994 (scaleRow (-1) node1769 ++ scaleRow (-1) node1280 ++ scaleRow (-1) node1290)
    (1) (-1) (by decide) node5994_check
  · rw [node5994Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1769 node1769_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1280 node1280_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1290 node1290_mem)))

def node5996 : WordRow := [([2, 4, 7, 17], 1), ([3, 4, 6, 17], 1), ([3, 4, 7, 16], 1)]

def node5996Raw : WordRow := multiplyRow 4 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5996_check :
    collect (scaleRow 1 node5996Raw ++ scaleRow (-(1 : ℤ)) node5996 ++
      ([])) = [] := by
  decide +kernel

theorem node5996_mem : rowEval varIndex node5996 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5996Raw node5996 ([])
    (1) (1) (by decide) node5996_check
  · rw [node5996Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · exact candidateIdeal.zero_mem

def node5998 : WordRow := [([3, 6, 6, 17], 1), ([3, 6, 7, 16], 1)]

def node5998Raw : WordRow := multiplyRow 6 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5998_check :
    collect (scaleRow 1 node5998Raw ++ scaleRow (-(1 : ℤ)) node5998 ++
      (scaleRow (-1) node3179)) = [] := by
  decide +kernel

theorem node5998_mem : rowEval varIndex node5998 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5998Raw node5998 (scaleRow (-1) node3179)
    (1) (1) (by decide) node5998_check
  · rw [node5998Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node3179 node3179_mem)

def node5999 : WordRow := [([2, 7, 8, 17], 1), ([3, 6, 8, 17], 1), ([3, 7, 8, 16], 1)]

def node5999Raw : WordRow := multiplyRow 8 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node5999_check :
    collect (scaleRow 1 node5999Raw ++ scaleRow (-(1 : ℤ)) node5999 ++
      ([])) = [] := by
  decide +kernel

theorem node5999_mem : rowEval varIndex node5999 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node5999Raw node5999 ([])
    (1) (1) (by decide) node5999_check
  · rw [node5999Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · exact candidateIdeal.zero_mem

def node6001 : WordRow := [([3, 6, 10, 17], 2), ([3, 7, 10, 16], 1)]

def node6001Raw : WordRow := multiplyRow 10 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6001_check :
    collect (scaleRow 1 node6001Raw ++ scaleRow (-(1 : ℤ)) node6001 ++
      (scaleRow (-1) node4163)) = [] := by
  decide +kernel

theorem node6001_mem : rowEval varIndex node6001 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6001Raw node6001 (scaleRow (-1) node4163)
    (1) (1) (by decide) node6001_check
  · rw [node6001Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4163 node4163_mem)

def node6002 : WordRow := [([2, 7, 12, 17], 1), ([3, 6, 12, 17], 1), ([3, 7, 12, 16], 1)]

def node6002Raw : WordRow := multiplyRow 12 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6002_check :
    collect (scaleRow 1 node6002Raw ++ scaleRow (-(1 : ℤ)) node6002 ++
      ([])) = [] := by
  decide +kernel

theorem node6002_mem : rowEval varIndex node6002 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6002Raw node6002 ([])
    (1) (1) (by decide) node6002_check
  · rw [node6002Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · exact candidateIdeal.zero_mem

def node6004 : WordRow := [([2, 10, 13, 17], 1), ([2, 11, 12, 17], 1), ([3, 6, 14, 17], -2), ([3, 7, 14, 16], -1), ([6, 8, 11, 17], -1), ([6, 9, 10, 17], -1)]

def node6004Raw : WordRow := multiplyRow 14 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6004_check :
    collect (scaleRow 1 node6004Raw ++ scaleRow (-(-1 : ℤ)) node6004 ++
      (scaleRow (-1) node5205)) = [] := by
  decide +kernel

theorem node6004_mem : rowEval varIndex node6004 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6004Raw node6004 (scaleRow (-1) node5205)
    (1) (-1) (by decide) node6004_check
  · rw [node6004Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5205 node5205_mem)

def node6006 : WordRow := [([3, 6, 16, 17], 2), ([3, 7, 16, 16], 1)]

def node6006Raw : WordRow := multiplyRow 16 node0800

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6006_check :
    collect (scaleRow 1 node6006Raw ++ scaleRow (-(1 : ℤ)) node6006 ++
      (scaleRow (-1) node5865)) = [] := by
  decide +kernel

theorem node6006_mem : rowEval varIndex node6006 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6006Raw node6006 (scaleRow (-1) node5865)
    (1) (1) (by decide) node6006_check
  · rw [node6006Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0800_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5865 node5865_mem)

def node6007 : WordRow := [([1, 4, 6, 17], 2), ([1, 4, 7, 16], 1)]

def node6007Raw : WordRow := multiplyRow 0 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6007_check :
    collect (scaleRow 1 node6007Raw ++ scaleRow (-(-1 : ℤ)) node6007 ++
      (scaleRow (-1) node1795 ++ scaleRow (-1) node1567 ++ scaleRow (-1) node1577)) = [] := by
  decide +kernel

theorem node6007_mem : rowEval varIndex node6007 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6007Raw node6007 (scaleRow (-1) node1795 ++ scaleRow (-1) node1567 ++ scaleRow (-1) node1577)
    (1) (-1) (by decide) node6007_check
  · rw [node6007Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1795 node1795_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1567 node1567_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1577 node1577_mem)))

def node6008 : WordRow := [([3, 4, 6, 17], 1), ([3, 4, 7, 16], 1), ([3, 5, 6, 16], 1)]

def node6008Raw : WordRow := multiplyRow 2 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6008_check :
    collect (scaleRow 1 node6008Raw ++ scaleRow (-(-2 : ℤ)) node6008 ++
      (scaleRow (-1) node5996 ++ scaleRow (-1) node5984 ++ scaleRow (-1) node2416)) = [] := by
  decide +kernel

theorem node6008_mem : rowEval varIndex node6008 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6008Raw node6008 (scaleRow (-1) node5996 ++ scaleRow (-1) node5984 ++ scaleRow (-1) node2416)
    (1) (-2) (by decide) node6008_check
  · rw [node6008Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5996 node5996_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5984 node5984_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2416 node2416_mem)))

def node6010 : WordRow := [([5, 6, 6, 17], 1), ([5, 6, 7, 16], 1)]

def node6010Raw : WordRow := multiplyRow 6 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6010_check :
    collect (scaleRow 1 node6010Raw ++ scaleRow (-(1 : ℤ)) node6010 ++
      (scaleRow (-1) node3201)) = [] := by
  decide +kernel

theorem node6010_mem : rowEval varIndex node6010 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6010Raw node6010 (scaleRow (-1) node3201)
    (1) (1) (by decide) node6010_check
  · rw [node6010Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node3201 node3201_mem)

def node6011 : WordRow := [([4, 7, 8, 17], 1), ([5, 6, 8, 17], 1), ([5, 7, 8, 16], 1)]

def node6011Raw : WordRow := multiplyRow 8 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6011_check :
    collect (scaleRow 1 node6011Raw ++ scaleRow (-(1 : ℤ)) node6011 ++
      ([])) = [] := by
  decide +kernel

theorem node6011_mem : rowEval varIndex node6011 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6011Raw node6011 ([])
    (1) (1) (by decide) node6011_check
  · rw [node6011Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · exact candidateIdeal.zero_mem

def node6013 : WordRow := [([4, 7, 10, 17], 1), ([5, 6, 10, 17], 1), ([5, 7, 10, 16], 1)]

def node6013Raw : WordRow := multiplyRow 10 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6013_check :
    collect (scaleRow 1 node6013Raw ++ scaleRow (-(1 : ℤ)) node6013 ++
      ([])) = [] := by
  decide +kernel

theorem node6013_mem : rowEval varIndex node6013 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6013Raw node6013 ([])
    (1) (1) (by decide) node6013_check
  · rw [node6013Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · exact candidateIdeal.zero_mem

def node6015 : WordRow := [([5, 6, 12, 17], 2), ([5, 7, 12, 16], 1)]

def node6015Raw : WordRow := multiplyRow 12 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6015_check :
    collect (scaleRow 1 node6015Raw ++ scaleRow (-(1 : ℤ)) node6015 ++
      (scaleRow (-1) node4506)) = [] := by
  decide +kernel

theorem node6015_mem : rowEval varIndex node6015 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6015Raw node6015 (scaleRow (-1) node4506)
    (1) (1) (by decide) node6015_check
  · rw [node6015Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4506 node4506_mem)

def node6016 : WordRow := [([4, 11, 12, 17], 1), ([5, 6, 14, 17], -2), ([5, 7, 14, 16], -1), ([5, 10, 12, 17], -1), ([6, 8, 13, 17], -1), ([6, 9, 12, 17], -1)]

def node6016Raw : WordRow := multiplyRow 14 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6016_check :
    collect (scaleRow 1 node6016Raw ++ scaleRow (-(-1 : ℤ)) node6016 ++
      (scaleRow (-1) node5222 ++ scaleRow (1) node4390)) = [] := by
  decide +kernel

theorem node6016_mem : rowEval varIndex node6016 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6016Raw node6016 (scaleRow (-1) node5222 ++ scaleRow (1) node4390)
    (1) (-1) (by decide) node6016_check
  · rw [node6016Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5222 node5222_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node4390 node4390_mem))

def node6018 : WordRow := [([5, 6, 16, 17], 2), ([5, 7, 16, 16], 1)]

def node6018Raw : WordRow := multiplyRow 16 node0802

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6018_check :
    collect (scaleRow 1 node6018Raw ++ scaleRow (-(1 : ℤ)) node6018 ++
      (scaleRow (-1) node5867)) = [] := by
  decide +kernel

theorem node6018_mem : rowEval varIndex node6018 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6018Raw node6018 (scaleRow (-1) node5867)
    (1) (1) (by decide) node6018_check
  · rw [node6018Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0802_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5867 node5867_mem)

def node6019 : WordRow := [([1, 2, 12, 17], 2), ([1, 2, 13, 16], 1), ([1, 4, 10, 17], 2), ([1, 4, 11, 16], 1), ([1, 6, 8, 17], 2), ([1, 6, 9, 16], 1), ([2, 4, 7, 17], -2), ([2, 5, 6, 17], -2), ([3, 4, 6, 17], -2)]

def node6019Raw : WordRow := multiplyRow 0 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6019_check :
    collect (scaleRow 1 node6019Raw ++ scaleRow (-(-1 : ℤ)) node6019 ++
      (scaleRow (-1) node2964 ++ scaleRow (-1) node1331 ++ scaleRow (-1) node1335 ++ scaleRow (-1) node2535 ++ scaleRow (-1) node1605 ++ scaleRow (-1) node1611 ++ scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)) = [] := by
  decide +kernel

theorem node6019_mem : rowEval varIndex node6019 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6019Raw node6019 (scaleRow (-1) node2964 ++ scaleRow (-1) node1331 ++ scaleRow (-1) node1335 ++ scaleRow (-1) node2535 ++ scaleRow (-1) node1605 ++ scaleRow (-1) node1611 ++ scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)
    (1) (-1) (by decide) node6019_check
  · rw [node6019Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2964 node2964_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1331 node1331_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1335 node1335_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2535 node2535_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1605 node1605_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1611 node1611_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2312 node2312_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1840 node1840_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1848 node1848_mem)))))))))

def node6021 : WordRow := [([3, 4, 12, 17], 2), ([3, 4, 13, 16], 1), ([3, 5, 12, 16], 1), ([4, 4, 11, 17], 1), ([4, 5, 10, 17], 1), ([4, 5, 11, 16], 1), ([4, 6, 9, 17], 1), ([4, 7, 8, 17], 1), ([4, 7, 9, 16], 1)]

def node6021Raw : WordRow := multiplyRow 4 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6021_check :
    collect (scaleRow 1 node6021Raw ++ scaleRow (-(1 : ℤ)) node6021 ++
      (scaleRow (-1) node4330 ++ scaleRow (1) node5989)) = [] := by
  decide +kernel

theorem node6021_mem : rowEval varIndex node6021 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6021Raw node6021 (scaleRow (-1) node4330 ++ scaleRow (1) node5989)
    (1) (1) (by decide) node6021_check
  · rw [node6021Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4330 node4330_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node5989 node5989_mem))

def node6022 : WordRow := [([3, 6, 12, 17], 2), ([3, 6, 13, 16], 1), ([3, 7, 12, 16], 1), ([4, 6, 11, 17], 1), ([5, 6, 10, 17], 1), ([5, 6, 11, 16], 1), ([6, 6, 9, 17], 1), ([6, 7, 8, 17], 1), ([6, 7, 9, 16], 1)]

def node6022Raw : WordRow := multiplyRow 6 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6022_check :
    collect (scaleRow 1 node6022Raw ++ scaleRow (-(1 : ℤ)) node6022 ++
      (scaleRow (-1) node4489 ++ scaleRow (1) node6002)) = [] := by
  decide +kernel

theorem node6022_mem : rowEval varIndex node6022 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6022Raw node6022 (scaleRow (-1) node4489 ++ scaleRow (1) node6002)
    (1) (1) (by decide) node6022_check
  · rw [node6022Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4489 node4489_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node6002 node6002_mem))

def node6023 : WordRow := [([3, 4, 14, 17], 2), ([3, 5, 14, 16], 1), ([3, 8, 12, 17], 2), ([3, 8, 13, 16], 1), ([4, 8, 11, 17], 2), ([4, 9, 10, 17], 1), ([5, 8, 10, 17], 1), ([5, 8, 11, 16], 1), ([6, 8, 9, 17], 1), ([7, 8, 8, 17], 1), ([7, 8, 9, 16], 1)]

def node6023Raw : WordRow := multiplyRow 8 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6023_check :
    collect (scaleRow 1 node6023Raw ++ scaleRow (-(1 : ℤ)) node6023 ++
      (scaleRow (-1) node5991 ++ scaleRow (1) node3464)) = [] := by
  decide +kernel

theorem node6023_mem : rowEval varIndex node6023 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6023Raw node6023 (scaleRow (-1) node5991 ++ scaleRow (1) node3464)
    (1) (1) (by decide) node6023_check
  · rw [node6023Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5991 node5991_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3464 node3464_mem))

def node6024 : WordRow := [([3, 6, 14, 17], 2), ([3, 7, 14, 16], 1), ([3, 10, 12, 17], 2), ([3, 10, 13, 16], 1), ([4, 10, 11, 17], 1), ([5, 10, 10, 17], 1), ([5, 10, 11, 16], 1), ([6, 8, 11, 17], 1), ([6, 9, 10, 17], 2), ([7, 8, 10, 17], 1), ([7, 9, 10, 16], 1)]

def node6024Raw : WordRow := multiplyRow 10 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6024_check :
    collect (scaleRow 1 node6024Raw ++ scaleRow (-(1 : ℤ)) node6024 ++
      (scaleRow (-1) node6004 ++ scaleRow (1) node3680)) = [] := by
  decide +kernel

theorem node6024_mem : rowEval varIndex node6024 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6024Raw node6024 (scaleRow (-1) node6004 ++ scaleRow (1) node3680)
    (1) (1) (by decide) node6024_check
  · rw [node6024Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6004 node6004_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node3680 node3680_mem))

def node6025 : WordRow := [([3, 12, 12, 17], 1), ([3, 12, 13, 16], 1), ([4, 11, 12, 17], 1), ([5, 10, 12, 17], 1), ([5, 11, 12, 16], 1), ([6, 9, 12, 17], 1), ([7, 8, 12, 17], 1), ([7, 9, 12, 16], 1)]

def node6025Raw : WordRow := multiplyRow 12 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6025_check :
    collect (scaleRow 1 node6025Raw ++ scaleRow (-(1 : ℤ)) node6025 ++
      (scaleRow (-1) node5330)) = [] := by
  decide +kernel

theorem node6025_mem : rowEval varIndex node6025 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6025Raw node6025 (scaleRow (-1) node5330)
    (1) (1) (by decide) node6025_check
  · rw [node6025Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5330 node5330_mem)

def node6026 : WordRow := [([3, 12, 14, 17], 2), ([3, 13, 14, 16], 1), ([4, 11, 14, 17], 1), ([5, 10, 14, 17], 1), ([5, 11, 14, 16], 1), ([6, 9, 14, 17], 1), ([7, 8, 14, 17], 1), ([7, 9, 14, 16], 1), ([8, 11, 12, 17], 1), ([9, 10, 12, 17], 1)]

def node6026Raw : WordRow := multiplyRow 14 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6026_check :
    collect (scaleRow 1 node6026Raw ++ scaleRow (-(1 : ℤ)) node6026 ++
      (scaleRow (-1) node5627)) = [] := by
  decide +kernel

theorem node6026_mem : rowEval varIndex node6026 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6026Raw node6026 (scaleRow (-1) node5627)
    (1) (1) (by decide) node6026_check
  · rw [node6026Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5627 node5627_mem)

def node6027 : WordRow := [([3, 12, 16, 17], 2), ([3, 13, 16, 16], 1), ([4, 11, 16, 17], 1), ([5, 10, 16, 17], 1), ([5, 11, 16, 16], 1), ([6, 9, 16, 17], 1), ([7, 8, 16, 17], 1), ([7, 9, 16, 16], 1)]

def node6027Raw : WordRow := multiplyRow 16 node0804

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6027_check :
    collect (scaleRow 1 node6027Raw ++ scaleRow (-(1 : ℤ)) node6027 ++
      (scaleRow (-1) node5908)) = [] := by
  decide +kernel

theorem node6027_mem : rowEval varIndex node6027 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6027Raw node6027 (scaleRow (-1) node5908)
    (1) (1) (by decide) node6027_check
  · rw [node6027Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0804_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5908 node5908_mem)

def node6028 : WordRow := [([1, 4, 10, 17], 2), ([1, 4, 11, 16], 1), ([1, 6, 8, 17], 2), ([1, 6, 9, 16], 1), ([2, 4, 7, 17], -1), ([2, 5, 6, 17], -1), ([3, 4, 6, 17], -2)]

def node6028Raw : WordRow := multiplyRow 0 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6028_check :
    collect (scaleRow 1 node6028Raw ++ scaleRow (-(-1 : ℤ)) node6028 ++
      (scaleRow (-1) node2535 ++ scaleRow (-1) node1605 ++ scaleRow (-1) node1611 ++ scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)) = [] := by
  decide +kernel

theorem node6028_mem : rowEval varIndex node6028 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6028Raw node6028 (scaleRow (-1) node2535 ++ scaleRow (-1) node1605 ++ scaleRow (-1) node1611 ++ scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)
    (1) (-1) (by decide) node6028_check
  · rw [node6028Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2535 node2535_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1605 node1605_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1611 node1611_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2312 node2312_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1840 node1840_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1848 node1848_mem))))))

def node6029 : WordRow := [([3, 4, 10, 17], 2), ([3, 4, 11, 16], 1), ([3, 5, 10, 16], 2), ([3, 6, 8, 17], 2), ([3, 6, 9, 16], -1), ([3, 7, 8, 16], 2)]

def node6029Raw : WordRow := multiplyRow 2 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6029_check :
    collect (scaleRow 1 node6029Raw ++ scaleRow (-(-1 : ℤ)) node6029 ++
      (scaleRow (-1) node3612 ++ scaleRow (-1) node5987 ++ scaleRow (-1) node2657 ++ scaleRow (-1) node3414 ++ scaleRow (-1) node5999 ++ scaleRow (-2) node3423)) = [] := by
  decide +kernel

theorem node6029_mem : rowEval varIndex node6029 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6029Raw node6029 (scaleRow (-1) node3612 ++ scaleRow (-1) node5987 ++ scaleRow (-1) node2657 ++ scaleRow (-1) node3414 ++ scaleRow (-1) node5999 ++ scaleRow (-2) node3423)
    (1) (-1) (by decide) node6029_check
  · rw [node6029Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3612 node3612_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5987 node5987_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2657 node2657_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3414 node3414_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5999 node5999_mem) (rowEval_scale_mem varIndex candidateIdeal (-2) node3423 node3423_mem))))))

def node6031 : WordRow := [([5, 6, 10, 17], 2), ([5, 6, 11, 16], 1), ([5, 7, 10, 16], 1), ([6, 6, 9, 17], 1), ([6, 7, 8, 17], 1), ([6, 7, 9, 16], 1)]

def node6031Raw : WordRow := multiplyRow 6 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6031_check :
    collect (scaleRow 1 node6031Raw ++ scaleRow (-(1 : ℤ)) node6031 ++
      (scaleRow (-1) node4180 ++ scaleRow (1) node6013)) = [] := by
  decide +kernel

theorem node6031_mem : rowEval varIndex node6031 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6031Raw node6031 (scaleRow (-1) node4180 ++ scaleRow (1) node6013)
    (1) (1) (by decide) node6031_check
  · rw [node6031Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node4180 node4180_mem) (rowEval_scale_mem varIndex candidateIdeal (1) node6013 node6013_mem))

def node6032 : WordRow := [([4, 8, 11, 17], 1), ([5, 8, 10, 17], 1), ([5, 8, 11, 16], 1), ([6, 8, 9, 17], 1), ([7, 8, 8, 17], 1), ([7, 8, 9, 16], 1)]

def node6032Raw : WordRow := multiplyRow 8 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6032_check :
    collect (scaleRow 1 node6032Raw ++ scaleRow (-(1 : ℤ)) node6032 ++
      ([])) = [] := by
  decide +kernel

theorem node6032_mem : rowEval varIndex node6032 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6032Raw node6032 ([])
    (1) (1) (by decide) node6032_check
  · rw [node6032Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · exact candidateIdeal.zero_mem

def node6034 : WordRow := [([5, 10, 10, 17], 1), ([5, 10, 11, 16], 1), ([6, 9, 10, 17], 1), ([7, 8, 10, 17], 1), ([7, 9, 10, 16], 1)]

def node6034Raw : WordRow := multiplyRow 10 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6034_check :
    collect (scaleRow 1 node6034Raw ++ scaleRow (-(1 : ℤ)) node6034 ++
      (scaleRow (-1) node4948)) = [] := by
  decide +kernel

theorem node6034_mem : rowEval varIndex node6034 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6034Raw node6034 (scaleRow (-1) node4948)
    (1) (1) (by decide) node6034_check
  · rw [node6034Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4948 node4948_mem)

def node6036 : WordRow := [([5, 6, 14, 17], 2), ([5, 7, 14, 16], 1), ([5, 10, 12, 17], 2), ([5, 11, 12, 16], 1), ([6, 8, 13, 17], 1), ([6, 9, 12, 17], 2), ([7, 8, 12, 17], 1), ([7, 9, 12, 16], 1)]

def node6036Raw : WordRow := multiplyRow 12 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6036_check :
    collect (scaleRow 1 node6036Raw ++ scaleRow (-(1 : ℤ)) node6036 ++
      (scaleRow (-1) node6016)) = [] := by
  decide +kernel

theorem node6036_mem : rowEval varIndex node6036 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6036Raw node6036 (scaleRow (-1) node6016)
    (1) (1) (by decide) node6036_check
  · rw [node6036Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node6016 node6016_mem)

def node6037 : WordRow := [([5, 10, 14, 17], 2), ([5, 11, 14, 16], 1), ([6, 9, 14, 17], 1), ([7, 8, 14, 17], 1), ([7, 9, 14, 16], 1), ([8, 10, 13, 17], 1), ([9, 10, 12, 17], 1)]

def node6037Raw : WordRow := multiplyRow 14 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6037_check :
    collect (scaleRow 1 node6037Raw ++ scaleRow (-(1 : ℤ)) node6037 ++
      (scaleRow (-1) node5549)) = [] := by
  decide +kernel

theorem node6037_mem : rowEval varIndex node6037 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6037Raw node6037 (scaleRow (-1) node5549)
    (1) (1) (by decide) node6037_check
  · rw [node6037Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5549 node5549_mem)

def node6039 : WordRow := [([5, 10, 16, 17], 2), ([5, 11, 16, 16], 1), ([6, 9, 16, 17], 1), ([7, 8, 16, 17], 1), ([7, 9, 16, 16], 1)]

def node6039Raw : WordRow := multiplyRow 16 node0806

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6039_check :
    collect (scaleRow 1 node6039Raw ++ scaleRow (-(1 : ℤ)) node6039 ++
      (scaleRow (-1) node5896)) = [] := by
  decide +kernel

theorem node6039_mem : rowEval varIndex node6039 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6039Raw node6039 (scaleRow (-1) node5896)
    (1) (1) (by decide) node6039_check
  · rw [node6039Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0806_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5896 node5896_mem)

def node6040 : WordRow := [([1, 8, 10, 17], 2), ([1, 8, 11, 16], 1), ([2, 5, 10, 17], -1), ([2, 5, 11, 16], -1), ([2, 7, 8, 17], -1), ([3, 4, 10, 17], -1), ([3, 4, 11, 16], -1), ([3, 6, 8, 17], -1)]

def node6040Raw : WordRow := multiplyRow 0 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6040_check :
    collect (scaleRow 1 node6040Raw ++ scaleRow (-(-1 : ℤ)) node6040 ++
      (scaleRow (-1) node2580 ++ scaleRow (-1) node2350 ++ scaleRow (-1) node2356)) = [] := by
  decide +kernel

theorem node6040_mem : rowEval varIndex node6040 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6040Raw node6040 (scaleRow (-1) node2580 ++ scaleRow (-1) node2350 ++ scaleRow (-1) node2356)
    (1) (-1) (by decide) node6040_check
  · rw [node6040Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2580 node2580_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2350 node2350_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node2356 node2356_mem)))

def node6041 : WordRow := [([3, 8, 10, 17], 2), ([3, 8, 11, 16], 1)]

def node6041Raw : WordRow := multiplyRow 2 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6041_check :
    collect (scaleRow 1 node6041Raw ++ scaleRow (-(-1 : ℤ)) node6041 ++
      (scaleRow (-1) node3651 ++ scaleRow (-1) node3451 ++ scaleRow (-1) node3457)) = [] := by
  decide +kernel

theorem node6041_mem : rowEval varIndex node6041 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6041Raw node6041 (scaleRow (-1) node3651 ++ scaleRow (-1) node3451 ++ scaleRow (-1) node3457)
    (1) (-1) (by decide) node6041_check
  · rw [node6041Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3651 node3651_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3451 node3451_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3457 node3457_mem)))

def node6042 : WordRow := [([5, 8, 10, 17], 2), ([5, 8, 11, 16], 2), ([6, 8, 9, 17], 1), ([7, 8, 8, 17], 1), ([7, 8, 9, 16], 1)]

def node6042Raw : WordRow := multiplyRow 4 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6042_check :
    collect (scaleRow 1 node6042Raw ++ scaleRow (-(-1 : ℤ)) node6042 ++
      (scaleRow (-1) node6032 ++ scaleRow (-1) node3839 ++ scaleRow (-1) node3845)) = [] := by
  decide +kernel

theorem node6042_mem : rowEval varIndex node6042 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6042Raw node6042 (scaleRow (-1) node6032 ++ scaleRow (-1) node3839 ++ scaleRow (-1) node3845)
    (1) (-1) (by decide) node6042_check
  · rw [node6042Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node6032 node6032_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3839 node3839_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3845 node3845_mem)))

def node6043 : WordRow := [([6, 9, 10, 17], 1), ([6, 9, 11, 16], 1), ([7, 8, 10, 17], -1)]

def node6043Raw : WordRow := multiplyRow 6 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6043_check :
    collect (scaleRow 1 node6043Raw ++ scaleRow (-(1 : ℤ)) node6043 ++
      (scaleRow (-1) node4207)) = [] := by
  decide +kernel

theorem node6043_mem : rowEval varIndex node6043 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6043Raw node6043 (scaleRow (-1) node4207)
    (1) (1) (by decide) node6043_check
  · rw [node6043Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4207 node4207_mem)

def node6045 : WordRow := [([9, 10, 10, 17], 1), ([9, 10, 11, 16], 1)]

def node6045Raw : WordRow := multiplyRow 10 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6045_check :
    collect (scaleRow 1 node6045Raw ++ scaleRow (-(1 : ℤ)) node6045 ++
      (scaleRow (-1) node4967)) = [] := by
  decide +kernel

theorem node6045_mem : rowEval varIndex node6045 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6045Raw node6045 (scaleRow (-1) node4967)
    (1) (1) (by decide) node6045_check
  · rw [node6045Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node4967 node4967_mem)

def node6046 : WordRow := [([8, 11, 12, 17], 1), ([9, 10, 12, 17], 1), ([9, 11, 12, 16], 1)]

def node6046Raw : WordRow := multiplyRow 12 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6046_check :
    collect (scaleRow 1 node6046Raw ++ scaleRow (-(1 : ℤ)) node6046 ++
      ([])) = [] := by
  decide +kernel

theorem node6046_mem : rowEval varIndex node6046 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6046Raw node6046 ([])
    (1) (1) (by decide) node6046_check
  · rw [node6046Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · exact candidateIdeal.zero_mem

def node6047 : WordRow := [([9, 10, 14, 17], 2), ([9, 11, 14, 16], 1)]

def node6047Raw : WordRow := multiplyRow 14 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6047_check :
    collect (scaleRow 1 node6047Raw ++ scaleRow (-(1 : ℤ)) node6047 ++
      (scaleRow (-1) node5567)) = [] := by
  decide +kernel

theorem node6047_mem : rowEval varIndex node6047 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6047Raw node6047 (scaleRow (-1) node5567)
    (1) (1) (by decide) node6047_check
  · rw [node6047Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5567 node5567_mem)

def node6048 : WordRow := [([9, 10, 16, 17], 2), ([9, 11, 16, 16], 1)]

def node6048Raw : WordRow := multiplyRow 16 node0808

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6048_check :
    collect (scaleRow 1 node6048Raw ++ scaleRow (-(1 : ℤ)) node6048 ++
      (scaleRow (-1) node5899)) = [] := by
  decide +kernel

theorem node6048_mem : rowEval varIndex node6048 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6048Raw node6048 (scaleRow (-1) node5899)
    (1) (1) (by decide) node6048_check
  · rw [node6048Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0808_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node5899 node5899_mem)

def node6049 : WordRow := [([1, 6, 8, 17], 2), ([1, 6, 9, 16], 1), ([2, 5, 6, 17], -1), ([3, 4, 6, 17], -1)]

def node6049Raw : WordRow := multiplyRow 0 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6049_check :
    collect (scaleRow 1 node6049Raw ++ scaleRow (-(-1 : ℤ)) node6049 ++
      (scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)) = [] := by
  decide +kernel

theorem node6049_mem : rowEval varIndex node6049 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6049Raw node6049 (scaleRow (-1) node2312 ++ scaleRow (-1) node1840 ++ scaleRow (-1) node1848)
    (1) (-1) (by decide) node6049_check
  · rw [node6049Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2312 node2312_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node1840 node1840_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1848 node1848_mem)))

def node6050 : WordRow := [([3, 6, 8, 17], 1), ([3, 7, 8, 16], 1)]

def node6050Raw : WordRow := multiplyRow 2 node0810

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node6050_check :
    collect (scaleRow 1 node6050Raw ++ scaleRow (-(-2 : ℤ)) node6050 ++
      (scaleRow (-1) node3414 ++ scaleRow (-1) node5999 ++ scaleRow (-1) node3423)) = [] := by
  decide +kernel

theorem node6050_mem : rowEval varIndex node6050 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node6050Raw node6050 (scaleRow (-1) node3414 ++ scaleRow (-1) node5999 ++ scaleRow (-1) node3423)
    (1) (-2) (by decide) node6050_check
  · rw [node6050Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0810_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node3414 node3414_mem) (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node5999 node5999_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node3423 node3423_mem)))

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node6050_mem
