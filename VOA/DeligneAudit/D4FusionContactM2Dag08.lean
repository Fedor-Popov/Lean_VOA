import VOA.DeligneAudit.D4FusionContactM2Dag07

/-! Exact sparse membership DAG, generated from integer identities.
Each module has at most64 nodes for bounded resource use. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

open VOA.DeligneAudit.D4FusionContact.Polynomial

noncomputable section

set_option linter.style.longLine false
set_option maxRecDepth 10000

def node1536 : WordRow := [([0, 4, 5, 11], 1), ([1, 4, 4, 11], 1)]

def node1536Raw : WordRow := multiplyRow 11 node0125

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1536_check :
    collect (scaleRow 1 node1536Raw ++ scaleRow (-(1 : ℤ)) node1536 ++
      ([])) = [] := by
  decide +kernel

theorem node1536_mem : rowEval varIndex node1536 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1536Raw node1536 ([])
    (1) (1) (by decide) node1536_check
  · rw [node1536Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0125_mem
  · exact candidateIdeal.zero_mem

def node1560 : WordRow := [([0, 5, 6, 10], 1), ([1, 4, 6, 10], 1)]

def node1560Raw : WordRow := multiplyRow 10 node0127

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1560_check :
    collect (scaleRow 1 node1560Raw ++ scaleRow (-(1 : ℤ)) node1560 ++
      ([])) = [] := by
  decide +kernel

theorem node1560_mem : rowEval varIndex node1560 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1560Raw node1560 ([])
    (1) (1) (by decide) node1560_check
  · rw [node1560Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0127_mem
  · exact candidateIdeal.zero_mem

def node1567 : WordRow := [([0, 5, 6, 17], 1), ([1, 4, 6, 17], 1)]

def node1567Raw : WordRow := multiplyRow 17 node0127

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1567_check :
    collect (scaleRow 1 node1567Raw ++ scaleRow (-(1 : ℤ)) node1567 ++
      ([])) = [] := by
  decide +kernel

theorem node1567_mem : rowEval varIndex node1567 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1567Raw node1567 ([])
    (1) (1) (by decide) node1567_check
  · rw [node1567Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0127_mem
  · exact candidateIdeal.zero_mem

def node1577 : WordRow := [([0, 5, 7, 16], 1), ([1, 4, 7, 16], 1)]

def node1577Raw : WordRow := multiplyRow 16 node0128

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1577_check :
    collect (scaleRow 1 node1577Raw ++ scaleRow (-(1 : ℤ)) node1577 ++
      ([])) = [] := by
  decide +kernel

theorem node1577_mem : rowEval varIndex node1577 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1577Raw node1577 ([])
    (1) (1) (by decide) node1577_check
  · rw [node1577Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0128_mem
  · exact candidateIdeal.zero_mem

def node1581 : WordRow := [([0, 5, 8, 10], 1), ([1, 4, 8, 10], 1)]

def node1581Raw : WordRow := multiplyRow 10 node0129

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1581_check :
    collect (scaleRow 1 node1581Raw ++ scaleRow (-(1 : ℤ)) node1581 ++
      ([])) = [] := by
  decide +kernel

theorem node1581_mem : rowEval varIndex node1581 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1581Raw node1581 ([])
    (1) (1) (by decide) node1581_check
  · rw [node1581Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0129_mem
  · exact candidateIdeal.zero_mem

def node1587 : WordRow := [([0, 5, 8, 16], 1), ([1, 4, 8, 16], 1)]

def node1587Raw : WordRow := multiplyRow 16 node0129

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1587_check :
    collect (scaleRow 1 node1587Raw ++ scaleRow (-(1 : ℤ)) node1587 ++
      ([])) = [] := by
  decide +kernel

theorem node1587_mem : rowEval varIndex node1587 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1587Raw node1587 ([])
    (1) (1) (by decide) node1587_check
  · rw [node1587Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0129_mem
  · exact candidateIdeal.zero_mem

def node1598 : WordRow := [([0, 5, 10, 10], 1), ([1, 4, 10, 10], 1)]

def node1598Raw : WordRow := multiplyRow 10 node0131

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1598_check :
    collect (scaleRow 1 node1598Raw ++ scaleRow (-(1 : ℤ)) node1598 ++
      ([])) = [] := by
  decide +kernel

theorem node1598_mem : rowEval varIndex node1598 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1598Raw node1598 ([])
    (1) (1) (by decide) node1598_check
  · rw [node1598Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0131_mem
  · exact candidateIdeal.zero_mem

def node1600 : WordRow := [([0, 5, 10, 12], 1), ([1, 4, 10, 12], 1)]

def node1600Raw : WordRow := multiplyRow 12 node0131

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1600_check :
    collect (scaleRow 1 node1600Raw ++ scaleRow (-(1 : ℤ)) node1600 ++
      ([])) = [] := by
  decide +kernel

theorem node1600_mem : rowEval varIndex node1600 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1600Raw node1600 ([])
    (1) (1) (by decide) node1600_check
  · rw [node1600Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0131_mem
  · exact candidateIdeal.zero_mem

def node1602 : WordRow := [([0, 5, 10, 14], 1), ([1, 4, 10, 14], 1)]

def node1602Raw : WordRow := multiplyRow 14 node0131

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1602_check :
    collect (scaleRow 1 node1602Raw ++ scaleRow (-(1 : ℤ)) node1602 ++
      ([])) = [] := by
  decide +kernel

theorem node1602_mem : rowEval varIndex node1602 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1602Raw node1602 ([])
    (1) (1) (by decide) node1602_check
  · rw [node1602Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0131_mem
  · exact candidateIdeal.zero_mem

def node1604 : WordRow := [([0, 5, 10, 16], 1), ([1, 4, 10, 16], 1)]

def node1604Raw : WordRow := multiplyRow 16 node0131

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1604_check :
    collect (scaleRow 1 node1604Raw ++ scaleRow (-(1 : ℤ)) node1604 ++
      ([])) = [] := by
  decide +kernel

theorem node1604_mem : rowEval varIndex node1604 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1604Raw node1604 ([])
    (1) (1) (by decide) node1604_check
  · rw [node1604Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0131_mem
  · exact candidateIdeal.zero_mem

def node1605 : WordRow := [([0, 5, 10, 17], 1), ([1, 4, 10, 17], 1)]

def node1605Raw : WordRow := multiplyRow 17 node0131

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1605_check :
    collect (scaleRow 1 node1605Raw ++ scaleRow (-(1 : ℤ)) node1605 ++
      ([])) = [] := by
  decide +kernel

theorem node1605_mem : rowEval varIndex node1605 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1605Raw node1605 ([])
    (1) (1) (by decide) node1605_check
  · rw [node1605Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0131_mem
  · exact candidateIdeal.zero_mem

def node1611 : WordRow := [([0, 5, 11, 16], 1), ([1, 4, 11, 16], 1)]

def node1611Raw : WordRow := multiplyRow 16 node0132

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1611_check :
    collect (scaleRow 1 node1611Raw ++ scaleRow (-(1 : ℤ)) node1611 ++
      ([])) = [] := by
  decide +kernel

theorem node1611_mem : rowEval varIndex node1611 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1611Raw node1611 ([])
    (1) (1) (by decide) node1611_check
  · rw [node1611Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0132_mem
  · exact candidateIdeal.zero_mem

def node1617 : WordRow := [([0, 5, 12, 16], 1), ([1, 4, 12, 16], 1)]

def node1617Raw : WordRow := multiplyRow 16 node0133

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1617_check :
    collect (scaleRow 1 node1617Raw ++ scaleRow (-(1 : ℤ)) node1617 ++
      ([])) = [] := by
  decide +kernel

theorem node1617_mem : rowEval varIndex node1617 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1617Raw node1617 ([])
    (1) (1) (by decide) node1617_check
  · rw [node1617Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0133_mem
  · exact candidateIdeal.zero_mem

def node1626 : WordRow := [([0, 5, 14, 16], 1), ([1, 4, 14, 16], 1)]

def node1626Raw : WordRow := multiplyRow 16 node0135

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1626_check :
    collect (scaleRow 1 node1626Raw ++ scaleRow (-(1 : ℤ)) node1626 ++
      ([])) = [] := by
  decide +kernel

theorem node1626_mem : rowEval varIndex node1626 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1626Raw node1626 ([])
    (1) (1) (by decide) node1626_check
  · rw [node1626Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0135_mem
  · exact candidateIdeal.zero_mem

def node1632 : WordRow := [([0, 5, 16, 17], 1), ([1, 4, 16, 17], 1)]

def node1632Raw : WordRow := multiplyRow 17 node0137

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1632_check :
    collect (scaleRow 1 node1632Raw ++ scaleRow (-(1 : ℤ)) node1632 ++
      ([])) = [] := by
  decide +kernel

theorem node1632_mem : rowEval varIndex node1632 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1632Raw node1632 ([])
    (1) (1) (by decide) node1632_check
  · rw [node1632Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0137_mem
  · exact candidateIdeal.zero_mem

def node1640 : WordRow := [([1, 4, 5, 10], 1)]

def node1640Raw : WordRow := multiplyRow 10 node0139

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1640_check :
    collect (scaleRow 1 node1640Raw ++ scaleRow (-(1 : ℤ)) node1640 ++
      ([])) = [] := by
  decide +kernel

theorem node1640_mem : rowEval varIndex node1640 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1640Raw node1640 ([])
    (1) (1) (by decide) node1640_check
  · rw [node1640Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0139_mem
  · exact candidateIdeal.zero_mem

def node1686 : WordRow := [([1, 5, 8, 10], 1)]

def node1686Raw : WordRow := multiplyRow 10 node0143

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1686_check :
    collect (scaleRow 1 node1686Raw ++ scaleRow (-(1 : ℤ)) node1686 ++
      ([])) = [] := by
  decide +kernel

theorem node1686_mem : rowEval varIndex node1686 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1686Raw node1686 ([])
    (1) (1) (by decide) node1686_check
  · rw [node1686Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0143_mem
  · exact candidateIdeal.zero_mem

def node1707 : WordRow := [([1, 5, 10, 14], 1)]

def node1707Raw : WordRow := multiplyRow 14 node0145

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1707_check :
    collect (scaleRow 1 node1707Raw ++ scaleRow (-(1 : ℤ)) node1707 ++
      ([])) = [] := by
  decide +kernel

theorem node1707_mem : rowEval varIndex node1707 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1707Raw node1707 ([])
    (1) (1) (by decide) node1707_check
  · rw [node1707Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0145_mem
  · exact candidateIdeal.zero_mem

def node1729 : WordRow := [([1, 5, 14, 14], 1)]

def node1729Raw : WordRow := multiplyRow 14 node0149

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1729_check :
    collect (scaleRow 1 node1729Raw ++ scaleRow (-(1 : ℤ)) node1729 ++
      ([])) = [] := by
  decide +kernel

theorem node1729_mem : rowEval varIndex node1729 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1729Raw node1729 ([])
    (1) (1) (by decide) node1729_check
  · rw [node1729Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0149_mem
  · exact candidateIdeal.zero_mem

def node1744 : WordRow := [([0, 0, 7, 8], 1), ([0, 1, 6, 8], 1)]

def node1744Raw : WordRow := multiplyRow 8 node0153

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1744_check :
    collect (scaleRow 1 node1744Raw ++ scaleRow (-(1 : ℤ)) node1744 ++
      ([])) = [] := by
  decide +kernel

theorem node1744_mem : rowEval varIndex node1744 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1744Raw node1744 ([])
    (1) (1) (by decide) node1744_check
  · rw [node1744Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0153_mem
  · exact candidateIdeal.zero_mem

def node1756 : WordRow := [([0, 2, 4, 7], 1), ([1, 2, 4, 6], 1)]

def node1756Raw : WordRow := multiplyRow 4 node0154

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1756_check :
    collect (scaleRow 1 node1756Raw ++ scaleRow (-(1 : ℤ)) node1756 ++
      ([])) = [] := by
  decide +kernel

theorem node1756_mem : rowEval varIndex node1756 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1756Raw node1756 ([])
    (1) (1) (by decide) node1756_check
  · rw [node1756Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0154_mem
  · exact candidateIdeal.zero_mem

def node1760 : WordRow := [([0, 2, 7, 8], 1), ([1, 2, 6, 8], 1)]

def node1760Raw : WordRow := multiplyRow 8 node0154

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1760_check :
    collect (scaleRow 1 node1760Raw ++ scaleRow (-(1 : ℤ)) node1760 ++
      ([])) = [] := by
  decide +kernel

theorem node1760_mem : rowEval varIndex node1760 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1760Raw node1760 ([])
    (1) (1) (by decide) node1760_check
  · rw [node1760Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0154_mem
  · exact candidateIdeal.zero_mem

def node1769 : WordRow := [([0, 2, 7, 17], 1), ([1, 2, 6, 17], 1)]

def node1769Raw : WordRow := multiplyRow 17 node0154

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1769_check :
    collect (scaleRow 1 node1769Raw ++ scaleRow (-(1 : ℤ)) node1769 ++
      ([])) = [] := by
  decide +kernel

theorem node1769_mem : rowEval varIndex node1769 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1769Raw node1769 ([])
    (1) (1) (by decide) node1769_check
  · rw [node1769Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0154_mem
  · exact candidateIdeal.zero_mem

def node1786 : WordRow := [([0, 4, 7, 8], 1), ([1, 4, 6, 8], 1)]

def node1786Raw : WordRow := multiplyRow 8 node0156

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1786_check :
    collect (scaleRow 1 node1786Raw ++ scaleRow (-(1 : ℤ)) node1786 ++
      ([])) = [] := by
  decide +kernel

theorem node1786_mem : rowEval varIndex node1786 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1786Raw node1786 ([])
    (1) (1) (by decide) node1786_check
  · rw [node1786Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0156_mem
  · exact candidateIdeal.zero_mem

def node1787 : WordRow := [([0, 4, 7, 9], 1), ([1, 4, 6, 9], 1)]

def node1787Raw : WordRow := multiplyRow 9 node0156

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1787_check :
    collect (scaleRow 1 node1787Raw ++ scaleRow (-(1 : ℤ)) node1787 ++
      ([])) = [] := by
  decide +kernel

theorem node1787_mem : rowEval varIndex node1787 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1787Raw node1787 ([])
    (1) (1) (by decide) node1787_check
  · rw [node1787Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0156_mem
  · exact candidateIdeal.zero_mem

def node1795 : WordRow := [([0, 4, 7, 17], 1), ([1, 4, 6, 17], 1)]

def node1795Raw : WordRow := multiplyRow 17 node0156

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1795_check :
    collect (scaleRow 1 node1795Raw ++ scaleRow (-(1 : ℤ)) node1795 ++
      ([])) = [] := by
  decide +kernel

theorem node1795_mem : rowEval varIndex node1795 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1795Raw node1795 ([])
    (1) (1) (by decide) node1795_check
  · rw [node1795Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0156_mem
  · exact candidateIdeal.zero_mem

def node1798 : WordRow := [([1, 4, 7, 8], 1), ([1, 5, 6, 8], -1)]

def node1798Raw : WordRow := multiplyRow 8 node0157

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1798_check :
    collect (scaleRow 1 node1798Raw ++ scaleRow (-(1 : ℤ)) node1798 ++
      ([])) = [] := by
  decide +kernel

theorem node1798_mem : rowEval varIndex node1798 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1798Raw node1798 ([])
    (1) (1) (by decide) node1798_check
  · rw [node1798Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0157_mem
  · exact candidateIdeal.zero_mem

def node1810 : WordRow := [([0, 6, 7, 8], 1), ([1, 6, 6, 8], 1)]

def node1810Raw : WordRow := multiplyRow 8 node0158

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1810_check :
    collect (scaleRow 1 node1810Raw ++ scaleRow (-(1 : ℤ)) node1810 ++
      ([])) = [] := by
  decide +kernel

theorem node1810_mem : rowEval varIndex node1810 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1810Raw node1810 ([])
    (1) (1) (by decide) node1810_check
  · rw [node1810Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0158_mem
  · exact candidateIdeal.zero_mem

def node1811 : WordRow := [([0, 6, 7, 9], 1), ([1, 6, 6, 9], 1)]

def node1811Raw : WordRow := multiplyRow 9 node0158

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1811_check :
    collect (scaleRow 1 node1811Raw ++ scaleRow (-(1 : ℤ)) node1811 ++
      ([])) = [] := by
  decide +kernel

theorem node1811_mem : rowEval varIndex node1811 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1811Raw node1811 ([])
    (1) (1) (by decide) node1811_check
  · rw [node1811Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0158_mem
  · exact candidateIdeal.zero_mem

def node1831 : WordRow := [([0, 7, 8, 8], 1), ([1, 6, 8, 8], 1)]

def node1831Raw : WordRow := multiplyRow 8 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1831_check :
    collect (scaleRow 1 node1831Raw ++ scaleRow (-(1 : ℤ)) node1831 ++
      ([])) = [] := by
  decide +kernel

theorem node1831_mem : rowEval varIndex node1831 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1831Raw node1831 ([])
    (1) (1) (by decide) node1831_check
  · rw [node1831Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1833 : WordRow := [([0, 7, 8, 10], 1), ([1, 6, 8, 10], 1)]

def node1833Raw : WordRow := multiplyRow 10 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1833_check :
    collect (scaleRow 1 node1833Raw ++ scaleRow (-(1 : ℤ)) node1833 ++
      ([])) = [] := by
  decide +kernel

theorem node1833_mem : rowEval varIndex node1833 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1833Raw node1833 ([])
    (1) (1) (by decide) node1833_check
  · rw [node1833Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1835 : WordRow := [([0, 7, 8, 12], 1), ([1, 6, 8, 12], 1)]

def node1835Raw : WordRow := multiplyRow 12 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1835_check :
    collect (scaleRow 1 node1835Raw ++ scaleRow (-(1 : ℤ)) node1835 ++
      ([])) = [] := by
  decide +kernel

theorem node1835_mem : rowEval varIndex node1835 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1835Raw node1835 ([])
    (1) (1) (by decide) node1835_check
  · rw [node1835Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1837 : WordRow := [([0, 7, 8, 14], 1), ([1, 6, 8, 14], 1)]

def node1837Raw : WordRow := multiplyRow 14 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1837_check :
    collect (scaleRow 1 node1837Raw ++ scaleRow (-(1 : ℤ)) node1837 ++
      ([])) = [] := by
  decide +kernel

theorem node1837_mem : rowEval varIndex node1837 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1837Raw node1837 ([])
    (1) (1) (by decide) node1837_check
  · rw [node1837Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1839 : WordRow := [([0, 7, 8, 16], 1), ([1, 6, 8, 16], 1)]

def node1839Raw : WordRow := multiplyRow 16 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1839_check :
    collect (scaleRow 1 node1839Raw ++ scaleRow (-(1 : ℤ)) node1839 ++
      ([])) = [] := by
  decide +kernel

theorem node1839_mem : rowEval varIndex node1839 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1839Raw node1839 ([])
    (1) (1) (by decide) node1839_check
  · rw [node1839Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1840 : WordRow := [([0, 7, 8, 17], 1), ([1, 6, 8, 17], 1)]

def node1840Raw : WordRow := multiplyRow 17 node0160

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1840_check :
    collect (scaleRow 1 node1840Raw ++ scaleRow (-(1 : ℤ)) node1840 ++
      ([])) = [] := by
  decide +kernel

theorem node1840_mem : rowEval varIndex node1840 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1840Raw node1840 ([])
    (1) (1) (by decide) node1840_check
  · rw [node1840Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0160_mem
  · exact candidateIdeal.zero_mem

def node1848 : WordRow := [([0, 7, 9, 16], 1), ([1, 6, 9, 16], 1)]

def node1848Raw : WordRow := multiplyRow 16 node0161

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1848_check :
    collect (scaleRow 1 node1848Raw ++ scaleRow (-(1 : ℤ)) node1848 ++
      ([])) = [] := by
  decide +kernel

theorem node1848_mem : rowEval varIndex node1848 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1848Raw node1848 ([])
    (1) (1) (by decide) node1848_check
  · rw [node1848Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0161_mem
  · exact candidateIdeal.zero_mem

def node1856 : WordRow := [([0, 7, 10, 16], 1), ([1, 6, 10, 16], 1)]

def node1856Raw : WordRow := multiplyRow 16 node0162

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1856_check :
    collect (scaleRow 1 node1856Raw ++ scaleRow (-(1 : ℤ)) node1856 ++
      ([])) = [] := by
  decide +kernel

theorem node1856_mem : rowEval varIndex node1856 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1856Raw node1856 ([])
    (1) (1) (by decide) node1856_check
  · rw [node1856Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0162_mem
  · exact candidateIdeal.zero_mem

def node1869 : WordRow := [([0, 7, 12, 16], 1), ([1, 6, 12, 16], 1)]

def node1869Raw : WordRow := multiplyRow 16 node0164

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1869_check :
    collect (scaleRow 1 node1869Raw ++ scaleRow (-(1 : ℤ)) node1869 ++
      ([])) = [] := by
  decide +kernel

theorem node1869_mem : rowEval varIndex node1869 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1869Raw node1869 ([])
    (1) (1) (by decide) node1869_check
  · rw [node1869Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0164_mem
  · exact candidateIdeal.zero_mem

def node1878 : WordRow := [([0, 7, 14, 16], 1), ([1, 6, 14, 16], 1)]

def node1878Raw : WordRow := multiplyRow 16 node0166

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1878_check :
    collect (scaleRow 1 node1878Raw ++ scaleRow (-(1 : ℤ)) node1878 ++
      ([])) = [] := by
  decide +kernel

theorem node1878_mem : rowEval varIndex node1878 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1878Raw node1878 ([])
    (1) (1) (by decide) node1878_check
  · rw [node1878Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0166_mem
  · exact candidateIdeal.zero_mem

def node1884 : WordRow := [([0, 7, 16, 17], 1), ([1, 6, 16, 17], 1)]

def node1884Raw : WordRow := multiplyRow 17 node0168

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1884_check :
    collect (scaleRow 1 node1884Raw ++ scaleRow (-(1 : ℤ)) node1884 ++
      ([])) = [] := by
  decide +kernel

theorem node1884_mem : rowEval varIndex node1884 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1884Raw node1884 ([])
    (1) (1) (by decide) node1884_check
  · rw [node1884Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0168_mem
  · exact candidateIdeal.zero_mem

def node1888 : WordRow := [([1, 6, 7, 8], 1)]

def node1888Raw : WordRow := multiplyRow 8 node0170

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1888_check :
    collect (scaleRow 1 node1888Raw ++ scaleRow (-(1 : ℤ)) node1888 ++
      ([])) = [] := by
  decide +kernel

theorem node1888_mem : rowEval varIndex node1888 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1888Raw node1888 ([])
    (1) (1) (by decide) node1888_check
  · rw [node1888Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0170_mem
  · exact candidateIdeal.zero_mem

def node1911 : WordRow := [([1, 7, 8, 10], 1)]

def node1911Raw : WordRow := multiplyRow 10 node0172

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1911_check :
    collect (scaleRow 1 node1911Raw ++ scaleRow (-(1 : ℤ)) node1911 ++
      ([])) = [] := by
  decide +kernel

theorem node1911_mem : rowEval varIndex node1911 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1911Raw node1911 ([])
    (1) (1) (by decide) node1911_check
  · rw [node1911Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0172_mem
  · exact candidateIdeal.zero_mem

def node1913 : WordRow := [([1, 7, 8, 12], 1)]

def node1913Raw : WordRow := multiplyRow 12 node0172

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1913_check :
    collect (scaleRow 1 node1913Raw ++ scaleRow (-(1 : ℤ)) node1913 ++
      ([])) = [] := by
  decide +kernel

theorem node1913_mem : rowEval varIndex node1913 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1913Raw node1913 ([])
    (1) (1) (by decide) node1913_check
  · rw [node1913Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0172_mem
  · exact candidateIdeal.zero_mem

def node1915 : WordRow := [([1, 7, 8, 14], 1)]

def node1915Raw : WordRow := multiplyRow 14 node0172

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1915_check :
    collect (scaleRow 1 node1915Raw ++ scaleRow (-(1 : ℤ)) node1915 ++
      ([])) = [] := by
  decide +kernel

theorem node1915_mem : rowEval varIndex node1915 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1915Raw node1915 ([])
    (1) (1) (by decide) node1915_check
  · rw [node1915Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0172_mem
  · exact candidateIdeal.zero_mem

def node1971 : WordRow := [([1, 2, 2, 12], 1)]

def node1971Raw : WordRow := multiplyRow 12 node0182

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node1971_check :
    collect (scaleRow 1 node1971Raw ++ scaleRow (-(1 : ℤ)) node1971 ++
      ([])) = [] := by
  decide +kernel

theorem node1971_mem : rowEval varIndex node1971 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node1971Raw node1971 ([])
    (1) (1) (by decide) node1971_check
  · rw [node1971Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0182_mem
  · exact candidateIdeal.zero_mem

def node2016 : WordRow := [([2, 3, 4, 12], 1)]

def node2016Raw : WordRow := multiplyRow 12 node0185

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2016_check :
    collect (scaleRow 1 node2016Raw ++ scaleRow (-(1 : ℤ)) node2016 ++
      ([])) = [] := by
  decide +kernel

theorem node2016_mem : rowEval varIndex node2016 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2016Raw node2016 ([])
    (1) (1) (by decide) node2016_check
  · rw [node2016Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0185_mem
  · exact candidateIdeal.zero_mem

def node2041 : WordRow := [([2, 3, 6, 12], 1)]

def node2041Raw : WordRow := multiplyRow 12 node0187

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2041_check :
    collect (scaleRow 1 node2041Raw ++ scaleRow (-(1 : ℤ)) node2041 ++
      ([])) = [] := by
  decide +kernel

theorem node2041_mem : rowEval varIndex node2041 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2041Raw node2041 ([])
    (1) (1) (by decide) node2041_check
  · rw [node2041Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0187_mem
  · exact candidateIdeal.zero_mem

def node2092 : WordRow := [([2, 3, 12, 12], 1)]

def node2092Raw : WordRow := multiplyRow 12 node0193

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2092_check :
    collect (scaleRow 1 node2092Raw ++ scaleRow (-(1 : ℤ)) node2092 ++
      ([])) = [] := by
  decide +kernel

theorem node2092_mem : rowEval varIndex node2092 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2092Raw node2092 ([])
    (1) (1) (by decide) node2092_check
  · rw [node2092Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0193_mem
  · exact candidateIdeal.zero_mem

def node2094 : WordRow := [([2, 3, 12, 14], 1)]

def node2094Raw : WordRow := multiplyRow 14 node0193

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2094_check :
    collect (scaleRow 1 node2094Raw ++ scaleRow (-(1 : ℤ)) node2094 ++
      ([])) = [] := by
  decide +kernel

theorem node2094_mem : rowEval varIndex node2094 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2094Raw node2094 ([])
    (1) (1) (by decide) node2094_check
  · rw [node2094Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0193_mem
  · exact candidateIdeal.zero_mem

def node2096 : WordRow := [([2, 3, 12, 16], 1)]

def node2096Raw : WordRow := multiplyRow 16 node0193

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2096_check :
    collect (scaleRow 1 node2096Raw ++ scaleRow (-(1 : ℤ)) node2096 ++
      ([])) = [] := by
  decide +kernel

theorem node2096_mem : rowEval varIndex node2096 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2096Raw node2096 ([])
    (1) (1) (by decide) node2096_check
  · rw [node2096Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0193_mem
  · exact candidateIdeal.zero_mem

def node2105 : WordRow := [([2, 3, 14, 16], 1)]

def node2105Raw : WordRow := multiplyRow 16 node0195

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2105_check :
    collect (scaleRow 1 node2105Raw ++ scaleRow (-(1 : ℤ)) node2105 ++
      ([])) = [] := by
  decide +kernel

theorem node2105_mem : rowEval varIndex node2105 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2105Raw node2105 ([])
    (1) (1) (by decide) node2105_check
  · rw [node2105Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0195_mem
  · exact candidateIdeal.zero_mem

def node2236 : WordRow := [([0, 0, 6, 9], 1), ([0, 1, 6, 8], 1), ([0, 2, 5, 6], -1), ([0, 3, 4, 6], -1)]

def node2236Raw : WordRow := multiplyRow 6 node0214

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2236_check :
    collect (scaleRow 1 node2236Raw ++ scaleRow (-(1 : ℤ)) node2236 ++
      ([])) = [] := by
  decide +kernel

theorem node2236_mem : rowEval varIndex node2236 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2236Raw node2236 ([])
    (1) (1) (by decide) node2236_check
  · rw [node2236Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0214_mem
  · exact candidateIdeal.zero_mem

def node2245 : WordRow := [([0, 0, 9, 16], 1), ([0, 1, 8, 16], 1), ([0, 2, 5, 16], -1), ([0, 3, 4, 16], -1)]

def node2245Raw : WordRow := multiplyRow 16 node0214

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2245_check :
    collect (scaleRow 1 node2245Raw ++ scaleRow (-(1 : ℤ)) node2245 ++
      ([])) = [] := by
  decide +kernel

theorem node2245_mem : rowEval varIndex node2245 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2245Raw node2245 ([])
    (1) (1) (by decide) node2245_check
  · rw [node2245Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0214_mem
  · exact candidateIdeal.zero_mem

def node2250 : WordRow := [([0, 2, 6, 9], 1), ([1, 2, 6, 8], 1), ([2, 2, 5, 6], -1), ([2, 3, 4, 6], -1)]

def node2250Raw : WordRow := multiplyRow 6 node0215

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2250_check :
    collect (scaleRow 1 node2250Raw ++ scaleRow (-(1 : ℤ)) node2250 ++
      ([])) = [] := by
  decide +kernel

theorem node2250_mem : rowEval varIndex node2250 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2250Raw node2250 ([])
    (1) (1) (by decide) node2250_check
  · rw [node2250Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0215_mem
  · exact candidateIdeal.zero_mem

def node2260 : WordRow := [([0, 2, 9, 16], 1), ([1, 2, 8, 16], 1), ([2, 2, 5, 16], -1), ([2, 3, 4, 16], -1)]

def node2260Raw : WordRow := multiplyRow 16 node0215

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2260_check :
    collect (scaleRow 1 node2260Raw ++ scaleRow (-(1 : ℤ)) node2260 ++
      ([])) = [] := by
  decide +kernel

theorem node2260_mem : rowEval varIndex node2260 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2260Raw node2260 ([])
    (1) (1) (by decide) node2260_check
  · rw [node2260Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0215_mem
  · exact candidateIdeal.zero_mem

def node2276 : WordRow := [([0, 4, 6, 9], 1), ([1, 4, 6, 8], 1), ([2, 4, 5, 6], -1), ([3, 4, 4, 6], -1)]

def node2276Raw : WordRow := multiplyRow 6 node0217

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2276_check :
    collect (scaleRow 1 node2276Raw ++ scaleRow (-(1 : ℤ)) node2276 ++
      ([])) = [] := by
  decide +kernel

theorem node2276_mem : rowEval varIndex node2276 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2276Raw node2276 ([])
    (1) (1) (by decide) node2276_check
  · rw [node2276Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0217_mem
  · exact candidateIdeal.zero_mem

def node2277 : WordRow := [([1, 4, 6, 9], 1), ([1, 4, 7, 8], -1), ([2, 4, 5, 7], 1), ([3, 4, 4, 7], 1)]

def node2277Raw : WordRow := multiplyRow 7 node0217

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2277_check :
    collect (scaleRow 1 node2277Raw ++ scaleRow (-(-1 : ℤ)) node2277 ++
      (scaleRow (-1) node1787)) = [] := by
  decide +kernel

theorem node2277_mem : rowEval varIndex node2277 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2277Raw node2277 (scaleRow (-1) node1787)
    (1) (-1) (by decide) node2277_check
  · rw [node2277Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0217_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node1787 node1787_mem)

def node2281 : WordRow := [([0, 4, 9, 11], 1), ([1, 4, 8, 11], 1), ([2, 4, 5, 11], -1), ([3, 4, 4, 11], -1)]

def node2281Raw : WordRow := multiplyRow 11 node0217

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2281_check :
    collect (scaleRow 1 node2281Raw ++ scaleRow (-(1 : ℤ)) node2281 ++
      ([])) = [] := by
  decide +kernel

theorem node2281_mem : rowEval varIndex node2281 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2281Raw node2281 ([])
    (1) (1) (by decide) node2281_check
  · rw [node2281Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0217_mem
  · exact candidateIdeal.zero_mem

def node2286 : WordRow := [([0, 4, 9, 16], 1), ([1, 4, 8, 16], 1), ([2, 4, 5, 16], -1), ([3, 4, 4, 16], -1)]

def node2286Raw : WordRow := multiplyRow 16 node0217

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2286_check :
    collect (scaleRow 1 node2286Raw ++ scaleRow (-(1 : ℤ)) node2286 ++
      ([])) = [] := by
  decide +kernel

theorem node2286_mem : rowEval varIndex node2286 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2286Raw node2286 ([])
    (1) (1) (by decide) node2286_check
  · rw [node2286Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0217_mem
  · exact candidateIdeal.zero_mem

def node2289 : WordRow := [([2, 4, 5, 7], 1), ([2, 5, 5, 6], -1), ([3, 4, 4, 7], 1), ([3, 4, 5, 6], -1)]

def node2289Raw : WordRow := multiplyRow 6 node0218

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2289_check :
    collect (scaleRow 1 node2289Raw ++ scaleRow (-(-1 : ℤ)) node2289 ++
      (scaleRow (-1) node2277 ++ scaleRow (-1) node1798)) = [] := by
  decide +kernel

theorem node2289_mem : rowEval varIndex node2289 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2289Raw node2289 (scaleRow (-1) node2277 ++ scaleRow (-1) node1798)
    (1) (-1) (by decide) node2289_check
  · rw [node2289Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0218_mem
  · simpa only [rowEval_append,add_assoc] using (candidateIdeal.add_mem (rowEval_scale_mem varIndex candidateIdeal (-1) node2277 node2277_mem) (rowEval_scale_mem varIndex candidateIdeal (-1) node1798 node1798_mem))

def node2293 : WordRow := [([1, 4, 9, 10], 1), ([1, 5, 8, 10], -1), ([2, 5, 5, 10], 1), ([3, 4, 5, 10], 1)]

def node2293Raw : WordRow := multiplyRow 10 node0218

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2293_check :
    collect (scaleRow 1 node2293Raw ++ scaleRow (-(1 : ℤ)) node2293 ++
      ([])) = [] := by
  decide +kernel

theorem node2293_mem : rowEval varIndex node2293 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2293Raw node2293 ([])
    (1) (1) (by decide) node2293_check
  · rw [node2293Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0218_mem
  · exact candidateIdeal.zero_mem

def node2301 : WordRow := [([0, 6, 6, 9], 1), ([1, 6, 6, 8], 1), ([2, 5, 6, 6], -1), ([3, 4, 6, 6], -1)]

def node2301Raw : WordRow := multiplyRow 6 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2301_check :
    collect (scaleRow 1 node2301Raw ++ scaleRow (-(1 : ℤ)) node2301 ++
      ([])) = [] := by
  decide +kernel

theorem node2301_mem : rowEval varIndex node2301 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2301Raw node2301 ([])
    (1) (1) (by decide) node2301_check
  · rw [node2301Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

def node2302 : WordRow := [([1, 6, 6, 9], 1), ([1, 6, 7, 8], -1), ([2, 5, 6, 7], 1), ([3, 4, 6, 7], 1)]

def node2302Raw : WordRow := multiplyRow 7 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2302_check :
    collect (scaleRow 1 node2302Raw ++ scaleRow (-(-1 : ℤ)) node2302 ++
      (scaleRow (-1) node1811)) = [] := by
  decide +kernel

theorem node2302_mem : rowEval varIndex node2302 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2302Raw node2302 (scaleRow (-1) node1811)
    (1) (-1) (by decide) node2302_check
  · rw [node2302Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · simpa only [rowEval_append,add_assoc] using (rowEval_scale_mem varIndex candidateIdeal (-1) node1811 node1811_mem)

def node2303 : WordRow := [([0, 6, 8, 9], 1), ([1, 6, 8, 8], 1), ([2, 5, 6, 8], -1), ([3, 4, 6, 8], -1)]

def node2303Raw : WordRow := multiplyRow 8 node0219

set_option maxHeartbeats 2000000 in
-- Sparse cancellation may expand up to nineteen earlier integer rows.
theorem node2303_check :
    collect (scaleRow 1 node2303Raw ++ scaleRow (-(1 : ℤ)) node2303 ++
      ([])) = [] := by
  decide +kernel

theorem node2303_mem : rowEval varIndex node2303 ∈ candidateIdeal := by
  apply row_mem_of_collect varIndex candidateIdeal node2303Raw node2303 ([])
    (1) (1) (by decide) node2303_check
  · rw [node2303Raw,rowEval_multiply]
    exact Ideal.mul_mem_right _ _ node0219_mem
  · exact candidateIdeal.zero_mem

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.Dag.node2303_mem
