import VOA.DeligneAudit.E6FusionKernelRawTable
import VOA.DeligneAudit.DeligneSectorSparse
import VOA.DeligneAudit.E6SectorChecks
import VOA.AffineGeneral.E6Table

/-! Unchanged E6 kernel selector data for small integer checks. -/
namespace VOA.DeligneAudit.UnivG.E6K
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneCarrier.E6 (thetaH)
noncomputable section
set_option maxRecDepth 100000



def fusL : List ℕ := [46, 51, 55, 56, 59, 60, 62, 63, 64, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77]

def lowL : List ℕ := [42, 43, 44, 45, 46, 47]

def hselL : List ℕ := [4, 3, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 1, 1]

def hselK (x : Fin 78) : Fin 78 := Fin.ofNat 78 (hselL.getD (x.val - 42) 0)

def bselL : List ℕ := [6, 6, 6, 6, 40, 6, 6, 6, 6, 39, 6, 6, 6, 38, 37, 6, 6, 36, 35, 6, 34, 33, 32, 6, 31, 30, 28, 27, 26, 24, 23, 20, 19, 15, 10, 6]

def kselL : List ℤ := [1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, -1, 1, -1, 1]

def bselK (x : Fin 78) : Fin 78 := Fin.ofNat 78 (bselL.getD (x.val - 42) 6)

def kselK (x : Fin 78) : ℤ := kselL.getD (x.val - 42) 1
end
end VOA.DeligneAudit.UnivG.E6K
