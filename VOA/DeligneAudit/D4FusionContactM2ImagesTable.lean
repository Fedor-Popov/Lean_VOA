import VOA.DeligneAudit.D4FusionContactM2Sparse
import VOA.DeligneAudit.D4FusionContactTable

/-! Exact root images for the finite current derivation certificate. -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.DeligneSector.D4 (br)

def derivRoot : Fin 10 → Fin 28 := ![0,1,2,3,4,5,7,16,17,19]

def rootImages (g : Fin 10) (i : Fin 9) : SparseRow 9 :=
  [[[(0, 1)], [(1, 1)], [(2, 1)], [(3, -1)], [(4, 1)], [(5, -1)], [(6, -1)], [(7, -1)], []],
    [[(0, -2)], [(1, -1)], [(2, -1)], [(3, -1)], [], [], [], [(7, 1)], [(8, -1)]],
    [[(0, 1)], [(1, 1)], [(2, -1)], [(3, 1)], [(4, -1)], [(5, 1)], [(6, -1)], [(7, -1)], []],
    [[(0, 1)], [(1, -1)], [(2, 1)], [(3, 1)], [(4, -1)], [(5, -1)], [(6, 1)], [(7, -1)], []],
    [[], [(0, 1)], [], [], [(2, -1)], [(3, -1)], [], [(6, -1)], []],
    [[], [], [(0, 1)], [], [(1, -1)], [], [(3, -1)], [(5, -1)], []],
    [[], [], [], [(0, -1)], [], [(1, 1)], [(2, 1)], [(4, 1)], []],
    [[(1, 1)], [], [(4, -1)], [(5, -1)], [], [], [(7, -1)], [], []],
    [[(2, 1)], [(4, -1)], [], [(6, -1)], [], [(7, -1)], [], [], []],
    [[(3, -1)], [(5, 1)], [(6, 1)], [], [(7, 1)], [], [], [], []]].getD g.val [] |>.getD i.val []

private theorem root_images_0 : ∀ i j : Fin 9,
    fZ br (derivRoot 0) (radIndex i) (radIndex j) = sparse (rootImages 0 i) j := by
  decide +kernel

private theorem root_images_1 : ∀ i j : Fin 9,
    fZ br (derivRoot 1) (radIndex i) (radIndex j) = sparse (rootImages 1 i) j := by
  decide +kernel

private theorem root_images_2 : ∀ i j : Fin 9,
    fZ br (derivRoot 2) (radIndex i) (radIndex j) = sparse (rootImages 2 i) j := by
  decide +kernel

private theorem root_images_3 : ∀ i j : Fin 9,
    fZ br (derivRoot 3) (radIndex i) (radIndex j) = sparse (rootImages 3 i) j := by
  decide +kernel

private theorem root_images_4 : ∀ i j : Fin 9,
    fZ br (derivRoot 4) (radIndex i) (radIndex j) = sparse (rootImages 4 i) j := by
  decide +kernel

private theorem root_images_5 : ∀ i j : Fin 9,
    fZ br (derivRoot 5) (radIndex i) (radIndex j) = sparse (rootImages 5 i) j := by
  decide +kernel

private theorem root_images_6 : ∀ i j : Fin 9,
    fZ br (derivRoot 6) (radIndex i) (radIndex j) = sparse (rootImages 6 i) j := by
  decide +kernel

private theorem root_images_7 : ∀ i j : Fin 9,
    fZ br (derivRoot 7) (radIndex i) (radIndex j) = sparse (rootImages 7 i) j := by
  decide +kernel

private theorem root_images_8 : ∀ i j : Fin 9,
    fZ br (derivRoot 8) (radIndex i) (radIndex j) = sparse (rootImages 8 i) j := by
  decide +kernel

private theorem root_images_9 : ∀ i j : Fin 9,
    fZ br (derivRoot 9) (radIndex i) (radIndex j) = sparse (rootImages 9 i) j := by
  decide +kernel

theorem root_images_Z (g : Fin 10) (i j : Fin 9) :
    fZ br (derivRoot g) (radIndex i) (radIndex j) = sparse (rootImages g i) j := by
  fin_cases g
  · exact root_images_0 i j
  · exact root_images_1 i j
  · exact root_images_2 i j
  · exact root_images_3 i j
  · exact root_images_4 i j
  · exact root_images_5 i j
  · exact root_images_6 i j
  · exact root_images_7 i j
  · exact root_images_8 i j
  · exact root_images_9 i j

end VOA.DeligneAudit.D4FusionContact.M2Certificate

#print axioms VOA.DeligneAudit.D4FusionContact.M2Certificate.root_images_Z
