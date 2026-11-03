import VOA.DeligneAudit.D4FusionContactM2ImagesTable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin

/-! Exact sign normalization of the actual D4 contact-color cube. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.M2Certificate
open VOA.DeligneAudit.DeligneSector.Sparse

def cubeColor : Fin 8 → Fin 9 := ![0,1,2,4,3,5,6,7]
def cubeSign : Fin 8 → ℤ := ![1,1,1,-1,-1,1,1,-1]
def cubeDirection : Fin 3 → Fin 10 := ![7,8,9]

def cubeNext : Fin 3 → Fin 8 → Option (Fin 8) :=
  ![![some 1,none,some 3,none,some 5,none,some 7,none],
    ![some 2,some 3,none,none,some 6,some 7,none,none],
    ![some 4,some 5,some 6,some 7,none,none,none,none]]

def expectedCubeCoeff (d : Fin 3) (i : Fin 8) (j : Fin 9) : ℤ :=
  match cubeNext d i with
  | none => 0
  | some k => if j=cubeColor k then cubeSign k else 0

/-- A small integer check against the already certified actual root-image table. -/
theorem signed_cube_images : ∀ d : Fin 3, ∀ i : Fin 8, ∀ j : Fin 9,
    cubeSign i * sparse (rootImages (cubeDirection d) (cubeColor i)) j =
      expectedCubeCoeff d i j := by
  decide +kernel

end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube

#print axioms VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube.signed_cube_images
