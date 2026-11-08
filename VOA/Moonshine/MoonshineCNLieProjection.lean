import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.LinearAlgebra.Projection
import Mathlib.Data.Complex.Basic

/-! Levi projection with abstract subalgebras, keeping subtype instances opaque to the kernel. -/

noncomputable section
namespace VOA.Moonshine.ConwayNorton

variable {g : Type*} [LieRing g] [LieAlgebra ℂ g]
variable (P L : LieSubalgebra ℂ g) (N : Submodule ℂ P)
variable (h : IsCompl (L.toSubmodule.comap P.toSubmodule.subtype) N)

def leviProjectionOfComplement : P →ₗ[ℂ] L :=
  let S := L.toSubmodule.comap P.toSubmodule.subtype
  ((P.toSubmodule.subtype.comp S.subtype).comp (S.projectionOnto N h)).codRestrict
    L.toSubmodule (fun x => (S.projectionOnto N h x).property)

theorem leviProjectionOfComplement_mem (x : P) :
    (leviProjectionOfComplement P L N h x : g) ∈ P :=
  ((L.toSubmodule.comap P.toSubmodule.subtype).projectionOnto N h x).val.property

theorem leviProjectionOfComplement_left (hLP : L ≤ P) (x : L) :
    leviProjectionOfComplement P L N h ⟨x, hLP x.property⟩ = x := by
  apply Subtype.ext
  exact congrArg (fun z : L.toSubmodule.comap P.toSubmodule.subtype => (z.val : g))
    (Submodule.projectionOnto_apply_left h
      (⟨⟨x, hLP x.property⟩, x.property⟩ : L.toSubmodule.comap P.toSubmodule.subtype))

theorem leviProjectionOfComplement_right (x : P) (hx : x ∈ N) :
    leviProjectionOfComplement P L N h x = 0 := by
  apply Subtype.ext
  exact congrArg (fun z : L.toSubmodule.comap P.toSubmodule.subtype => (z.val : g))
    (Submodule.projectionOnto_apply_of_mem_right h hx)

theorem leviProjectionOfComplement_residual (x : P) :
    (x : g) - (leviProjectionOfComplement P L N h x : g) ∈ N.map P.toSubmodule.subtype := by
  refine ⟨x - (L.toSubmodule.comap P.toSubmodule.subtype).projection N h x,
    Submodule.sub_projection_mem h x, rfl⟩

end VOA.Moonshine.ConwayNorton
