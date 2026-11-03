/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import VOA.Huang.HuangRigidOrdinary
import VOA.Huang.HexagonCloseResidual

/-!
# Two-sided rigidity of the category of ordinary modules of a nice VOA

`HuangRigid.rightRigid_ordinary` gives right duals for `Ordinary W` with the proved monoidal
structure `monoidalCategoryOfStronglyRational_pbw F hNice.1`. That monoidal category carries the
proved braiding `HexagonClose.braidedCategory_stronglyRational_pbw F hNice.1`, and in a braided
category a right dual is also a left dual (precompose evaluation / postcompose coevaluation with
the braiding: Mathlib's `CategoryTheory.BraidedCategory.rigidCategoryOfRightRigidCategory`).
Hence Mathlib's two-sided `RigidCategory`.

* `rigid_ordinary` — `Nonempty (RigidCategory (Ordinary W))` for nice `W`.
* `rigidCategoryOrdinary` — a chosen such structure (noncomputable).
-/

noncomputable section

namespace VOA.Huang.HuangRigid

open VOA VOA.Classification.COne VOA.Huang.TensorCat CategoryTheory

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Huang's rigidity theorem, two-sided**: for a nice VOA `W`
(`Nice W := StronglyRational W ∧ PseudoUnitary W`) and any fusion choice `F`, the proved monoidal
category of ordinary modules `monoidalCategoryOfStronglyRational_pbw F hNice.1` is rigid in
Mathlib's sense (`RigidCategory`: every object has a left and a right dual). Right duals come from
`rightRigid_ordinary`; left duals from them via the proved braiding
`braidedCategory_stronglyRational_pbw`
(Mathlib `BraidedCategory.rigidCategoryOfRightRigidCategory`). -/
theorem rigid_ordinary (F : FusionChoice W) (hNice : Nice W) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    Nonempty (RigidCategory (Ordinary W)) := by
  letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
  letI := HexagonClose.braidedCategory_stronglyRational_pbw F hNice.1
  obtain ⟨r⟩ := rightRigid_ordinary F hNice
  letI : RightRigidCategory (Ordinary W) := r
  exact ⟨BraidedCategory.rigidCategoryOfRightRigidCategory (C := Ordinary W)⟩

/-- A chosen two-sided rigid structure on the ordinary modules of a nice VOA
(`Classical.choice` of `rigid_ordinary`). -/
@[implicit_reducible]
def rigidCategoryOrdinary (F : FusionChoice W) (hNice : Nice W) :
    letI := monoidalCategoryOfStronglyRational_pbw F hNice.1
    RigidCategory (Ordinary W) :=
  Classical.choice (rigid_ordinary F hNice)

end VOA.Huang.HuangRigid
