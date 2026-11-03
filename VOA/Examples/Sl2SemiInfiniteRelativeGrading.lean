/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteRelative

/-! # The internal ghost grading of relative states

Both sets of kernel conditions are homogeneous: total currents preserve ghost
number and antighost zero modes lower it by one. Thus the relative carrier
inherits a genuine internal direct-sum grading, without a nilpotency input.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

theorem totalCurrentState_ghost (A : AffineSl2Action V k) (a : Fin 3) :
    totalCurrentState A a ∈ matterGhostGrading M 0 :=
  Submodule.add_mem _
    (tmul_mem_matterGhostGrading M (A.current a) sl2GhostSVA_vacuum_ghost)
    (tmul_mem_matterGhostGrading M V.vacuum (ghostCurrent_ghost a))

theorem tensorAntighost_ghost (a : Fin 3) :
    tensorAntighost V a ∈ matterGhostGrading M (-1) :=
  tmul_mem_matterGhostGrading M V.vacuum (bGhost_ghost a)

/-- The total current zero modes preserve ghost number. -/
theorem totalCurrentZero_ghost (A : AffineSl2Action V k) (a : Fin 3) {g : ℤ}
    {x : M ⊗[ℂ] Sl2GhostSpace} (hx : x ∈ matterGhostGrading M g) :
    totalCurrentZero A a x ∈ matterGhostGrading M g := by
  simpa only [zero_add] using
    tenY_mem_matterGhostGrading V (totalCurrentState_ghost A a) hx (-1)

/-- The antighost zero modes lower ghost number by one. -/
theorem antighostZero_ghost (a : Fin 3) {g : ℤ}
    {x : M ⊗[ℂ] Sl2GhostSpace} (hx : x ∈ matterGhostGrading M g) :
    antighostZero V a x ∈ matterGhostGrading M (g - 1) := by
  have h := tenY_mem_matterGhostGrading V (tensorAntighost_ghost (V := V) a) hx (-1)
  simpa only [sub_eq_add_neg, add_comm] using h

/-- The ghost-degree component inside the relative carrier. -/
noncomputable def relativeGhostGrading (A : AffineSl2Action V k) (g : ℤ) :
    Submodule ℂ (relativeCarrier A) :=
  (matterGhostGrading M g).comap (relativeCarrier A).subtype

/-- Relative ghost number is an internal grading, not merely a filtration. -/
theorem relativeGhostGrading_isInternal (A : AffineSl2Action V k) :
    DirectSum.IsInternal (relativeGhostGrading A) := by
  haveI : DirectSum.Decomposition (matterGhostGrading M) :=
    (matterGhostGrading_isInternal M).chooseDecomposition _
  apply isInternal_comap (matterGhostGrading M) (relativeCarrier A)
  intro g x hx
  rw [mem_relativeCarrier] at hx ⊢
  constructor
  · intro a
    exact BRST.homogProj_mem_ker (matterGhostGrading M)
      (f := totalCurrentZero A a) (e := Equiv.refl ℤ)
      (fun _ _ hy => totalCurrentZero_ghost A a hy) g (hx.1 a)
  · intro a
    let e : ℤ ≃ ℤ :=
      { toFun := fun g => g - 1
        invFun := fun g => g + 1
        left_inv := by intro g; dsimp; omega
        right_inv := by intro g; dsimp; omega }
    exact BRST.homogProj_mem_ker (matterGhostGrading M)
      (f := antighostZero V a) (e := e)
      (fun _ _ hy => antighostZero_ghost a hy) g (hx.2 a)

end VOA.Sl2SemiInfinite
