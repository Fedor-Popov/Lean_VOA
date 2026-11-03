/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteGhostProducts

/-!
# Ghost number on matter tensored with the `sl₂` ghosts

All matter states have ghost number zero, independently of their parity.  The
resulting decomposition is internal and all tensor vertex products add ghost
numbers.  In particular, the zero mode of a state of ghost number one raises the
ghost grading by one, the grading condition needed for the BRST charge.
-/

namespace VOA.Sl2SemiInfinite

open scoped TensorProduct
open Module (End)
open TensorVA

variable (A : Type*) [AddCommGroup A] [Module ℂ A]

/-- Ghost number comes entirely from the ghost tensor factor. -/
noncomputable def matterGhostGrading (n : ℤ) : Submodule ℂ (A ⊗[ℂ] Sl2GhostSpace) :=
  tenSub (⊤ : Submodule ℂ A) (sl2GhostGrading n)

/-- A pure tensor has the ghost number of its second factor. -/
theorem tmul_mem_matterGhostGrading {n : ℤ} (a : A) {b : Sl2GhostSpace}
    (hb : b ∈ sl2GhostGrading n) : a ⊗ₜ[ℂ] b ∈ matterGhostGrading A n :=
  tmul_mem_tenSub (Submodule.mem_top) hb

/-- The total ghost-number operator is zero on matter and `N_gh` on ghosts. -/
noncomputable def matterGhostNumber : End ℂ (A ⊗[ℂ] Sl2GhostSpace) :=
  DSMor.L0tot (0 : End ℂ A) sl2GhostNumber

/-- The matter–ghost pieces lie in the corresponding number eigenspaces. -/
theorem matterGhostGrading_le_eigenspace (n : ℤ) :
    matterGhostGrading A n ≤ Module.End.eigenspace (matterGhostNumber A) (n : ℂ) := by
  have hzero : (⊤ : Submodule ℂ A) ≤ Module.End.eigenspace (0 : End ℂ A) 0 := by
    intro x _
    rw [Module.End.mem_eigenspace_iff]
    simp
  simpa only [zero_add] using
    DSMor.tenSub_le_eigen (0 : End ℂ A) sl2GhostNumber 0 (n : ℂ)
      ⊤ (sl2GhostGrading n) hzero (sl2GhostGrading_le_eigenspace n)

/-- Every state is a finite sum of states of definite total ghost number. -/
theorem matterGhostGrading_iSup_eq_top : (⨆ n : ℤ, matterGhostGrading A n) = ⊤ := by
  have hG := ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    sl2GhostGrading_isInternal).2
  refine eq_top_of_tmul_mem (P := fun _ : Unit => (⊤ : Submodule ℂ A))
    (Q := sl2GhostGrading) (by simp) hG ?_
  intro _ n a _ b hb
  exact Submodule.mem_iSup_of_mem n (tmul_mem_matterGhostGrading A a hb)

/-- The matter–ghost space is internally graded by total ghost number. -/
theorem matterGhostGrading_isInternal : DirectSum.IsInternal (matterGhostGrading A) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact ((Module.End.eigenspaces_iSupIndep (matterGhostNumber A)).comp
      (f := fun n : ℤ => (n : ℂ)) Int.cast_injective).mono
      (matterGhostGrading_le_eigenspace A)
  · exact matterGhostGrading_iSup_eq_top A

variable {A}

/-- Parity signs preserve each ghost-number space. -/
theorem parityInvol_mem_sl2GhostGrading {n : ℤ} {b : Sl2GhostSpace}
    (hb : b ∈ sl2GhostGrading n) :
    (parGr sl2GhostSVA).parityInvol b ∈ sl2GhostGrading n := by
  rw [(parGr sl2GhostSVA).parityInvol_homog
    (show b ∈ (parGr sl2GhostSVA).parity (n : ZMod 2) from sl2GhostGrading_le_parity n hb)]
  exact Submodule.smul_mem _ _ hb

/-- Unsigned tensor coefficients add ghost numbers, without a parity condition on matter. -/
theorem rawCoeff_mem_matterGhostGrading (V : SuperVertexAlgebra A)
    {m n : ℤ} (a x : A) {b y : Sl2GhostSpace}
    (hb : b ∈ sl2GhostGrading m) (hy : y ∈ sl2GhostGrading n) (s : ℤ) :
    rawCoeff V sl2GhostSVA a b s (x ⊗ₜ[ℂ] y) ∈ matterGhostGrading A (m + n) := by
  rw [rawCoeff_tmul]
  refine finsum_mem_sub _ _ fun j => ?_
  exact tmul_mem_matterGhostGrading A _ (ghostAdditive_sl2GhostSVA hb hy (s - j))

/-- Tensor coefficients add ghost numbers for arbitrary, possibly odd, matter states. -/
theorem tenY_mem_matterGhostGrading (V : SuperVertexAlgebra A)
    {m n : ℤ} {u x : A ⊗[ℂ] Sl2GhostSpace}
    (hu : u ∈ matterGhostGrading A m) (hx : x ∈ matterGhostGrading A n) (s : ℤ) :
    tenY V sl2GhostSVA u s x ∈ matterGhostGrading A (m + n) := by
  refine tenSub_induction (P := ⊤) (Q := sl2GhostGrading m)
    (motive := fun w => ∀ x ∈ matterGhostGrading A n,
      tenY V sl2GhostSVA w s x ∈ matterGhostGrading A (m + n))
    ?_ ?_ ?_ ?_ hu x hx
  · intro x _
    rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb x hx
    rw [map_add]; exact Submodule.add_mem _ (ha x hx) (hb x hx)
  · intro c a ha x hx
    rw [map_smul]; exact Submodule.smul_mem _ _ (ha x hx)
  · intro a _ b hb x hx
    refine tenSub_induction (P := ⊤) (Q := sl2GhostGrading n)
      (motive := fun w => tenY V sl2GhostSVA (a ⊗ₜ[ℂ] b) s w ∈
        matterGhostGrading A (m + n)) ?_ ?_ ?_ ?_ hx
    · change tenY V sl2GhostSVA (a ⊗ₜ[ℂ] b) s 0 ∈ matterGhostGrading A (m + n)
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy
      rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x hx
      rw [map_smul]; exact Submodule.smul_mem _ _ hx
    · intro x _ y hy
      rw [tenY_tmul_apply, kappaTen_tmul, koszulOp_one, map_add, map_sub]
      refine Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
        (Submodule.sub_mem _ ?_ ?_))
      · exact rawCoeff_mem_matterGhostGrading V a x hb hy s
      · exact rawCoeff_mem_matterGhostGrading V a _ hb hy s
      · exact rawCoeff_mem_matterGhostGrading V a x (parityInvol_mem_sl2GhostGrading hb) hy s
      · exact rawCoeff_mem_matterGhostGrading V a _ (parityInvol_mem_sl2GhostGrading hb) hy s

/-- A ghost-number-one current has a residue of ghost degree one. -/
theorem residue_mem_matterGhostGrading (V : SuperVertexAlgebra A)
    {n : ℤ} {u x : A ⊗[ℂ] Sl2GhostSpace}
    (hu : u ∈ matterGhostGrading A 1) (hx : x ∈ matterGhostGrading A n) :
    mode (tenY V sl2GhostSVA u) 0 x ∈ matterGhostGrading A (n + 1) := by
  simpa only [add_comm] using tenY_mem_matterGhostGrading V hu hx (-1)

end VOA.Sl2SemiInfinite
