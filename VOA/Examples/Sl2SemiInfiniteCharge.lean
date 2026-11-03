/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteAction
import VOA.Examples.Sl2SemiInfiniteCurrents
import VOA.Examples.Sl2SemiInfiniteMatterGrading

/-!
# The diagonal sl2 semi-infinite BRST current and charge

For an abstract matter action `A`, `brstState A` is the actual state
`∑ a, J_matter(a) ⊗ c(a) + 1 ⊗ (1/2 ∑ a, :c(a) J_gh(a):)`.
The three `c(a)` are dual to the Chevalley basis indexing the matter currents;
there is no additional Killing-form inverse in this dual-coordinate formula.
`semiInfiniteQ A` is its zero mode for `TensorVA.tenY`, including the Koszul signs
when the matter superalgebra has odd states.

The weight and parity of the current, and their consequences for its residue,
are proved here for all levels. Defining the residue does not need finite
dimensionality of the tensor weight spaces; bundling the tensor SVA does.

The complete ghost OPE is proved in `Sl2SemiInfiniteGhostAffine`. The actual
self-product anomaly is computed in `Sl2SemiInfiniteNilpotency`, and the
square-zero charge, derivation, BRST complex and relative differential are
assembled in `Sl2SemiInfiniteComplex` for translated matter. No nilpotency or
derivation hypothesis is hidden in the definition of the charge. The additional
structure `TranslatedAffineSl2Action` requires only ordinary translation
covariance; tensor parity and finite weight-space conditions remain explicit.

OPEN: obtain operator nilpotency for every bare `AffineSl2Action` without
translation or tensor-grading hypotheses by finishing the pure mode-algebra
sum rearrangement. The state identity `semiInfiniteQ_brstState_zero` already
holds for every bare action at level `-4`.
-/

namespace VOA.Sl2SemiInfinite

open Module (End)
open scoped BigOperators TensorProduct

/-- The adjoint ghost currents have ghost number zero. -/
theorem ghostCurrent_ghost (a : Fin 3) : ghostCurrent a ∈ sl2GhostGrading 0 := by
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro c _
  apply Submodule.smul_mem
  simpa only [neg_add_cancel] using
    sl2GhostSVA_mode_ghostGrading (bGhost_ghost c) (cGhost_ghost b) (-1)

/-- The cubic ghost correction, with the conventional factor one half. -/
noncomputable def ghostBRSTState : Sl2GhostSpace :=
  (1 / 2 : ℂ) • ∑ a : Fin 3,
    mode (sl2GhostSVA.Y (cGhost a)) (-1) (ghostCurrent a)

/-- The cubic correction has conformal weight one. -/
theorem ghostBRSTState_weight : ghostBRSTState ∈ sl2GhostSVA.grading 1 := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a _
  have h := sl2GhostSVA.grading_mode (cGhost a) (cGhost_weight a)
    (ghostCurrent a) (ghostCurrent_weight a) (-1)
  norm_num at h
  exact h

/-- The cubic correction is odd. -/
theorem ghostBRSTState_odd : ghostBRSTState ∈ sl2GhostSVA.parity 1 := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a _
  simpa only [add_zero] using sl2GhostSVA.parity_mode (cGhost a) (cGhost_odd a)
    (ghostCurrent a) (ghostCurrent_even a) (-1)

/-- The cubic correction has ghost number one. -/
theorem ghostBRSTState_ghost : ghostBRSTState ∈ sl2GhostGrading 1 := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro a _
  simpa only [add_zero] using
    sl2GhostSVA_mode_ghostGrading (cGhost_ghost a) (ghostCurrent_ghost a) (-1)

universe u

variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- The BRST current state in the actual tensor carrier. -/
noncomputable def brstState (A : AffineSl2Action V k) : M ⊗[ℂ] Sl2GhostSpace :=
  (∑ a : Fin 3, A.current a ⊗ₜ[ℂ] cGhost a) + V.vacuum ⊗ₜ[ℂ] ghostBRSTState

/-- The BRST current has weight one in the tensor weight grading. -/
theorem brstState_weight (A : AffineSl2Action V k) :
    brstState A ∈ TensorVA.tenGrading V sl2GhostSVA 1 := by
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro a _
    simpa only [add_zero] using
      tmul_mem_tenGrading_add V sl2GhostSVA (A.current_weight a) (cGhost_weight a)
  · simpa only [zero_add] using
      tmul_mem_tenGrading_add V sl2GhostSVA V.vacuum_mem ghostBRSTState_weight

/-- The BRST current is odd, also for matter with nontrivial odd part. -/
theorem brstState_odd (A : AffineSl2Action V k) :
    brstState A ∈ TensorVA.tenParity V sl2GhostSVA 1 := by
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro a _
    apply TensorVA.tmul_mem_tenParity V sl2GhostSVA (A.current_even a)
    simpa only [sub_zero] using cGhost_odd a
  · apply TensorVA.tmul_mem_tenParity V sl2GhostSVA V.vacuum_parity
    simpa only [sub_zero] using ghostBRSTState_odd

/-- The complete current has ghost number one; all matter states have ghost number zero. -/
theorem brstState_ghost (A : AffineSl2Action V k) :
    brstState A ∈ matterGhostGrading M 1 := by
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro a _
    exact tmul_mem_matterGhostGrading M (A.current a) (cGhost_ghost a)
  · exact tmul_mem_matterGhostGrading M V.vacuum ghostBRSTState_ghost

/-- The diagonal semi-infinite charge, the residue of the BRST current. -/
noncomputable def semiInfiniteQ (A : AffineSl2Action V k) : End ℂ (M ⊗[ℂ] Sl2GhostSpace) :=
  mode (TensorVA.tenY V sl2GhostSVA (brstState A)) 0

/-- The residue kills the tensor vacuum at every matter level. -/
theorem semiInfiniteQ_vacuum (A : AffineSl2Action V k) :
    semiInfiniteQ A (V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = 0 := by
  change TensorVA.tenY V sl2GhostSVA (brstState A) (-1)
    (V.vacuum ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = 0
  exact (TensorVA.tenY_creation V sl2GhostSVA (brstState A)).2 (-1) (by omega)

/-- The residue preserves the conformal weight grading. -/
theorem semiInfiniteQ_weight (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (h : ℂ) (x : M ⊗[ℂ] Sl2GhostSpace)
    (hx : x ∈ TensorVA.tenGrading V sl2GhostSVA h) :
    semiInfiniteQ A x ∈ TensorVA.tenGrading V sl2GhostSVA h := by
  have ht := TensorVA.tenY_mem_tenGrading V sl2GhostSVA hV parityCompatible_sl2GhostSVA
    (brstState_weight A) (-1) x hx
  change TensorVA.tenY V sl2GhostSVA (brstState A) (-1) x ∈ _
  have he : (1 : ℂ) + h + ((-1 : ℤ) : ℂ) = h := by push_cast; ring
  rw [he] at ht
  exact ht

/-- The residue exchanges the two parity components. -/
theorem semiInfiniteQ_odd (A : AffineSl2Action V k)
    (p : ZMod 2) (x : M ⊗[ℂ] Sl2GhostSpace)
    (hx : x ∈ TensorVA.tenParity V sl2GhostSVA p) :
    semiInfiniteQ A x ∈ TensorVA.tenParity V sl2GhostSVA (p + 1) := by
  change TensorVA.tenY V sl2GhostSVA (brstState A) (-1) x ∈ _
  simpa only [add_comm] using
    TensorVA.tenY_mem_tenParity V sl2GhostSVA (brstState_odd A) (-1) x hx

/-- The residue raises total ghost number by one. -/
theorem semiInfiniteQ_ghost (A : AffineSl2Action V k)
    (g : ℤ) (x : M ⊗[ℂ] Sl2GhostSpace) (hx : x ∈ matterGhostGrading M g) :
    semiInfiniteQ A x ∈ matterGhostGrading M (g + 1) :=
  residue_mem_matterGhostGrading V (brstState_ghost A) hx

/-- A bundled matter-times-ghost SVA, with the necessary tensor grading hypotheses explicit.
For naturally supported matter, `DSMor.tensorGradingHyp_of_natSupported` discharges `hg`. -/
noncomputable def matterGhostSVA (V : SuperVertexAlgebra M)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    SuperVertexAlgebra (M ⊗[ℂ] Sl2GhostSpace) :=
  TensorVA.tensorSVA V sl2GhostSVA hV parityCompatible_sl2GhostSVA hg

/-- The charge is the zero mode in the bundled tensor super vertex algebra. -/
theorem semiInfiniteQ_eq_mode (A : AffineSl2Action V k)
    (hV : TensorVA.ParityCompatible V) (hg : TensorVA.TensorGradingHyp V sl2GhostSVA) :
    semiInfiniteQ A = mode ((matterGhostSVA V hV hg).Y (brstState A)) 0 := rfl

end VOA.Sl2SemiInfinite
