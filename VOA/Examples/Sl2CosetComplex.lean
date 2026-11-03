/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetSubspace
import VOA.Examples.Sl2SemiInfiniteComplex
import VOA.Examples.Sl2SemiInfiniteModes

/-!
# Coset representatives in the semi-infinite complex

Tensoring a current-commutant state with the ghost vacuum gives an actual
relative, closed state, of ghost degree zero. The resulting map preserves
vacuum and every vertex mode, both before and after passage to cohomology.
No simplicity or non-exactness hypothesis is needed for this construction.
-/

namespace VOA.Sl2Coset

open Sl2SemiInfinite
open scoped TensorProduct

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}

/-- Adjoin the three-pair ghost vacuum. -/
noncomputable def ghostVacuumEmbedding (V : SuperVertexAlgebra M) :
    M →ₗ[ℂ] M ⊗[ℂ] Sl2GhostSpace :=
  (TensorProduct.mk ℂ M Sl2GhostSpace).flip sl2GhostSVA.vacuum

@[simp] theorem ghostVacuumEmbedding_apply (x : M) :
    ghostVacuumEmbedding V x = x ⊗ₜ[ℂ] sl2GhostSVA.vacuum := rfl

/-- Adjoining a vacuum preserves every mode, including negative modes. -/
theorem ghostVacuumEmbedding_mode (x y : M) (n : ℤ) :
    ghostVacuumEmbedding V (mode (V.Y x) n y) =
      mode (TensorVA.tenY V sl2GhostSVA (ghostVacuumEmbedding V x)) n
        (ghostVacuumEmbedding V y) :=
  (tenY_left_unit V sl2GhostSVA x y sl2GhostSVA.vacuum (-n - 1)).symm

/-- A commutant state with the ghost vacuum satisfies all relative conditions. -/
theorem ghostVacuumEmbedding_mem_relativeCarrier (A : AffineSl2Action V k)
    {x : M} (hx : x ∈ cosetSubspace A) :
    ghostVacuumEmbedding V x ∈ relativeCarrier A := by
  rw [mem_relativeCarrier]
  constructor
  · intro a
    rw [ghostVacuumEmbedding_apply, totalCurrentZero_tmul,
      (mem_cosetSubspace A x).mp hx a 0 (le_refl 0)]
    have hg : mode (ghostCurrentField a) 0 sl2GhostSVA.vacuum = 0 :=
      sl2GhostSVA.smul_vacuum_eq_zero (ghostCurrent a) (le_refl 0)
    rw [hg, TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero]
  · intro a
    change antighostZero V a (x ⊗ₜ[ℂ] sl2GhostSVA.vacuum) = 0
    have hb : mode (sl2GhostSVA.Y (bGhost a)) 0 sl2GhostSVA.vacuum = 0 :=
      sl2GhostSVA.smul_vacuum_eq_zero (bGhost a) (le_refl 0)
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := (TensorVA.parGr V).exists_parity_decomp x
    rw [TensorProduct.add_tmul, map_add, antighostZero_tmul a hx₀,
      antighostZero_tmul a hx₁, hb, TensorProduct.tmul_zero,
      TensorProduct.tmul_zero, smul_zero, smul_zero, add_zero]

/-- The full, actual BRST residue kills the displayed coset representative. -/
theorem semiInfiniteQ_ghostVacuumEmbedding (A : AffineSl2Action V k)
    {x : M} (hx : x ∈ cosetSubspace A) :
    semiInfiniteQ A (ghostVacuumEmbedding V x) = 0 := by
  rw [ghostVacuumEmbedding_apply, semiInfiniteQ_tmul]
  have hp := parityInvol_mem_cosetSubspace A hx
  have hg : mode (sl2GhostSVA.Y ghostBRSTState) 0 sl2GhostSVA.vacuum = 0 :=
    sl2GhostSVA.smul_vacuum_eq_zero ghostBRSTState (le_refl 0)
  rw [hg, TensorProduct.tmul_zero, add_zero]
  apply Finset.sum_eq_zero
  intro a _
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : 0 ≤ n
  · rw [(mem_cosetSubspace A _).mp hp a n hn, TensorProduct.zero_tmul]
  · have hc : mode (sl2GhostSVA.Y (cGhost a)) (-n - 1) sl2GhostSVA.vacuum = 0 :=
      sl2GhostSVA.smul_vacuum_eq_zero (cGhost a) (by omega)
    rw [hc, TensorProduct.tmul_zero]

/-- The linear map on the genuine commutant carrier. -/
noncomputable def cosetToComplex (A : AffineSl2Action V k) :
    cosetSubspace A →ₗ[ℂ] M ⊗[ℂ] Sl2GhostSpace :=
  (ghostVacuumEmbedding V).comp (cosetSubspace A).subtype

@[simp] theorem cosetToComplex_apply (A : AffineSl2Action V k)
    (x : cosetSubspace A) : cosetToComplex A x = (x : M) ⊗ₜ[ℂ] sl2GhostSVA.vacuum := rfl

theorem cosetToComplex_relative (A : AffineSl2Action V k) (x : cosetSubspace A) :
    cosetToComplex A x ∈ relativeCarrier A :=
  ghostVacuumEmbedding_mem_relativeCarrier A x.property

theorem cosetToComplex_closed (A : AffineSl2Action V k) (x : cosetSubspace A) :
    semiInfiniteQ A (cosetToComplex A x) = 0 :=
  semiInfiniteQ_ghostVacuumEmbedding A x.property

theorem cosetToComplex_ghost (A : AffineSl2Action V k) (x : cosetSubspace A) :
    cosetToComplex A x ∈ matterGhostGrading M 0 :=
  tmul_mem_matterGhostGrading M x sl2GhostSVA_vacuum_ghost

variable (A : TranslatedAffineSl2Action V (-4))
variable (hV : TensorVA.ParityCompatible V)
variable (hg : TensorVA.TensorGradingHyp V sl2GhostSVA)

/-- The closed representative, before quotienting by boundaries. -/
noncomputable def cosetToCycles :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (semiInfiniteBRSTComplex A hV hg).kerQ :=
  (cosetToComplex A.toAffineSl2Action).codRestrict _
    (fun x => cosetToComplex_closed A.toAffineSl2Action x)

/-- The actual linear map from the coset to BRST cohomology. -/
noncomputable def cosetToCohomology :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (semiInfiniteBRSTComplex A hV hg).Coh :=
  (semiInfiniteBRSTComplex A hV hg).prj.comp (cosetToCycles A hV hg)

/-- Every coset class has ghost degree zero. -/
theorem cosetToCohomology_mem_H0 (x : cosetSubspace A.toAffineSl2Action) :
    cosetToCohomology A hV hg x ∈ (semiInfiniteBRSTComplex A hV hg).H0 :=
  Submodule.mem_map_of_mem (cosetToComplex_ghost A.toAffineSl2Action x)

/-- The same map with codomain explicitly restricted to `H⁰`. -/
noncomputable def cosetToH0 :
    cosetSubspace A.toAffineSl2Action →ₗ[ℂ] (semiInfiniteBRSTComplex A hV hg).H0 :=
  (cosetToCohomology A hV hg).codRestrict _ (cosetToCohomology_mem_H0 A hV hg)

/-- Vacuum preservation in cohomology. -/
theorem cosetToCohomology_vacuum :
    cosetToCohomology A hV hg
      ⟨V.vacuum, vacuum_mem_cosetSubspace A.toAffineSl2Action⟩ =
      (semiInfiniteBRSTComplex A hV hg).cohomology.vacuum := rfl

/-- All vertex products descend along the coset map. -/
theorem cosetToCohomology_mode (x y : cosetSubspace A.toAffineSl2Action) (n : ℤ) :
    cosetToCohomology A hV hg
      ⟨mode (V.Y (x : M)) n (y : M),
        mode_mem_cosetSubspace A.toAffineSl2Action A.translation x.property y.property n⟩ =
      mode ((semiInfiniteBRSTComplex A hV hg).cohomology.Y
        (cosetToCohomology A hV hg x)) n (cosetToCohomology A hV hg y) := by
  change (semiInfiniteBRSTComplex A hV hg).prj _ =
    mode ((semiInfiniteBRSTComplex A hV hg).Ycohom
      ((semiInfiniteBRSTComplex A hV hg).prj (cosetToCycles A hV hg x))) n
        ((semiInfiniteBRSTComplex A hV hg).prj (cosetToCycles A hV hg y))
  rw [BRST.BRSTComplex.mode_Ycohom]
  congr 1
  apply Subtype.ext
  exact ghostVacuumEmbedding_mode (x : M) (y : M) n

end VOA.Sl2Coset
