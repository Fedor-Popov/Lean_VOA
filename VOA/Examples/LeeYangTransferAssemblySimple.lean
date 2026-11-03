/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteVOA
import VOA.Examples.VirasoroSimple
import VOA.Examples.LeeYangSingular
import VOA.Core.SimpleImage

/-!
# Simplicity from the Lee--Yang coset identification

OPEN: `CosetIdentification` is the conformal vertex-algebra identification of
the actual diagonal-current commutant with the simple Lee--Yang Virasoro VOA.
Its existence is not proved here. Once supplied, simplicity of the coset and
injectivity of its concrete BRST cohomology map are consequences, not extra
open inputs.
-/

namespace VOA.LeeYangTransferAssembly

open Sl2CosetConcrete VirModule VirSimple LeeYang

noncomputable section

/-- The concrete carrier of the simple Lee--Yang Virasoro VOA. -/
abbrev LeeYangSpace := VirUniv leeYangC ⧸ maxIdealVir leeYangC

/-- OPEN: a conformal VOA isomorphism identifying the diagonal coset with
the simple Lee--Yang Virasoro algebra. -/
structure CosetIdentification where
  /-- The isomorphism of complex state spaces. -/
  equiv : CosetSpace ≃ₗ[ℂ] LeeYangSpace
  /-- Vacuum and every vertex product are preserved. -/
  hom : IsVOAHom cosetVOA (virasoroSimple leeYangC) equiv.toLinearMap
  /-- The coset stress tensor maps to the Virasoro conformal vector. -/
  conformal : equiv cosetVOA.conformalVector =
    (virasoroSimple leeYangC).conformalVector

/-- Simplicity pulls back across a vertex-algebra isomorphism. -/
theorem simple_of_vertexEquiv {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {V : VertexOperatorAlgebra X}
    {W : VertexOperatorAlgebra Y} (e : X ≃ₗ[ℂ] Y)
    (he : IsVOAHom V W e.toLinearMap) (hW : W.IsSimple) : V.IsSimple := by
  refine ⟨fun h => hW.1 ?_, fun I hI => ?_⟩
  · rw [eq_bot_iff]
    intro y _
    have hy : e.symm y ∈ (⊤ : Submodule ℂ X) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at hy
    rw [Submodule.mem_bot, ← e.apply_symm_apply y, hy, map_zero]
  · have hJ : W.IsIdeal (I.map e.toLinearMap) := by
      intro u v n hv
      obtain ⟨v', hv', rfl⟩ := hv
      refine ⟨V.smul (e.symm u) n v', hI _ _ _ hv', ?_⟩
      have hm := he.map_smul (e.symm u) n v'
      simpa only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply] using hm
    have hc : I = (I.map e.toLinearMap).comap e.toLinearMap :=
      (Submodule.comap_map_eq_of_injective e.injective I).symm
    rcases hW.2 _ hJ with h | h
    · left
      rw [hc, h, Submodule.comap_bot]
      exact LinearMap.ker_eq_bot.mpr e.injective
    · right
      rw [hc, h, Submodule.comap_top]

/-- Coset simplicity is discharged by the identification with the existing
simple Virasoro quotient. -/
theorem CosetIdentification.coset_isSimple (ident : CosetIdentification) :
    cosetVOA.IsSimple :=
  simple_of_vertexEquiv ident.equiv ident.hom (virasoroSimple_isSimple leeYangC)

/-- The actual coset-to-cohomology map is injective once the VOA identification
is supplied; no independent simplicity assumption remains. -/
theorem CosetIdentification.cosetToH0_injective (ident : CosetIdentification) :
    Function.Injective leeYangCosetToH0 :=
  leeYangCosetToH0_injective_of_cosetSimple ident.coset_isSimple

/-- An integer eigenvector of `L₀` belongs to the corresponding VOA weight space. -/
theorem mem_grading_of_L_zero {X : Type*} [AddCommGroup X] [Module ℂ X]
    (V : VertexOperatorAlgebra X) {n : ℤ} {x : X}
    (hx : V.L 0 x = (n : ℂ) • x) : x ∈ V.grading n := by
  have htop : (⊤ : Submodule ℂ X) ≤ V.grading n ⊔ ⨆ (k : ℤ) (_ : k ≠ n),
      V.grading k := by
    rw [← V.isInternal.submodule_iSup_eq_top, iSup_split_single _ n]
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.mp (htop (Submodule.mem_top (x := x)))
  have hgr : ∀ k : ℤ, V.grading k ≤ (V.L 0).eigenspace (k : ℂ) := fun k y hy =>
    Module.End.mem_eigenspace_iff.mpr (V.L_zero_grading y hy)
  have hz1 : z ∈ (V.L 0).eigenspace (n : ℂ) := by
    have h1 : a + z ∈ (V.L 0).eigenspace (n : ℂ) :=
      Module.End.mem_eigenspace_iff.mpr hx
    simpa using Submodule.sub_mem _ h1 (hgr n ha)
  have hle : (⨆ (k : ℤ) (_ : k ≠ n), V.grading k) ≤
      ⨆ (μ : ℂ) (_ : μ ≠ (n : ℂ)), (V.L 0).eigenspace μ :=
    iSup₂_le fun k hk => le_trans (hgr k)
      (le_iSup₂_of_le (k : ℂ) (by exact_mod_cast hk) le_rfl)
  have hz0 := Submodule.disjoint_def.mp (Module.End.eigenspaces_iSupIndep (V.L 0)
    (n : ℂ)) z hz1 (hle hz)
  rw [hz0, add_zero]
  exact ha

/-- Preservation of the conformal vector identifies the actual conformal weight spaces. -/
theorem CosetIdentification.map_mem_grading_iff (ident : CosetIdentification)
    (n : ℤ) (x : CosetSpace) :
    ident.equiv x ∈ (virasoroSimple leeYangC).grading n ↔ x ∈ cosetVOA.grading n := by
  constructor
  · intro hx
    apply mem_grading_of_L_zero cosetVOA
    apply ident.equiv.injective
    calc
      ident.equiv (cosetVOA.L 0 x) =
          (virasoroSimple leeYangC).L 0 (ident.equiv x) :=
        ident.hom.map_L ident.conformal 0 x
      _ = (n : ℂ) • ident.equiv x := (virasoroSimple leeYangC).L_zero_grading _ hx
      _ = ident.equiv ((n : ℂ) • x) := (map_smul ident.equiv _ _).symm
  · intro hx
    apply mem_grading_of_L_zero (virasoroSimple leeYangC)
    calc
      (virasoroSimple leeYangC).L 0 (ident.equiv x) =
          ident.equiv (cosetVOA.L 0 x) := (ident.hom.map_L ident.conformal 0 x).symm
      _ = ident.equiv ((n : ℂ) • x) := congrArg ident.equiv (cosetVOA.L_zero_grading x hx)
      _ = (n : ℂ) • ident.equiv x := map_smul ident.equiv _ _

/-- The conformal VOA identification restricts to an isomorphism at each weight. -/
def CosetIdentification.weightEquiv (ident : CosetIdentification) (n : ℤ) :
    cosetVOA.grading n ≃ₗ[ℂ] (virasoroSimple leeYangC).grading n where
  toFun x := ⟨ident.equiv x, (ident.map_mem_grading_iff n x).mpr x.property⟩
  invFun y := ⟨ident.equiv.symm y, (ident.map_mem_grading_iff n (ident.equiv.symm y)).mp
    (by simpa only [LinearEquiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (ident.equiv.symm_apply_apply x)
  right_inv y := Subtype.ext (ident.equiv.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add ident.equiv (x : CosetSpace) (y : CosetSpace))
  map_smul' c x := Subtype.ext (map_smul ident.equiv c (x : CosetSpace))

@[simp] theorem CosetIdentification.weightEquiv_apply_coe (ident : CosetIdentification)
    (n : ℤ) (x : cosetVOA.grading n) :
    (ident.weightEquiv n x : LeeYangSpace) = ident.equiv x := rfl

@[simp] theorem CosetIdentification.weightEquiv_symm_apply_coe (ident : CosetIdentification)
    (n : ℤ) (x : (virasoroSimple leeYangC).grading n) :
    ((ident.weightEquiv n).symm x : CosetSpace) = ident.equiv.symm x := rfl

end
end VOA.LeeYangTransferAssembly
