/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2CosetConcreteFactors
import VOA.Core.SuperEvenPart

/-!
# The ordinary vertex algebra on the concrete diagonal coset

The commutant is stable under weight projections as well as all vertex modes.
Pure evenness and natural weight support therefore give an ordinary vertex
algebra on the actual coset carrier, with exactly the existing coset products.
-/

namespace VOA.Sl2CosetConcrete

open Module (End)
open Sl2SemiInfinite Sl2Coset
open scoped TensorProduct

noncomputable section

section Restriction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M} {k : ℂ}
variable (A : AffineSl2Action V k) (H : TranslationCovariant V)

local instance : DirectSum.Decomposition V.grading :=
  V.isInternal.chooseDecomposition V.grading

/-- Current modes shift weights, so their common kernel is graded. -/
theorem weightProjection_mem_coset (h : ℂ) {x : M} (hx : x ∈ cosetSubspace A) :
    homogProj V.grading h x ∈ cosetSubspace A := by
  intro a n hn
  have hs := BRST.homogProj_shift V.grading (mode (V.Y (A.current a)) n)
    (Equiv.subRight (n : ℂ)) (fun j y hy => by
      simpa only [Equiv.subRight_apply,
        show (1 : ℂ) + j - (n : ℂ) - 1 = j - (n : ℂ) by ring]
        using V.grading_mode (A.current a) (A.current_weight a) y hy n) h x
  rw [hx a n hn, map_zero] at hs
  exact hs.symm

/-- Restriction of the ambient complex-weight grading to the commutant. -/
def cosetGradingC (h : ℂ) : Submodule ℂ (cosetSubspace A) :=
  (V.grading h).comap (cosetSubspace A).subtype

theorem cosetGradingC_isInternal : DirectSum.IsInternal (cosetGradingC A) :=
  isInternal_comap V.grading (cosetSubspace A) (fun h _ hx => weightProjection_mem_coset A h hx)

instance cosetGradingC_finite (h : ℂ) : FiniteDimensional ℂ (cosetGradingC A h) := by
  haveI := V.finrank h
  refine Module.Finite.of_injective (LinearMap.codRestrict (V.grading h)
    ((cosetSubspace A).subtype.comp (cosetGradingC A h).subtype) (fun x => x.2)) ?_
  intro x y hxy
  have hcoe := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext hcoe)

/-- The actual restricted state-field map, with no change in any coefficient. -/
def cosetY : cosetSubspace A →ₗ[ℂ] (End ℂ (cosetSubspace A))⟦z^±⟧ where
  toFun x := fun j => (V.Y x j).restrict (fun y hy => by
    have h := mode_mem_cosetSubspace A H x.2 hy (-j - 1)
    simpa only [mode_apply, show -(-j - 1) - 1 = j by omega] using h)
  map_add' x y := by
    funext j
    ext z
    simp only [Submodule.coe_add, map_add, LinearMap.restrict_apply]
    rfl
  map_smul' c x := by
    funext j
    ext z
    simp only [Submodule.coe_smul, map_smul, LinearMap.restrict_apply, RingHom.id_apply]
    rfl

@[simp] theorem cosetY_coeff_coe (x y : cosetSubspace A) (j : ℤ) :
    ((cosetY A H x j y : cosetSubspace A) : M) = V.Y x j y := rfl

@[simp] theorem cosetY_mode_coe (x y : cosetSubspace A) (n : ℤ) :
    ((mode (cosetY A H x) n y : cosetSubspace A) : M) = mode (V.Y x) n y := rfl

theorem cosetY_bracket_coe (x y z : cosetSubspace A) (N : ℕ) (m n : ℤ) :
    ((mulBySubPow N (bracketDist (cosetY A H x) (cosetY A H y)) m n z :
      cosetSubspace A) : M) =
      mulBySubPow N (bracketDist (V.Y x) (V.Y y)) m n z := by
  induction N generalizing m n with
  | zero =>
      simp only [mulBySubPow, LinearMap.id_apply, bracketDist_apply,
        LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
      rfl
  | succ N ih =>
      simp only [mulBySubPow, LinearMap.comp_apply, mulBySub_apply,
        LinearMap.sub_apply, Submodule.coe_sub, ih]

/-- Integer weights form an internal grading of a naturally supported coset. -/
theorem cosetGradingZ_isInternal (hn : DSMor.NatSupported V.grading) :
    DirectSum.IsInternal (fun n : ℤ => cosetGradingC A (n : ℂ)) := by
  classical
  apply isInternal_comp_of_bot (fun _ _ h => Int.cast_injective h)
    (cosetGradingC_isInternal A)
  intro h hh
  have hzero := hn h (fun ⟨n, hn⟩ => hh ⟨(n : ℤ), by exact_mod_cast hn⟩)
  unfold cosetGradingC
  rw [hzero, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _)

/-- A purely even, naturally supported affine commutant is an ordinary vertex algebra. -/
def cosetVertexAlgebraOf (he : V.parity 0 = ⊤)
    (hn : DSMor.NatSupported V.grading) : PreVertexAlgebra (cosetSubspace A) where
  grading n := cosetGradingC A (n : ℂ)
  isInternal := cosetGradingZ_isInternal A hn
  finrank n := cosetGradingC_finite A (n : ℂ)
  Y := cosetY A H
  vacuum := cosetVacuum A
  vacuum_mem := by
    change V.vacuum ∈ V.grading ((0 : ℤ) : ℂ)
    simpa only [Int.cast_zero] using V.vacuum_mem
  grading_mode := by
    intro p q x hx y hy n
    change mode (V.Y x) n y ∈ V.grading (((p + q - n - 1 : ℤ) : ℂ))
    push_cast
    exact V.grading_mode x hx y hy n
  vacuum_Y := by
    funext j
    ext x
    rw [cosetY_coeff_coe]
    change V.Y V.vacuum j x = _
    rw [V.vacuum_Y, FormalDist.one_apply, FormalDist.one_apply]
    by_cases hj : j = 0 <;> simp [hj]
  creation := by
    intro x
    exact ⟨Subtype.ext (V.creation x).1,
      fun n hn => Subtype.ext ((V.creation x).2 n hn)⟩
  locality := by
    intro x y
    have hx : (x : M) ∈ V.parity 0 := by rw [he]; exact Submodule.mem_top
    have hy : (y : M) ∈ V.parity 0 := by rw [he]; exact Submodule.mem_top
    have hloc := V.locality x hx y hy
    rw [koszul_zero_left] at hloc
    obtain ⟨N, hN⟩ := (localε_one_iff _ _).mp hloc
    refine ⟨N, ?_⟩
    funext m n
    ext z
    rw [cosetY_bracket_coe, hN]
    rfl
  regularity := by
    intro x y
    obtain ⟨N, hN⟩ := V.regularity x y
    exact ⟨N, fun n hn => Subtype.ext (hN n hn)⟩

@[simp] theorem cosetVertexAlgebraOf_vacuum (he : V.parity 0 = ⊤)
    (hn : DSMor.NatSupported V.grading) :
    (cosetVertexAlgebraOf A H he hn).vacuum = cosetVacuum A := rfl

@[simp] theorem cosetVertexAlgebraOf_mode (he : V.parity 0 = ⊤)
    (hn : DSMor.NatSupported V.grading) (x y : cosetSubspace A) (n : ℤ) :
    (cosetVertexAlgebraOf A H he hn).smul x n y = cosetMode A H x n y := rfl

/-- Natural support descends to positivity of the integer coset grading. -/
theorem cosetVertexAlgebraOf_positivity (he : V.parity 0 = ⊤)
    (hn : DSMor.NatSupported V.grading) (n : ℤ) (hneg : n < 0) :
    (cosetVertexAlgebraOf A H he hn).grading n = ⊥ := by
  have hz : V.grading (n : ℂ) = ⊥ := hn _ (by
    rintro ⟨m, hm⟩
    have hi : (m : ℤ) = n := by exact_mod_cast hm
    omega)
  change (V.grading (n : ℂ)).comap (cosetSubspace A).subtype = ⊥
  rw [hz, Submodule.comap_bot]
  exact LinearMap.ker_eq_bot.mpr (Submodule.subtype_injective _)

/-- The vacuum line of the ambient algebra remains exactly the coset weight-zero space. -/
theorem cosetVertexAlgebraOf_vacuum_grade (he : V.parity 0 = ⊤)
    (hn : DSMor.NatSupported V.grading) (h0 : V.grading 0 = ℂ ∙ V.vacuum) :
    (cosetVertexAlgebraOf A H he hn).grading 0 =
      ℂ ∙ (cosetVertexAlgebraOf A H he hn).vacuum := by
  ext x
  change ((x : M) ∈ V.grading ((0 : ℤ) : ℂ)) ↔ _
  rw [Int.cast_zero, h0, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg Subtype.val hc⟩

end Restriction

/-- The first two concrete factors, and hence their tensor product, are purely even. -/
theorem abPurelyEven : abSVA.parity 0 = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul x y =>
      exact TensorVA.tmul_mem_tenParity ASVA BSVA
        (show x ∈ ASVA.parity 0 from Submodule.mem_top)
        (show y ∈ BSVA.parity 0 from Submodule.mem_top)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- Weight zero of the concrete tensor algebra is its vacuum line. -/
theorem abVacuumGrade : abSVA.grading 0 = ℂ ∙ abSVA.vacuum := by
  have hA : ASVA.grading 0 = ℂ ∙ ASVA.vacuum := by
    change AVOA.toPreVertexAlgebra.gradingC 0 = _
    rw [← show ((0 : ℤ) : ℂ) = 0 by simp, PreVertexAlgebra.gradingC_intCast]
    exact AVOA.vacuum_grade
  have hB : BSVA.grading 0 = ℂ ∙ BSVA.vacuum := by
    change BVOA.toPreVertexAlgebra.gradingC 0 = _
    rw [← show ((0 : ℤ) : ℂ) = 0 by simp, PreVertexAlgebra.gradingC_intCast]
    exact BVOA.vacuum_grade
  change TensorVA.tenGrading ASVA BSVA 0 = ℂ ∙ (ASVA.vacuum ⊗ₜ[ℂ] BSVA.vacuum)
  rw [tenGrading_zero_eq ASVA BSVA aNatSupported bNatSupported]
  apply le_antisymm
  · intro x hx
    refine TensorVA.tenSub_induction (Submodule.zero_mem _)
      (fun _ _ => Submodule.add_mem _) (fun c _ => Submodule.smul_mem _ c) ?_ hx
    intro x hx y hy
    rw [hA, Submodule.mem_span_singleton] at hx
    rw [hB, Submodule.mem_span_singleton] at hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    rw [Submodule.mem_span_singleton]
    exact ⟨c * d, by simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_smul, mul_comm]⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact TensorVA.tmul_mem_tenSub ASVA.vacuum_mem BSVA.vacuum_mem

/-- The actual diagonal coset carries its ordinary vertex algebra without hypotheses. -/
def cosetVertexAlgebra : PreVertexAlgebra (cosetSubspace diagonalAction.toAffineSl2Action) :=
  cosetVertexAlgebraOf diagonalAction.toAffineSl2Action diagonalAction.translation
    abPurelyEven abNatSupported

@[simp] theorem cosetVertexAlgebra_vacuum :
    cosetVertexAlgebra.vacuum = cosetVacuum diagonalAction.toAffineSl2Action := rfl

@[simp] theorem cosetVertexAlgebra_mode
    (x y : cosetSubspace diagonalAction.toAffineSl2Action) (n : ℤ) :
    cosetVertexAlgebra.smul x n y =
      cosetMode diagonalAction.toAffineSl2Action diagonalAction.translation x n y := rfl

/-- CFT-type positivity holds on the actual ordinary coset vertex algebra. -/
theorem cosetVertexAlgebra_positivity (n : ℤ) (hn : n < 0) :
    cosetVertexAlgebra.grading n = ⊥ :=
  cosetVertexAlgebraOf_positivity _ _ abPurelyEven abNatSupported n hn

/-- CFT-type weight zero holds on the actual ordinary coset vertex algebra. -/
theorem cosetVertexAlgebra_vacuum_grade :
    cosetVertexAlgebra.grading 0 = ℂ ∙ cosetVertexAlgebra.vacuum :=
  cosetVertexAlgebraOf_vacuum_grade _ _ abPurelyEven abNatSupported abVacuumGrade

end
end VOA.Sl2CosetConcrete
