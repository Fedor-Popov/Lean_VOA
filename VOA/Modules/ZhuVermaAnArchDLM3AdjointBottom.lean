/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWIndependence
import VOA.Modules.ZhuVermaAnArchRhoFZ

/-!
# A concrete faithful bottom for DLM3 induction

This file supplies a family of satisfying instances of the PBW boundary.
For the adjoint module `𝒱`, its weight-zero space is a genuine Zhu module.  The inclusion of that
bottom into `𝒱` is `P₀`-equivariant for the Frenkel--Zhu `V̂`-action, hence the universal property
of `IndMod` gives a left inverse of its canonical bottom map.  The bottom map is therefore
injective, without PBW and without any project axiom.

The Euler-operator theorem `levCover_iSupIndep` proves level independence for every parabolic
representation.  Combining it with the adjoint bottom injection therefore gives a full concrete
`PBWFreeness` term and, at level zero, a `BottomProjection`. Neither construction uses the
PBW theorem `VOA.pbw`. The companion
`Examples.HeisenbergPBWFreeness` proves that the rank-one Heisenberg instance has a genuinely
nonzero bottom vector and induced image.

This is a satisfiability result for the abstract structures, not a discharge of the downstream
regular-module gate: the parabolic representation here is built from
`adjointBottomAMod W = (adjointModule W).weight 0`, whereas Zhu bijectivity carries a projection
for `regularAMod W`.  No identification of those two `A(W)`-modules is asserted.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace DLM3

/-- The adjoint module has lowest weight zero. -/
theorem adjointModule_isLowestWeight (W : VertexOperatorAlgebra 𝒱) :
    IsLowestWeight (adjointModule W) 0 := by
  intro α hα
  by_cases h : ∃ m : ℤ, (m : ℂ) = α
  · obtain ⟨m, rfl⟩ := h
    rw [show (adjointModule W).weight (m : ℂ) = adjWeight W (m : ℂ) from rfl,
      adjWeight_cast W m] at hα
    have hm : 0 ≤ m := by
      by_contra hm
      exact hα (W.positivity m (not_le.mp hm))
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    exact ⟨k, by simp⟩
  · have hbot : (adjointModule W).weight α = ⊥ :=
      adjWeight_eq_bot W (not_exists.mp h)
    exact absurd hbot hα

/-- The Zhu module on the weight-zero bottom of the adjoint module. -/
noncomputable abbrev adjointBottomAMod (W : VertexOperatorAlgebra 𝒱) : AMod W :=
  lowestAMod (adjointModule_isLowestWeight W)

/-- Inclusion of the adjoint weight-zero bottom into the VOA. -/
def adjointBottomInclusion (W : VertexOperatorAlgebra 𝒱) :
    (adjointBottomAMod W).carrier →ₗ[ℂ] 𝒱 :=
  ((adjointModule W).weight 0).subtype

@[simp] theorem adjointBottomInclusion_apply (W : VertexOperatorAlgebra 𝒱)
    (x : (adjointBottomAMod W).carrier) :
    adjointBottomInclusion W x = ((adjointModule W).weight 0).subtype x := rfl

theorem adjointBottomInclusion_injective (W : VertexOperatorAlgebra 𝒱) :
    Function.Injective (adjointBottomInclusion W) := by
  intro x y h
  exact Subtype.ext h

/-- The weight-zero inclusion intertwines the pulled-back `P₀` action with the adjoint
Frenkel--Zhu action. -/
theorem adjointBottomInclusion_equivariant (W : VertexOperatorAlgebra 𝒱)
    (g : Pn W 0) (x : (adjointBottomAMod W).carrier) :
    adjointBottomInclusion W ((parabolicRepOfAMod W (adjointBottomAMod W)).act g x) =
      fzRho W (g : VHatCarrier W) (adjointBottomInclusion W x) := by
  change adjointBottomInclusion W
      ((adjointBottomAMod W).ρ (zhuDeg0 W (g : VHatCarrier W)) x) =
    fzRho W (g : VHatCarrier W) (adjointBottomInclusion W x)
  refine Submodule.span_induction
    (p := fun y _ =>
      adjointBottomInclusion W ((adjointBottomAMod W).ρ (zhuDeg0 W y) x) =
        fzRho W y (adjointBottomInclusion W x))
    ?_ ?_ ?_ ?_ g.2
  · rintro y ⟨w, m, a, ha, hd, rfl⟩
    rcases hd with hd | hd
    · have hm : m = w - 1 := by omega
      subst m
      rw [zhuDeg0_gen_deg_zero W ha (by ring)]
      rw [show (adjointBottomAMod W).ρ =
          actA (adjointModule W) (adjointModule_isLowestWeight W) from rfl]
      change
        (((actA (adjointModule W) (adjointModule_isLowestWeight W))
            (VOA.mk W a) x : (adjointModule W).weight 0) : 𝒱) =
          (fzRho W).actMode a (w - 1) (adjointBottomInclusion W x)
      have hlhs := actA_mk_apply_coe (adjointModule W)
        (adjointModule_isLowestWeight W) a x
      rw [hlhs, oMod_homogeneous (adjointModule W) ha]
      change mode (W.Y a) (w - 1) (adjointBottomInclusion W x) =
        (fzRho W).actMode a (w - 1) (adjointBottomInclusion W x)
      rw [fzRho_actMode]
    · have hne : w - m - 1 ≠ 0 := by omega
      rw [zhuDeg0_gen_of_ne W ha hne, map_zero, LinearMap.zero_apply, map_zero]
      change 0 = (fzRho W).actMode a m (adjointBottomInclusion W x)
      rw [fzRho_actMode]
      symm
      have hx : adjointBottomInclusion W x ∈ (adjointModule W).weight 0 := by
        simpa only [adjointBottomInclusion_apply] using x.2
      exact mode_lowering_vanish (adjointModule W) (adjointModule_isLowestWeight W)
        ha hx (by omega)
  · simp only [map_zero, LinearMap.zero_apply]
  · intro y z _ _ hy hz
    simp only [map_add, LinearMap.add_apply]
    rw [hy, hz]
  · intro c y _ hy
    simp only [map_smul, LinearMap.smul_apply]
    rw [hy]

/-- The universal `IndMod` lift from the adjoint bottom to the adjoint representation. -/
noncomputable def adjointBottomLift (W : VertexOperatorAlgebra 𝒱) :
    IndMod (parabolicRepOfAMod W (adjointBottomAMod W)) →ₗ[ℂ] 𝒱 :=
  indLift (parabolicRepOfAMod W (adjointBottomAMod W)) (fzRho W)
    (adjointBottomInclusion W) (adjointBottomInclusion_equivariant W)

@[simp] theorem adjointBottomLift_bottom (W : VertexOperatorAlgebra 𝒱)
    (x : (adjointBottomAMod W).carrier) :
    adjointBottomLift W
        (indBottom (parabolicRepOfAMod W (adjointBottomAMod W)) x) =
      adjointBottomInclusion W x := by
  rw [adjointBottomLift, indLift_bottom, adjointBottomInclusion_apply]

/-- **Concrete faithful bottom, PBW-free.**  The canonical bottom map for the adjoint
weight-zero Zhu module is injective. -/
theorem adjoint_indBottom_injective (W : VertexOperatorAlgebra 𝒱) :
    Function.Injective (indBottom (parabolicRepOfAMod W (adjointBottomAMod W))) := by
  intro x y hxy
  apply adjointBottomInclusion_injective W
  have h := congrArg (adjointBottomLift W) hxy
  simpa only [adjointBottomLift_bottom] using h

/-- **A concrete full `PBWFreeness` term.**  The adjoint weight-zero Zhu module has an injective
bottom by the separating adjoint realization, and its levels are independent by the descended
Euler operator.  This is not the `regularAMod W` instance carried by the downstream gate. -/
def adjointPBWFreeness (W : VertexOperatorAlgebra 𝒱) :
    PBWFreeness (parabolicRepOfAMod W (adjointBottomAMod W)) :=
  pbwFreeness_of_bottom_injective _ (adjoint_indBottom_injective W)

/-- The resulting level-zero bottom projection for the adjoint bottom. -/
noncomputable def adjointBottomProjection (W : VertexOperatorAlgebra 𝒱) :
    BottomProjection (parabolicRepOfAMod W (adjointBottomAMod W)) :=
  bottomProjectionOfInjective _ (adjoint_indBottom_injective W)

end DLM3
end VHat
end VOA
