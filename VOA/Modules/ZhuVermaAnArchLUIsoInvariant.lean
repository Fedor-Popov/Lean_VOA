/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUFunctorial

/-!
# `J(U)` is natural: the functor map `M(e)` carries `J(U₁)` onto `J(U₂)`.

`J(U) = maxJ` is the maximal bottom-trivial graded submodule of `M(U)`, hence **canonical**.  Any
graded-preserving, action-intertwining `ℂ`-linear equivalence `f : M(U₁) ≅ M(U₂)` therefore carries
`J(U₁)` onto `J(U₂)` (`transported_le_djJ` in both directions).  Applied to the functor map
`M(e) = djFunctorEquiv` and its inverse, this gives the DJ-track `MUJNatural`:
`M(e)(J(U₁)) = J(U₂)`.

This is the last graded ingredient of the DJ-track `isoInvariant`; it necessarily carries the graded
data `(Pr, hU, h, hL0)` of `djJ`.

Proof-term `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, and
`pbw`-free, but conditional on the carried `regularAMod` `BottomProjection` hypothesis `Pr`. The
project-level witness `voaPBWBottomProjection` is supplied from the generic relative-induction
field of the theorem `VOA.pbw : PBWPrinciple`.

## References
Dong–Jiang math/0601626 Prop 3.5.  `ZhuVermaAnArchLU` (`djJ`, `djJ_bottom_disjoint`),
`ZhuVermaAnArchLUGraded` (`maxJ`, `le_maxJ_of_bottom_disjoint`), `ZhuVermaAnArchLUFunctorial`
(`djFunctorEquiv`, `djFunctorEquiv_natural`, `djFunctorEquiv_maps_deg`).
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra
open VHat VHat.DLM3 GradedLWWeakModule

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **A graded action-intertwining equivalence carries `J(U₁)` into `J(U₂)`.**  The image of
`J(U₁) = maxJ` is act-closed (`hnat`) and bottom-trivial (`hdeg` at level 0 + `djJ_bottom_disjoint`),
hence `≤ maxJ = J(U₂)` (`le_maxJ_of_bottom_disjoint`). -/
theorem transported_le_djJ (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (hU₁ : Nontrivial U₁.carrier) (hU₂ : Nontrivial U₂.carrier) (h : ℂ)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h + n) • x)
    (f : DJCarrier W U₁ ≃ₗ[ℂ] DJCarrier W U₂)
    (hnat : ∀ (p : ℤ) (a : 𝒱) (y : DJCarrier W U₁),
      f (djModeZero W U₁ p a y) = djModeZero W U₂ p a (f y))
    (hdeg : Submodule.map f.toLinearMap (DJCarrier.deg W U₁ 0) = DJCarrier.deg W U₂ 0) :
    Submodule.map f.toLinearMap (djJ Pr U₁ hU₁ h hL0₁).carrier ≤ (djJ Pr U₂ hU₂ h hL0₂).carrier := by
  classical
  letI := DirectSum.IsInternal.chooseDecomposition
    (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂).weight
    (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂).isInternal
  let K : WeakModule.Submodule' (djCarrierWeak W U₂) :=
    { carrier := Submodule.map f.toLinearMap (djJ Pr U₁ hU₁ h hL0₁).carrier
      act_mem := fun u n {x} hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        have key : (djCarrierWeak W U₂).act u n (f.toLinearMap y)
            = f.toLinearMap ((djCarrierWeak W U₁).act u n y) := by
          simp only [djCarrierWeak_act, LinearEquiv.coe_coe, hnat]
        rw [key]
        exact Submodule.mem_map_of_mem ((djJ Pr U₁ hU₁ h hL0₁).act_mem u n hy) }
  have hbd : K.carrier ⊓ (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂).weight h = ⊥ := by
    show Submodule.map f.toLinearMap (djJ Pr U₁ hU₁ h hL0₁).carrier
        ⊓ (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂).weight h = ⊥
    rw [show (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂).weight h = DJCarrier.deg W U₂ 0 from
        djCWeight_zero U₂ h, ← hdeg, ← Submodule.map_inf f.toLinearMap f.injective,
      djJ_bottom_disjoint, Submodule.map_bot]
  exact le_maxJ_of_bottom_disjoint (djGradedLW_of_pbwDatum Pr U₂ hU₂ h hL0₂) K hbd

/-- **`M(e)` carries `J(U₁)` onto `J(U₂)`** — the DJ-track `MUJNatural`, by antisymmetry of
`transported_le_djJ` (forward with `M(e)`, backward with its inverse). -/
theorem djFunctorEquiv_maps_djJ (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) (hU₁ : Nontrivial U₁.carrier)
    (hU₂ : Nontrivial U₂.carrier) (h : ℂ)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h + n) • x) :
    Submodule.map (djFunctorEquiv U₁ U₂ e).toLinearMap (djJ Pr U₁ hU₁ h hL0₁).carrier
      = (djJ Pr U₂ hU₂ h hL0₂).carrier := by
  refine le_antisymm
    (transported_le_djJ Pr hU₁ hU₂ h hL0₁ hL0₂ (djFunctorEquiv U₁ U₂ e)
      (djFunctorEquiv_natural U₁ U₂ e) (djFunctorEquiv_maps_deg U₁ U₂ e 0)) ?_
  -- Backward: `map (M(e).symm) (J U₂) ≤ J U₁`, then apply `map (M(e))`.
  have hback : Submodule.map (djFunctorEquiv U₁ U₂ e).symm.toLinearMap (djJ Pr U₂ hU₂ h hL0₂).carrier
      ≤ (djJ Pr U₁ hU₁ h hL0₁).carrier :=
    transported_le_djJ Pr hU₂ hU₁ h hL0₂ hL0₁ (djFunctorEquiv U₁ U₂ e).symm
      (djFunctorEquiv_symm_natural U₁ U₂ e) (djFunctorEquiv_symm_maps_deg U₁ U₂ e 0)
  have hmap := Submodule.map_mono (f := (djFunctorEquiv U₁ U₂ e).toLinearMap) hback
  rwa [← Submodule.map_comp,
    show (djFunctorEquiv U₁ U₂ e).toLinearMap.comp (djFunctorEquiv U₁ U₂ e).symm.toLinearMap
        = LinearMap.id from by ext x; simp, Submodule.map_id] at hmap

/-! ## The descent: `L(U₁) ≅ L(U₂)` -/

/-- **The functor map descends to the quotient** `L(U₁) = M(U₁)/J ≅ M(U₂)/J = L(U₂)` (linear). -/
noncomputable def djLUFunctorLinEquiv (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) (hU₁ : Nontrivial U₁.carrier)
    (hU₂ : Nontrivial U₂.carrier) (h : ℂ)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h + n) • x) :
    (DJCarrier W U₁ ⧸ (djJ Pr U₁ hU₁ h hL0₁).carrier)
      ≃ₗ[ℂ] (DJCarrier W U₂ ⧸ (djJ Pr U₂ hU₂ h hL0₂).carrier) :=
  Submodule.Quotient.equiv _ _ (djFunctorEquiv U₁ U₂ e)
    (djFunctorEquiv_maps_djJ Pr e hU₁ hU₂ h hL0₁ hL0₂)

@[simp] theorem djLUFunctorLinEquiv_mk
    (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) (hU₁ : Nontrivial U₁.carrier)
    (hU₂ : Nontrivial U₂.carrier) (h : ℂ)
    (hL0₁ : ∀ (n : ℕ) (x : DJCarrier W U₁), x ∈ DJCarrier.deg W U₁ n →
      djModeZero W U₁ 1 W.conformalVector x = (h + n) • x)
    (hL0₂ : ∀ (n : ℕ) (x : DJCarrier W U₂), x ∈ DJCarrier.deg W U₂ n →
      djModeZero W U₂ 1 W.conformalVector x = (h + n) • x) (x : DJCarrier W U₁) :
    djLUFunctorLinEquiv Pr e hU₁ hU₂ h hL0₁ hL0₂ (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (djFunctorEquiv U₁ U₂ e x) := by
  rw [djLUFunctorLinEquiv, Submodule.Quotient.equiv_apply]
  rfl

end

end VOA
