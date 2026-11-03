/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Core.WeightOneCohomology
import VOA.Core.BilinearForm

/-!
# Reconstruction from a closed lift inside a first-order extension

A state `(u,u₁)` represents `u + t u₁`, with `t² = 0`. If a subspace of this
extension is closed under all products and projects onto a simple VOA, its pure
first-order coefficients form an ideal. Excluding the pure first-order vacuum
makes that ideal zero. Inverting the projection then constructs a change of
coordinates, provided the subspace respects the grading and contains the vacuum.

This proves the linear-algebra and simplicity step of reconstruction. It does
not assert separation for the current-generated subspace of a regular deformation.
The extension itself is not assumed to be CFT type: its weight-zero space has two
dimensions, so using that assumption would be circular.
-/

namespace VOA.Deform.Reconstruction
open VertexOperatorAlgebra
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V} (D : FirstOrderDeformation W)

/-- Multiply first-order states, retaining the constant and linear coefficients. -/
def product (x : V × V) (n : ℤ) (y : V × V) : V × V :=
  (W.smul x.1 n y.1,
    W.smul x.1 n y.2 + W.smul x.2 n y.1 + D.smul₁ x.1 n y.1)

/-- Closure under every mode product of two elements of the subspace. -/
def ModeClosed (S : Submodule ℂ (V × V)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ n : ℤ, product D x n y ∈ S

/-- Reduction modulo the first-order parameter, restricted to a subspace. -/
def reduction (S : Submodule ℂ (V × V)) : S →ₗ[ℂ] V :=
  (LinearMap.fst ℂ V V).comp S.subtype

/-- Coefficients of the pure first-order states in a subspace. -/
def tangentKernel (S : Submodule ℂ (V × V)) : Submodule ℂ V :=
  S.comap (LinearMap.inr ℂ V V)

/-- Membership in the coefficient kernel is membership of the pure first-order lift. -/
@[simp] theorem mem_tangentKernel (S : Submodule ℂ (V × V)) (v : V) :
    v ∈ tangentKernel S ↔ (0, v) ∈ S := Iff.rfl

/-- Lift the acting state using surjectivity. Its product with a pure first-order
state proves that kernel coefficients form an ideal of the original VOA. -/
theorem tangentKernel_isIdeal (S : Submodule ℂ (V × V))
    (hclosed : ModeClosed D S) (hsurj : Function.Surjective (reduction S)) :
    W.IsIdeal (tangentKernel S) := by
  intro u v n hv
  obtain ⟨x, hx⟩ := hsurj u
  have hx' : (x : V × V).1 = u := hx
  have h := hclosed x x.property (0, v) hv n
  simpa [product, hx'] using h

/-- Simplicity and exclusion of the pure first-order vacuum kill the whole kernel. -/
theorem tangentKernel_eq_bot (S : Submodule ℂ (V × V)) (hsimple : W.IsSimple)
    (hclosed : ModeClosed D S) (hsurj : Function.Surjective (reduction S))
    (hsep : (0, W.vacuum) ∉ S) : tangentKernel S = ⊥ := by
  rcases hsimple.2 _ (tangentKernel_isIdeal D S hclosed hsurj) with h | h
  · exact h
  · exfalso
    apply hsep
    change W.vacuum ∈ tangentKernel S
    rw [h]
    trivial

/-- Zero coefficient kernel implies injectivity of reduction, by linear algebra. -/
theorem reduction_injective (S : Submodule ℂ (V × V))
    (hker : tangentKernel S = ⊥) : Function.Injective (reduction S) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  have hx1 : (x : V × V).1 = 0 := hx
  have hxk : (x : V × V).2 ∈ tangentKernel S := by
    change (0, (x : V × V).2) ∈ S
    simpa [← hx1] using x.property
  rw [hker, Submodule.mem_bot] at hxk
  apply Subtype.ext
  exact Prod.ext hx1 hxk

/-- Projection to one homogeneous grade, viewed in the whole state space. -/
noncomputable def gradePart (W : VertexOperatorAlgebra V) (n : ℤ) : V →ₗ[ℂ] V := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition W.grading
  exact (W.grading n).subtype.comp (gradedProj W n)

/-- The projected state belongs to its requested grade. -/
theorem gradePart_mem (n : ℤ) (v : V) : gradePart W n v ∈ W.grading n := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition W.grading
  unfold gradePart
  exact (gradedProj W n v).property

/-- Projection fixes a state already in the requested grade. -/
theorem gradePart_of_mem {n : ℤ} {v : V} (hv : v ∈ W.grading n) :
    gradePart W n v = v := by
  letI : DirectSum.Decomposition W.grading := W.isInternal.chooseDecomposition W.grading
  unfold gradePart
  exact gradedProj_of_mem W hv

/-- Taking homogeneous components in both coordinates preserves the subspace. -/
def GradeClosed (W : VertexOperatorAlgebra V) (S : Submodule ℂ (V × V)) : Prop :=
  ∀ x ∈ S, ∀ n : ℤ, (gradePart W n x.1, gradePart W n x.2) ∈ S

/-- Invert reduction to construct a trivializing change of coordinates.
The subspace and its separation condition must still be established concretely;
this theorem alone does not prove rigidity of any VOA. -/
theorem isTrivial_of_closed_lift (S : Submodule ℂ (V × V))
    (hsimple : W.IsSimple) (hclosed : ModeClosed D S)
    (hsurj : Function.Surjective (reduction S))
    (hsep : (0, W.vacuum) ∉ S) (hvac : (W.vacuum, 0) ∈ S)
    (hgrade : GradeClosed W S) : D.IsTrivial := by
  classical
  let e : S ≃ₗ[ℂ] V := LinearEquiv.ofBijective (reduction S)
    ⟨reduction_injective S (tangentKernel_eq_bot D S hsimple hclosed hsurj hsep), hsurj⟩
  let ψ : V →ₗ[ℂ] V := (LinearMap.snd ℂ V V).comp (S.subtype.comp e.symm.toLinearMap)
  have hfst (v : V) : (e.symm v : V × V).1 = v := e.apply_symm_apply v
  have hsnd (v : V) : (e.symm v : V × V).2 = ψ v := rfl
  have unique (x : V × V) (hx : x ∈ S) : e.symm x.1 = (⟨x, hx⟩ : S) := by
    apply e.injective
    exact e.apply_symm_apply x.1
  have hψvac : ψ W.vacuum = 0 := by
    have h := congrArg (fun x : S => (x : V × V).2) (unique (W.vacuum, 0) hvac)
    exact h
  have hψgrade : GradePreserving W ψ := by
    intro n v hv
    have hg := hgrade (e.symm v) (e.symm v).property n
    rw [hfst v, gradePart_of_mem hv, hsnd v] at hg
    have hu := congrArg (fun x : S => (x : V × V).2) (unique (v, gradePart W n (ψ v)) hg)
    change ψ v = gradePart W n (ψ v) at hu
    rw [hu]
    exact gradePart_mem n (ψ v)
  have hψmode (u v : V) (n : ℤ) :
      ψ (W.smul u n v) = W.smul u n (ψ v) + W.smul (ψ u) n v + D.smul₁ u n v := by
    have hm := hclosed (e.symm u) (e.symm u).property (e.symm v) (e.symm v).property n
    have hu := congrArg (fun x : S => (x : V × V).2)
      (unique (product D (e.symm u) n (e.symm v)) hm)
    simpa only [product, hfst, hsnd] using hu
  refine ⟨-ψ, ?_, ?_, ?_⟩
  · simpa using congrArg Neg.neg hψvac
  · intro n v hv
    exact (W.grading n).neg_mem (hψgrade n v hv)
  · intro u n v
    change D.smul₁ u n v = _
    simp only [LinearMap.neg_apply]
    rw [hψmode u v n]
    simp only [PreVertexAlgebra.smul_def, map_neg, mode_neg, LinearMap.neg_apply]
    abel


/-- A generating set reaches every state from the vacuum by linear combinations
and modes of generators. This condition refers only to the original VOA. -/
def ModeGenerating (W : VertexOperatorAlgebra V) (G : Set V) : Prop :=
  ∀ S : Submodule ℂ V, W.vacuum ∈ S → G ⊆ S →
    (∀ g ∈ G, ∀ v ∈ S, ∀ n : ℤ, W.smul g n v ∈ S) → S = ⊤

/-- The smallest subspace containing the undeformed vacuum and generators and
closed under deformed products and homogeneous projections. Intersections make
this an actual construction for every deformation, without an existence assumption. -/
noncomputable def generatedCarrier (G : Set V) : Submodule ℂ (V × V) :=
  sInf {S | (W.vacuum, 0) ∈ S ∧ (∀ g ∈ G, (g, 0) ∈ S) ∧
    ModeClosed D S ∧ GradeClosed W S}

/-- The constructed carrier contains the ordinary vacuum. -/
theorem generatedCarrier_vacuum (G : Set V) : (W.vacuum, 0) ∈ generatedCarrier D G := by
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.1

/-- Every chosen generator has its pure constant lift in the constructed carrier. -/
theorem generatedCarrier_generator (G : Set V) {g : V} (hg : g ∈ G) :
    (g, 0) ∈ generatedCarrier D G := by
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2.1 g hg

/-- Intersections preserve closure under deformed mode products. -/
theorem generatedCarrier_modeClosed (G : Set V) : ModeClosed D (generatedCarrier D G) := by
  intro x hx y hy n
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2.2.1 x (Submodule.mem_sInf.mp hx S hS) y (Submodule.mem_sInf.mp hy S hS) n

/-- Intersections preserve closure under homogeneous projections. -/
theorem generatedCarrier_gradeClosed (G : Set V) : GradeClosed W (generatedCarrier D G) := by
  intro x hx n
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.2.2.2 x (Submodule.mem_sInf.mp hx S hS) n

/-- Original generation implies surjectivity of reduction for the constructed
carrier. No triviality or regularity assumption on the deformation is used. -/
theorem generatedCarrier_surjective (G : Set V) (hgen : ModeGenerating W G) :
    Function.Surjective (reduction (generatedCarrier D G)) := by
  let S := generatedCarrier D G
  let R := S.map (LinearMap.fst ℂ V V)
  have hR : R = ⊤ := by
    apply hgen
    · exact Submodule.mem_map.mpr ⟨(W.vacuum, 0), generatedCarrier_vacuum D G, rfl⟩
    · intro g hg
      exact Submodule.mem_map.mpr ⟨(g, 0), generatedCarrier_generator D G hg, rfl⟩
    · intro g hg v hv n
      obtain ⟨x, hx, hxv⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨product D (g, 0) n x,
        generatedCarrier_modeClosed D G (g, 0) (generatedCarrier_generator D G hg) x hx n, ?_⟩
      change W.smul g n x.1 = W.smul g n v
      change x.1 = v at hxv
      rw [hxv]
  intro v
  have hv : v ∈ R := by rw [hR]; trivial
  obtain ⟨x, hx, hxv⟩ := Submodule.mem_map.mp hv
  exact ⟨⟨x, hx⟩, hxv⟩

/-- Reconstruction for the explicit generated carrier: only separation of the
pure first-order vacuum remains once simplicity and original generation are known.
This is a reduction, not a proof that separation holds for regular deformations. -/
theorem isTrivial_of_generated_separation (G : Set V) (hsimple : W.IsSimple)
    (hgen : ModeGenerating W G) (hsep : (0, W.vacuum) ∉ generatedCarrier D G) :
    D.IsTrivial :=
  isTrivial_of_closed_lift D (generatedCarrier D G) hsimple
    (generatedCarrier_modeClosed D G) (generatedCarrier_surjective D G hgen) hsep
    (generatedCarrier_vacuum D G) (generatedCarrier_gradeClosed D G)

end VOA.Deform.Reconstruction
