/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Huang.AssocJacobiBoundary
import VOA.Classification.COne.McRaeM1Cover

/-! # Genuine binary products of weak VOA modules

The action is coordinatewise on the actual vector-space product. All weak-module
axioms are proved. The genuine weak-submodule lattice has the usual comparable
submodule separation by intersection with the first factor and projection to the
second; hence products of finite-length weak modules have finite length.
-/

namespace VOA.WeakModuleProduct
open Module (End)
open scoped BigOperators
open VOA.Huang.AssocJacobiBoundary
open VOA.Classification.COne.PlusSplitting VOA.Classification.COne.McRaeM1
open VOA.Huang.LogRemovalAdmissible
open VOA.Classification.COne
universe u
variable {V M N R : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup R] [Module ℂ R] {W : VertexOperatorAlgebra V}

noncomputable def field (A : WeakModule W M) (B : WeakModule W N) :
    V →ₗ[ℂ] (End ℂ (M × N))⟦z^±⟧ where
  toFun u p := (A.YM u p).prodMap (B.YM u p)
  map_add' u v := by
    funext p
    apply LinearMap.ext
    intro x
    simp [map_add]
  map_smul' s u := by
    funext p
    apply LinearMap.ext
    intro x
    simp [map_smul]

@[simp] theorem mode_field (A : WeakModule W M) (B : WeakModule W N) (u : V) (p : ℤ)
    (x : M × N) : mode (field A B u) p x =
      (mode (A.YM u) p x.1,mode (B.YM u) p x.2) := rfl

theorem field_truncated (A : WeakModule W M) (B : WeakModule W N) : Truncated (field A B) := by
  intro u x
  obtain ⟨K,hK⟩ := A.truncation u x.1
  obtain ⟨L,hL⟩ := B.truncation u x.2
  exact ⟨max K L,fun p hp => by
    rw [mode_field,hK p (le_trans (le_max_left _ _) hp),hL p (le_trans (le_max_right _ _) hp)]
    rfl⟩

theorem field_vacuum (A : WeakModule W M) (B : WeakModule W N) : field A B W.vacuum = 1 := by
  refine FormalDist.ext fun p => ?_
  apply LinearMap.ext
  intro x
  simp only [field,LinearMap.coe_mk,AddHom.coe_mk,A.vacuum_YM,B.vacuum_YM,
    FormalDist.one_apply]
  split_ifs <;> rfl

theorem field_jacobi (A : WeakModule W M) (B : WeakModule W N) (u v : V)
    (x : M × N) (ell m n : ℤ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
      (mode (field A B u) (ell+m-i) (mode (field A B v) (n+i) x) -
        negOnePow ell • mode (field A B v) (ell+n-i) (mode (field A B u) (m+i) x))) =
      ∑ᶠ i : ℤ, cbz m i • mode (field A B (W.smul u (ell+i) v)) (m+n-i) x := by
  have htr := field_truncated A B
  have hL : (Function.support fun i : ℤ => (negOnePow i * cbz ell i) •
      (mode (field A B u) (ell+m-i) (mode (field A B v) (n+i) x) -
        negOnePow ell • mode (field A B v) (ell+n-i) (mode (field A B u) (m+i) x))).Finite := by
    refine ((Puv_fin htr u v x ell m n).union (Pvu_fin htr u v x ell m n)).subset ?_
    intro i hi
    by_contra hc
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hc hi
    apply hi
    rw [smul_sub,hc.1,smul_comm,hc.2,smul_zero,sub_zero]
  have hR := BR_fin (W := W) (YM := field A B) u v x ell m n
  apply Prod.ext
  · change (LinearMap.fst ℂ M N) _ = (LinearMap.fst ℂ M N) _
    rw [map_finsum (LinearMap.fst ℂ M N) hL,map_finsum (LinearMap.fst ℂ M N) hR]
    simpa only [map_smul,map_sub,mode_field,LinearMap.fst_apply] using A.jacobi u v x.1 ell m n
  · change (LinearMap.snd ℂ M N) _ = (LinearMap.snd ℂ M N) _
    rw [map_finsum (LinearMap.snd ℂ M N) hL,map_finsum (LinearMap.snd ℂ M N) hR]
    simpa only [map_smul,map_sub,mode_field,LinearMap.snd_apply] using B.jacobi u v x.2 ell m n

/-- The actual coordinatewise product weak module. -/
noncomputable def prod (A : WeakModule W M) (B : WeakModule W N) : WeakModule W (M × N) where
  YM := field A B
  vacuum_YM := field_vacuum A B
  truncation := field_truncated A B
  jacobi := field_jacobi A B

noncomputable def fstHom (A : WeakModule W M) (B : WeakModule W N) : (prod A B).Hom A where
  toLinearMap := LinearMap.fst ℂ M N
  map_act _ _ _ := rfl

noncomputable def sndHom (A : WeakModule W M) (B : WeakModule W N) : (prod A B).Hom B where
  toLinearMap := LinearMap.snd ℂ M N
  map_act _ _ _ := rfl

noncomputable def inlHom (A : WeakModule W M) (B : WeakModule W N) : A.Hom (prod A B) where
  toLinearMap := (LinearMap.id : M →ₗ[ℂ] M).prod (0 : M →ₗ[ℂ] N)
  map_act u p x := by
    change (mode (A.YM u) p x,0) = (mode (A.YM u) p x,mode (B.YM u) p 0)
    rw [map_zero]

noncomputable def pairHom {C : WeakModule W R} {A : WeakModule W M} {B : WeakModule W N}
    (f : C.Hom A) (g : C.Hom B) : C.Hom (prod A B) where
  toLinearMap := f.toLinearMap.prod g.toLinearMap
  map_act u p x := by
    change (f.toLinearMap (C.act u p x),g.toLinearMap (C.act u p x)) =
      (A.act u p (f.toLinearMap x),B.act u p (g.toLinearMap x))
    rw [f.map_act,g.map_act]

private theorem comparable_separation (A : WeakModule W M) (B : WeakModule W N)
    {P Q : Submodule (modeAlg (prod A B)) (M × N)} (hPQ : P ≤ Q)
    (h₁ : modeComap (inlHom A B) P = modeComap (inlHom A B) Q)
    (h₂ : modeMap (sndHom A B) P = modeMap (sndHom A B) Q) : P = Q := by
  apply le_antisymm hPQ
  intro x hx
  have hs : x.2 ∈ modeMap (sndHom A B) P := by rw [h₂]; exact ⟨x,hx,rfl⟩
  obtain ⟨y,hy,he⟩ := hs
  change y.2 = x.2 at he
  have hxy : x-y ∈ Q := Q.sub_mem hx (hPQ hy)
  have hs0 : x.2-y.2 = 0 := by change x.2-y.2=0; rw [he,sub_self]
  have hi : (x.1-y.1,0) ∈ Q := by simpa only [Prod.sub_def,hs0] using hxy
  have hp : x.1-y.1 ∈ modeComap (inlHom A B) P := by rw [h₁]; exact hi
  have hp' : (x.1-y.1,0) ∈ P := hp
  have hsum : (x.1-y.1,0)+y = x := by apply Prod.ext <;> simp [he]
  rw [← hsum]
  exact P.add_mem hp' hy

private theorem separation_strictMono (A : WeakModule W M) (B : WeakModule W N) :
    StrictMono (fun P : Submodule (modeAlg (prod A B)) (M × N) =>
      (modeComap (inlHom A B) P,modeMap (sndHom A B) P)) := by
  intro P Q h
  apply lt_iff_le_and_ne.mpr
  refine ⟨⟨modeComap_mono (inlHom A B) h.le,modeMap_mono (sndHom A B) h.le⟩,?_⟩
  intro he
  exact h.ne (comparable_separation A B h.le (congrArg Prod.fst he) (congrArg Prod.snd he))

/-- Products of genuinely finite-length weak modules have finite length for their own
actual mode algebra. -/
theorem finiteLength_prod (A : WeakModule W M) (B : WeakModule W N)
    (hA : IsFiniteLength (modeAlg A) M) (hB : IsFiniteLength (modeAlg B) N) :
    IsFiniteLength (modeAlg (prod A B)) (M × N) := by
  haveI : IsNoetherian (modeAlg A) M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  haveI : IsArtinian (modeAlg A) M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).2
  haveI : IsNoetherian (modeAlg B) N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hB).1
  haveI : IsArtinian (modeAlg B) N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hB).2
  haveI : WellFoundedLT (Submodule (modeAlg A) M) := inferInstance
  haveI : WellFoundedGT (Submodule (modeAlg A) M) := isNoetherian_iff'.mp inferInstance
  haveI : WellFoundedLT (Submodule (modeAlg B) N) := inferInstance
  haveI : WellFoundedGT (Submodule (modeAlg B) N) := isNoetherian_iff'.mp inferInstance
  haveI : WellFoundedLT (Submodule (modeAlg (prod A B)) (M × N)) :=
    (separation_strictMono A B).wellFoundedLT
  haveI : WellFoundedGT (Submodule (modeAlg (prod A B)) (M × N)) :=
    (separation_strictMono A B).wellFoundedGT
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff'.mpr inferInstance,inferInstance⟩

end VOA.WeakModuleProduct
