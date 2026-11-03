/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchLUUniversalIrr

/-!
# Functoriality of the Dong–Jiang module `M(·)` in its bottom (the `hfin`-free core).

The generalized-Verma carrier `M(U) = ⨁ₙ (A_{n,0}(𝒱) ⊗_{A(𝒱)} U)` is functorial in the bottom `U`:
a `ρ`-intertwining `ℂ`-linear equivalence `e : U₁ ≅ U₂` induces `M(e) = ⨁ₙ (id ⊗ e)`, a `ℂ`-linear
equivalence `M(U₁) ≅ M(U₂)`.  This file builds that map and its two structural facts (it commutes
with the projection from the cover; it is functorial), the `hL0`-free heart of the DJ-track
`isoInvariant`.  The `𝒱`-action naturality and the `J`-transport (which need the graded structure)
are assembled downstream once `hL0` is available.

Mirrors the MU-track `MU.functorEquiv` (`ZhuVermaAnArchHoleMuEquiv`), but for the DJ carrier, whose
balancing `[x∗a]⊗w − [x]⊗ρ([a])w` mixes **both** tensor factors — so well-definedness genuinely uses
`e`'s intertwining of `ρ` (`djFunctorCover_maps_balancing`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), `sorry`-free, `pbw`-free; no existing file
mutated.

## References
Dong–Jiang math/0601626 Prop 3.4/3.5.  `ZhuVermaAnArchDJCarrier` (`DJCover`, `djBalancing`,
`DJPiece`, `mkDJPiece`, `mkDJPiece_balance`), `ZhuVermaAnArchDJCarrierGraded` (`DJCarrier`, `incl`),
`ZhuVermaAnArchHoleMuEquiv` (`MU.functorEquiv`, the template).
-/

namespace VOA

open scoped BigOperators TensorProduct
open VertexOperatorAlgebra

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section
variable {W : VertexOperatorAlgebra 𝒱}

/-- **`A(𝒱)`-equivariance of a bottom equivalence** — the data `M(·)` is functorial against: a
`ℂ`-linear equivalence of bottoms intertwining the `AmMod` action `ρ`. -/
structure AmModHom (U₁ U₂ : AmMod W 0) where
  /-- The underlying `ℂ`-linear equivalence of the carriers. -/
  toLinearEquiv : U₁.carrier ≃ₗ[ℂ] U₂.carrier
  /-- It intertwines the `A(𝒱)`-actions. -/
  map_ρ : ∀ (g : AnFull W 0) (w : U₁.carrier),
    toLinearEquiv (U₁.ρ g w) = U₂.ρ g (toLinearEquiv w)

/-- The **cover map** `id_{A_{n,0}} ⊗ e : A_{n,0}(𝒱) ⊗ U₁ ≅ A_{n,0}(𝒱) ⊗ U₂` (action on the second
factor only). -/
noncomputable def djFunctorCover (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ) :
    DJCover W U₁ n ≃ₗ[ℂ] DJCover W U₂ n :=
  TensorProduct.congr (LinearEquiv.refl ℂ (AnmFull W n 0)) e.toLinearEquiv

@[simp] theorem djFunctorCover_tmul (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ)
    (a : AnmFull W n 0) (w : U₁.carrier) :
    djFunctorCover U₁ U₂ e n (a ⊗ₜ[ℂ] w) = a ⊗ₜ[ℂ] e.toLinearEquiv w := by
  simp only [djFunctorCover, TensorProduct.congr_tmul, LinearEquiv.refl_apply]

/-- **The cover map sends the balancing submodule onto the balancing submodule** — the
well-definedness of the functor, using `e`'s `ρ`-intertwining. -/
theorem djFunctorCover_maps_balancing (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ) :
    (djBalancing W U₁ n).map (djFunctorCover U₁ U₂ e n).toLinearMap = djBalancing W U₂ n := by
  simp only [djBalancing, Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_image, djBalancingSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨x, a, w, rfl⟩, rfl⟩
    exact ⟨x, a, e.toLinearEquiv w, by
      simp only [LinearEquiv.coe_coe, map_sub, djFunctorCover_tmul, e.map_ρ]⟩
  · rintro ⟨x, a, w, rfl⟩
    exact ⟨_, ⟨x, a, e.toLinearEquiv.symm w, rfl⟩, by
      simp only [LinearEquiv.coe_coe, map_sub, djFunctorCover_tmul, e.map_ρ,
        LinearEquiv.apply_symm_apply]⟩

/-- **The level-`n` functor piece** `M(e)_n : M(U₁)(n) ≅ M(U₂)(n)` (`id ⊗ e` descended through the
balancing). -/
noncomputable def djFunctorPiece (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ) :
    DJPiece W U₁ n ≃ₗ[ℂ] DJPiece W U₂ n :=
  Submodule.Quotient.equiv (djBalancing W U₁ n) (djBalancing W U₂ n)
    (djFunctorCover U₁ U₂ e n) (djFunctorCover_maps_balancing U₁ U₂ e n)

@[simp] theorem djFunctorPiece_mk (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ)
    (z : DJCover W U₁ n) :
    djFunctorPiece U₁ U₂ e n (mkDJPiece W U₁ n z) = mkDJPiece W U₂ n (djFunctorCover U₁ U₂ e n z) := by
  rw [djFunctorPiece, mkDJPiece, mkDJPiece, Submodule.Quotient.equiv_apply]
  rfl

/-- **The DJ functor map** `M(e) = ⨁ₙ (id ⊗ e) : M(U₁) ≅ M(U₂)` as a `ℂ`-linear equivalence. -/
noncomputable def djFunctorEquiv (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) :
    DJCarrier W U₁ ≃ₗ[ℂ] DJCarrier W U₂ :=
  DirectSum.congrLinearEquiv (fun n => djFunctorPiece U₁ U₂ e n)

@[simp] theorem djFunctorEquiv_incl (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ)
    (z : DJPiece W U₁ n) :
    djFunctorEquiv U₁ U₂ e (DJCarrier.incl W U₁ n z)
      = DJCarrier.incl W U₂ n (djFunctorPiece U₁ U₂ e n z) := by
  rw [djFunctorEquiv, DJCarrier.incl, DJCarrier.incl,
    show (DirectSum.congrLinearEquiv (fun n => djFunctorPiece U₁ U₂ e n))
          (DirectSum.lof ℂ ℕ (DJPiece W U₁) n z)
        = DirectSum.lmap (fun i => ((djFunctorPiece U₁ U₂ e i).toLinearMap))
          (DirectSum.lof ℂ ℕ (DJPiece W U₁) n z)
      from congrFun (DirectSum.coe_congrLinearEquiv (fun n => djFunctorPiece U₁ U₂ e n)) _,
    DirectSum.lmap_lof]
  rfl

/-! ## The `𝒱`-action naturality: `M(e)` intertwines `djModeZero`

The DJ mode `uₚ` acts on the **first** tensor factor (`djCoverAct = leftGen ⊗ id`) and `M(e) = id ⊗ e`
on the second; they commute.  On a generator both `djMode_apply_tmul` and `M(e)` leave the other
factor untouched, so `M(e)(uₚ·z) = uₚ·M(e)(z)`.  Extended over the direct sum, the balanced tensor
and the grade decomposition of `a` — verbatim the shape of `oLevUnivMap_intertwine`. -/

/-- Naturality on an elementary generator with homogeneous `a`. -/
theorem djFunctorEquiv_natural_tmul (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂)
    (k p : ℤ) {a : 𝒱} (ha : a ∈ W.grading k) (n : ℕ) (v : 𝒱) (w : U₁.carrier) :
    djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p a
        (DJCarrier.incl W U₁ n (mkDJPiece W U₁ n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w))))
      = djModeZero W U₂ p a (djFunctorEquiv U₁ U₂ e
          (DJCarrier.incl W U₁ n (mkDJPiece W U₁ n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))) := by
  have hrhs : djFunctorEquiv U₁ U₂ e
      (DJCarrier.incl W U₁ n (mkDJPiece W U₁ n (mkAnmFull W n 0 v ⊗ₜ[ℂ] w)))
      = DJCarrier.incl W U₂ n (mkDJPiece W U₂ n (mkAnmFull W n 0 v ⊗ₜ[ℂ] e.toLinearEquiv w)) := by
    rw [djFunctorEquiv_incl, djFunctorPiece_mk, djFunctorCover_tmul]
  rw [hrhs]
  by_cases hN : 0 ≤ muTargetLevel k p n
  · obtain ⟨N, hNeq⟩ : ∃ N : ℕ, muTargetLevel k p n = (N : ℤ) :=
      ⟨(muTargetLevel k p n).toNat, (Int.toNat_of_nonneg hN).symm⟩
    simp only [djModeZero]
    rw [djMode_apply_tmul U₁ (djActionDescent_zero W) p ha hNeq,
      djMode_apply_tmul U₂ (djActionDescent_zero W) p ha hNeq,
      djFunctorEquiv_incl, djFunctorPiece_mk, djFunctorCover_tmul]
  · have hp : k + (n : ℤ) ≤ p := by simp only [muTargetLevel] at hN; omega
    simp only [djModeZero]
    rw [djMode_incl_eq_zero U₁ (djActionDescent_zero W) ha hp, map_zero,
      djMode_incl_eq_zero U₂ (djActionDescent_zero W) ha hp]

/-- Naturality for homogeneous `a`, all `x`. -/
theorem djFunctorEquiv_natural_homog (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂)
    (k p : ℤ) {a : 𝒱} (ha : a ∈ W.grading k) (x : DJCarrier W U₁) :
    djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p a x)
      = djModeZero W U₂ p a (djFunctorEquiv U₁ U₂ e x) := by
  have hcomp : (djFunctorEquiv U₁ U₂ e).toLinearMap.comp (djModeZero W U₁ p a)
      = (djModeZero W U₂ p a).comp (djFunctorEquiv U₁ U₂ e).toLinearMap := by
    refine DirectSum.linearMap_ext ℂ (fun n => ?_)
    refine djPiece_ext (fun v w => ?_)
    simp only [LinearMap.comp_apply]
    exact djFunctorEquiv_natural_tmul U₁ U₂ e k p ha n v w
  have := LinearMap.congr_fun hcomp x
  simpa only [LinearMap.comp_apply] using this

/-- **`M(e)` intertwines the `𝒱`-action** (`djModeZero`) — the DJ-track `MUActionNatural`. -/
theorem djFunctorEquiv_natural (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (p : ℤ) (a : 𝒱)
    (x : DJCarrier W U₁) :
    djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p a x)
      = djModeZero W U₂ p a (djFunctorEquiv U₁ U₂ e x) := by
  refine reduce_homogeneous W
    (P := fun a => djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p a x)
      = djModeZero W U₂ p a (djFunctorEquiv U₁ U₂ e x)) ?_ ?_ ?_ a
  · intro k a ha
    exact djFunctorEquiv_natural_homog U₁ U₂ e k p ha x
  · change djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p (0 : 𝒱) x)
      = djModeZero W U₂ p (0 : 𝒱) (djFunctorEquiv U₁ U₂ e x)
    have h1 : djModeZero W U₁ p (0 : 𝒱) = 0 := by
      have := djMode_smul_acting U₁ (djActionDescent_zero W) p (0 : ℂ) W.vacuum
      rwa [zero_smul, zero_smul] at this
    have h2 : djModeZero W U₂ p (0 : 𝒱) = 0 := by
      have := djMode_smul_acting U₂ (djActionDescent_zero W) p (0 : ℂ) W.vacuum
      rwa [zero_smul, zero_smul] at this
    rw [h1, LinearMap.zero_apply, map_zero, h2, LinearMap.zero_apply]
  · intro b c hb hc
    change djFunctorEquiv U₁ U₂ e (djModeZero W U₁ p (b + c) x)
      = djModeZero W U₂ p (b + c) (djFunctorEquiv U₁ U₂ e x)
    rw [show djModeZero W U₁ p (b + c) = djModeZero W U₁ p b + djModeZero W U₁ p c from
        djMode_add_acting U₁ (djActionDescent_zero W) p b c,
      show djModeZero W U₂ p (b + c) = djModeZero W U₂ p b + djModeZero W U₂ p c from
        djMode_add_acting U₂ (djActionDescent_zero W) p b c,
      LinearMap.add_apply, map_add, hb, hc, LinearMap.add_apply]

/-- **`M(e)` is graded**: it carries the level-`n` piece `M(U₁)(n)` onto `M(U₂)(n)`.  Needed to
transport bottom-triviality of `J` across the functor. -/
theorem djFunctorEquiv_maps_deg (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ) :
    Submodule.map (djFunctorEquiv U₁ U₂ e).toLinearMap (DJCarrier.deg W U₁ n)
      = DJCarrier.deg W U₂ n := by
  ext z
  simp only [Submodule.mem_map, DJCarrier.deg, LinearMap.mem_range, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨djFunctorPiece U₁ U₂ e n y, (djFunctorEquiv_incl U₁ U₂ e n y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨DJCarrier.incl W U₁ n ((djFunctorPiece U₁ U₂ e n).symm y),
      ⟨(djFunctorPiece U₁ U₂ e n).symm y, rfl⟩, ?_⟩
    rw [djFunctorEquiv_incl, LinearEquiv.apply_symm_apply]

/-- The inverse `AmModHom` (its `ρ`-intertwining is `e`'s, applied to `e.symm`). -/
noncomputable def AmModHom.symm {U₁ U₂ : AmMod W 0} (e : AmModHom U₁ U₂) : AmModHom U₂ U₁ where
  toLinearEquiv := e.toLinearEquiv.symm
  map_ρ g w := by
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply, e.map_ρ, LinearEquiv.apply_symm_apply]

/-- The inverse functor map intertwines the `𝒱`-action (from `djFunctorEquiv_natural`, applied to
`e.symm y`). -/
theorem djFunctorEquiv_symm_natural (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (p : ℤ) (a : 𝒱)
    (y : DJCarrier W U₂) :
    (djFunctorEquiv U₁ U₂ e).symm (djModeZero W U₂ p a y)
      = djModeZero W U₁ p a ((djFunctorEquiv U₁ U₂ e).symm y) := by
  apply (djFunctorEquiv U₁ U₂ e).injective
  rw [LinearEquiv.apply_symm_apply, djFunctorEquiv_natural, LinearEquiv.apply_symm_apply]

/-- The inverse functor map is graded (carries `M(U₂)(n)` onto `M(U₁)(n)`). -/
theorem djFunctorEquiv_symm_maps_deg (U₁ U₂ : AmMod W 0) (e : AmModHom U₁ U₂) (n : ℕ) :
    Submodule.map (djFunctorEquiv U₁ U₂ e).symm.toLinearMap (DJCarrier.deg W U₂ n)
      = DJCarrier.deg W U₁ n := by
  rw [← djFunctorEquiv_maps_deg U₁ U₂ e n, ← Submodule.map_comp]
  rw [show (djFunctorEquiv U₁ U₂ e).symm.toLinearMap.comp (djFunctorEquiv U₁ U₂ e).toLinearMap
        = LinearMap.id from by ext x; simp, Submodule.map_id]

/-! ## The bottom bridge: an `A(𝒱)`-iso of bottoms is an `AmModHom` of the level-0 modules -/

/-- **`AModEquiv` of bottoms ⟹ `AmModHom`.**  A `𝒱`-module `A(𝒱)`-iso `ψ : Ω(P) ≅ Ω(Q)` is, through
`AMod.toAmModZero_ρ`, an `AmMod W 0`-equivariant equivalence `pBotAmMod P ≅ pBotAmMod Q` (the `AmMod`
action on generators `mkAnFull W 0 x` is `U.ρ (mk W x)`, and `ψ` intertwines those). -/
noncomputable def amModHomOfBottomEquiv {P Q : LWModule W}
    (ψ : AModEquiv W P.toAMod Q.toAMod) : AmModHom (pBotAmMod P) (pBotAmMod Q) where
  toLinearEquiv := ψ.toLinearEquiv
  map_ρ g w := by
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (OnFull W 0) g
    show ψ.toLinearEquiv ((pBotAmMod P).ρ (mkAnFull W 0 x) w)
      = (pBotAmMod Q).ρ (mkAnFull W 0 x) (ψ.toLinearEquiv w)
    simp only [pBotAmMod, AMod.toAmModZero_ρ]
    exact ψ.map_ρ (mk W x) w

end

end VOA
