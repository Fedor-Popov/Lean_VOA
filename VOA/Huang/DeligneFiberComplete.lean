/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.DeligneFiberSquareZero

/-!
# Deligne's fiber functor — completeness of an orthonormal frame

Let `G` be a lax braided functor (commutative algebra `A` in `Ind(C)`), `X` an object with
`Λ^{n+1} X = 0`, and `(e, f)` an **orthonormal `n`-family**: `e_j ∈ G X`, `f_i ∈ G Xᘁ`,
`⟨f_i, e_j⟩ = δ_ij`.  Then the frame is **complete**: `Σ_j e_j f_j = G(η_X)(1)` in `G(X ⊗ Xᘁ)`, and
consequently `(a_j) ↦ Σ_j e_j a_j : G(Z)^n → G(X ⊗ Z)` is bijective for every `Z`
(`A ⊗ X ≅ A^n`).

Proof: the "tailed vector" `P = η − Σ e_j f_j` becomes an honest vector `(0, P)` of the square-zero
extension `sqZero G Xᘁ`, orthogonal to every `f_i` (zigzag identity); `eq_zero_of_orthonormal`
(Leibniz formula + `Λ^{n+1} X = 0`) kills it.

* `coordZ`, `coordZ_frameMap` (coordinates `C_i`), `contr_eta`, `contr_prod`;
* `frame_complete` — `η = Σ_j e_j f_j`;
* `frameMap_bijective_of_orthonormal`;
* named Prop **`OrthonormalFrameExists`** and
  `frameFunctorExists_of_orthonormalFrameExists : OrthonormalFrameExists → FrameFunctorExists`,
  hence `symmetricFiberFunctorExists_of_orthonormalFrameExists`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace VOA.Huang.TensorCat.DeligneFiber

open CategoryTheory MonoidalCategory Limits Module Functor.LaxMonoidal Cardinal
open scoped TensorProduct

universe v u

section Complete

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [SymmetricCategory C] [RightRigidCategory C]
  (G : C ⥤ ModuleCat.{0} ℂ) [G.LaxBraided] [G.Additive] [G.Linear ℂ]

theorem mu_unit_left_eq {Z : C} (b : G.obj Z) :
    (μ G (𝟙_ C) Z).hom ((ε G).hom 1 ⊗ₜ b) = (G.map (λ_ Z).inv).hom b := by
  have h := unit_left_apply G 1 b
  rw [one_smul] at h
  conv_rhs => rw [← h]
  rw [map_map_apply, Iso.hom_inv_id, G.map_id]
  rfl

theorem mu_unit_right_eq {Z : C} (b : G.obj Z) :
    (μ G Z (𝟙_ C)).hom (b ⊗ₜ (ε G).hom 1) = (G.map (ρ_ Z).inv).hom b := by
  have h := unit_right_apply G 1 b
  rw [one_smul] at h
  conv_rhs => rw [← h]
  rw [map_map_apply, Iso.hom_inv_id, G.map_id]
  rfl

/-- The coordinate `C_f(w) ∈ G Z` of `w ∈ G(X ⊗ Z)` along a covector `f ∈ G Xᘁ`. -/
def contrZ (X Z : C) : Xᘁ ⊗ (X ⊗ Z) ⟶ Z := (α_ _ _ _).inv ≫ (ε_ X Xᘁ ▷ Z) ≫ (λ_ Z).hom

def coordZ {X Z : C} (g : G.obj Xᘁ) (w : G.obj (X ⊗ Z)) : G.obj Z :=
  (G.map (contrZ X Z)).hom ((μ G Xᘁ (X ⊗ Z)).hom (g ⊗ₜ w))

theorem coordZ_mu {X Z : C} (g : G.obj Xᘁ) (x : G.obj X) (a : G.obj Z) :
    coordZ G g ((μ G X Z).hom (x ⊗ₜ a)) = act G (pairG G g x) a := by
  simp only [coordZ, contrZ, map_comp_apply]
  rw [μ_assoc_inv_apply, μ_whiskerRight_apply]
  rfl

/-- `G(α⁻¹ ≫ ε ▷ Xᘁ)(g · η) = G(λ⁻¹) g` (zigzag). -/
theorem contr_eta {X : C} (g : G.obj Xᘁ) :
    (G.map ((α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ))).hom
        ((μ G Xᘁ (X ⊗ Xᘁ)).hom (g ⊗ₜ (G.map (η_ X Xᘁ)).hom ((ε G).hom 1))) = (G.map (λ_ Xᘁ).inv).hom g := by
  rw [← μ_whiskerLeft_apply, mu_unit_right_eq, map_map_apply, map_map_apply]
  have hz := ExactPairing.coevaluation_evaluation X Xᘁ
  rw [show (ρ_ Xᘁ).inv ≫ Xᘁ ◁ η_ X Xᘁ ≫ (α_ Xᘁ X Xᘁ).inv ≫ ε_ X Xᘁ ▷ Xᘁ = (λ_ Xᘁ).inv by
    rw [hz, Iso.inv_hom_id_assoc]]

theorem contr_prod {X : C} (g : G.obj Xᘁ) (x : G.obj X) (h : G.obj Xᘁ) :
    (G.map ((α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ))).hom
        ((μ G Xᘁ (X ⊗ Xᘁ)).hom (g ⊗ₜ (μ G X Xᘁ).hom (x ⊗ₜ h))) =
      (μ G (𝟙_ C) Xᘁ).hom (pairG G g x ⊗ₜ h) := by
  rw [map_comp_apply, μ_assoc_inv_apply, μ_whiskerRight_apply]
  rfl

variable {X : C} {n : ℕ} (e : Fin n → G.obj X) (f : Fin n → G.obj Xᘁ)

/-- The defect `P = η − Σ_j e_j f_j ∈ G(X ⊗ Xᘁ)`. -/
def defect : G.obj (X ⊗ Xᘁ) :=
  (G.map (η_ X Xᘁ)).hom ((ε G).hom 1) - ∑ j, (μ G X Xᘁ).hom (e j ⊗ₜ f j)

/-- **Completeness**: `η = Σ_j e_j f_j`. -/
theorem frame_complete (hA : antisym X (n + 1) = 0)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) :
    defect G e f = 0 := by
  let incl : ∀ Y : C, G.obj Y → (sqZero G Xᘁ).obj Y := fun Y x => (x, 0)
  have hpair : ∀ (g : G.obj Xᘁ) (y : G.obj X × G.obj (X ⊗ Xᘁ)),
      pairG (sqZero G Xᘁ) (incl _ g) y = (pairG G g y.1,
        (G.map ((α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ))).hom ((μ G Xᘁ (X ⊗ Xᘁ)).hom (g ⊗ₜ y.2))) := by
    intro g y
    simp only [pairG, sqZero_μ_apply, sqZero_map_fst, mulSnd, incl, TensorProduct.zero_tmul, map_zero,
      add_zero, map_comp_apply]
  have horthH : ∀ i j, pairG (sqZero G Xᘁ) (incl _ (f i)) (incl _ (e j)) = if i = j then (ε (sqZero G Xᘁ)).hom 1 else 0 := by
    intro i j
    rw [hpair]
    simp only [incl, TensorProduct.tmul_zero, map_zero, horth, sqZero_ε_apply]
    split_ifs <;> rfl
  have hy : ∀ i, pairG (sqZero G Xᘁ) (incl _ (f i)) ((0 : G.obj X), defect G e f) = 0 := by
    intro i
    rw [hpair]
    simp only [pairG, TensorProduct.tmul_zero, map_zero, defect, TensorProduct.tmul_sub,
      TensorProduct.tmul_sum, map_sub, map_sum]
    rw [contr_eta]
    simp only [contr_prod]
    have : ∑ j, (μ G (𝟙_ C) Xᘁ).hom (pairG G (f i) (e j) ⊗ₜ f j) = (G.map (λ_ Xᘁ).inv).hom (f i) := by
      simp only [horth]
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), TensorProduct.zero_tmul, map_zero])
        (by simp), if_pos rfl, mu_unit_left_eq]
    rw [this, sub_self]
    rfl
  have h0 := eq_zero_of_orthonormal (sqZero G Xᘁ) hA (fun j => incl _ (e j)) (fun i => incl _ (f i)) horthH _ hy
  exact congrArg Prod.snd h0

/-- **The frame map of a complete orthonormal frame is bijective.** -/
theorem frameMap_bijective_of_orthonormal (hA : antisym X (n + 1) = 0)
    (horth : ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0) (Z : C) :
    Function.Bijective (frameMap G e Z) := by
  have hcoord : ∀ (a : Fin n → G.obj Z) i, coordZ G (f i) (frameMap G e Z a) = a i := by
    intro a i
    rw [frameMap_apply]
    simp only [coordZ, TensorProduct.tmul_sum, map_sum]
    have := fun j => coordZ_mu G (f i) (e j) (a j)
    simp only [coordZ] at this
    simp only [this, horth]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), act_zero_left]) (by simp),
      if_pos rfl, act_unit]
  constructor
  · intro a b hab
    funext i
    rw [← hcoord a i, ← hcoord b i, hab]
  · intro w
    refine ⟨fun j => coordZ G (f j) w, ?_⟩
    -- contract `P · w` against the middle
    set Ψ : (X ⊗ Xᘁ) ⊗ (X ⊗ Z) ⟶ X ⊗ Z := (α_ X Xᘁ (X ⊗ Z)).hom ≫ (X ◁ contrZ X Z)
    have hP := frame_complete G e f hA horth
    have h0 : (G.map Ψ).hom ((μ G (X ⊗ Xᘁ) (X ⊗ Z)).hom (defect G e f ⊗ₜ w)) = 0 := by
      rw [hP, TensorProduct.zero_tmul, map_zero, map_zero]
    simp only [defect, TensorProduct.sub_tmul, TensorProduct.sum_tmul, map_sub, map_sum] at h0
    have hη : (G.map Ψ).hom ((μ G (X ⊗ Xᘁ) (X ⊗ Z)).hom ((G.map (η_ X Xᘁ)).hom ((ε G).hom 1) ⊗ₜ w)) = w := by
      rw [← μ_whiskerRight_apply, mu_unit_left_eq, map_map_apply, map_map_apply]
      have hz := ExactPairing.evaluation_coevaluation X Xᘁ
      have key : (λ_ (X ⊗ Z)).inv ≫ η_ X Xᘁ ▷ (X ⊗ Z) ≫ Ψ = 𝟙 _ := by
        simp only [Ψ, contrZ]
        calc (λ_ (X ⊗ Z)).inv ≫ η_ X Xᘁ ▷ (X ⊗ Z) ≫ (α_ X Xᘁ (X ⊗ Z)).hom ≫
              X ◁ ((α_ Xᘁ X Z).inv ≫ ε_ X Xᘁ ▷ Z ≫ (λ_ Z).hom)
            = (λ_ (X ⊗ Z)).inv ≫ (α_ (𝟙_ C) X Z).inv ≫
                ((η_ X Xᘁ ▷ X ≫ (α_ X Xᘁ X).hom ≫ X ◁ ε_ X Xᘁ) ▷ Z) ≫
                (α_ X (𝟙_ C) Z).hom ≫ (X ◁ (λ_ Z).hom) := by monoidal
          _ = 𝟙 _ := by rw [hz]; monoidal
      rw [key, G.map_id]
      rfl
    have hterm : ∀ j, (G.map Ψ).hom ((μ G (X ⊗ Xᘁ) (X ⊗ Z)).hom ((μ G X Xᘁ).hom (e j ⊗ₜ f j) ⊗ₜ w)) =
        (μ G X Z).hom (e j ⊗ₜ coordZ G (f j) w) := by
      intro j
      simp only [Ψ, map_comp_apply]
      rw [μ_assoc_apply, μ_whiskerLeft_apply]
      rfl
    rw [hη, Finset.sum_congr rfl (fun j _ => hterm j), sub_eq_zero] at h0
    rw [frameMap_apply]
    exact h0.symm

end Complete

section Reduction

/-- **Orthonormal frames** (named TRUE input): for every symmetric fusion category over `ℂ` with
positive dimensions there are a lax braided, additive, `ℂ`-linear `G : D ⥤ ModuleCat ℂ` with
`G 𝟙 = ℂ` (`ε` bijective), an object `X` containing every simple as a retract, `n = symDim X`, and
an orthonormal `n`-family `e : Fin n → G X`, `f : Fin n → G Xᘁ`.

TRUE by Deligne's theorem (take `G = ω`, `e` a basis of `ω X`, `f` the dual basis in
`ω Xᘁ ≅ (ω X)^*`).  It is the output of `n` Gram–Schmidt steps.
Not used by the final route: `DeligneFiberMain` proves `FrameFunctorExists` directly from the weaker
invariants `ε 1 ≠ 0` and countable ranks (`exists_orthonormal_family`). -/
def OrthonormalFrameExists : Prop :=
  ∀ (D : Type u) [Category.{v} D] [Preadditive D] [Linear ℂ D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
    [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D],
    (∀ i, 0 < (symDim (F.simple i)).re) →
    ∃ (G : D ⥤ ModuleCat.{0} ℂ) (_ : G.LaxBraided) (_ : G.Additive) (_ : G.Linear ℂ)
      (X : D) (n : ℕ) (e : Fin n → G.obj X) (f : Fin n → G.obj Xᘁ),
      (∀ i, ∃ (s : F.simple i ⟶ X) (r : X ⟶ F.simple i), s ≫ r = 𝟙 _) ∧
      symDim X = n ∧ Function.Bijective (ε G).hom ∧
      ∀ i j, pairG G (f i) (e j) = if i = j then (ε G).hom 1 else 0

/-- `Λ^{n+1} X = 0` as the vanishing of the antisymmetrizer. -/
theorem antisym_eq_zero_of_symDim {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D]
    [HasFiniteBiproducts D] [RightRigidCategory D] [SymmetricCategory D] [F : FusionCategory D]
    (hpos : ∀ i, 0 < (symDim (F.simple i)).re) (X : D) {n : ℕ} (hn : symDim X = n) :
    antisym X (n + 1) = 0 := by
  have hZ := isZero_extPow_of_lt hpos X hn (Nat.lt_succ_self n)
  obtain ⟨i, e, _, hei⟩ := (antisym_split X (n + 1)).choose_spec
  rw [← hei, hZ.eq_zero_of_tgt e]
  exact Limits.zero_comp

/-- **Orthonormal frames give frame functors.** -/
theorem frameFunctorExists_of_orthonormalFrameExists (h : OrthonormalFrameExists.{v, u}) :
    FrameFunctorExists.{v, u} := by
  intro D _ _ _ _ _ _ _ _ _ _ F hpos
  obtain ⟨G, _, _, _, X, n, e, f, hX, hn, hε, horth⟩ := h D hpos
  refine ⟨G, inferInstance, inferInstance, inferInstance, X, n, e, hX, ?_, ?_, ?_⟩
  · intro h0
    exact one_ne_zero (α := ℂ) (hε.1 (h0.trans (map_zero _).symm))
  · rw [← (LinearEquiv.ofBijective (ε G).hom hε).rank_eq]
    exact (Module.rank_self ℂ).le.trans Cardinal.one_le_aleph0
  · exact frameMap_bijective_of_orthonormal G e f (antisym_eq_zero_of_symDim hpos X hn) horth

/-- `OrthonormalFrameExists → SymmetricFiberFunctorExists`. -/
theorem symmetricFiberFunctorExists_of_orthonormalFrameExists (h : OrthonormalFrameExists.{v, u}) :
    SymmetricFiberFunctorExists.{v, u} :=
  symmetricFiberFunctorExists_of_frameFunctorExists (frameFunctorExists_of_orthonormalFrameExists h)

end Reduction

end VOA.Huang.TensorCat.DeligneFiber
