/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Classification.COne.McRaeO5Monodromy

/-! # O5, part (a): the twisted condition in terms of the action intertwiner

Let `C = LogModuleCat W` (`W` `C₂`-cofinite) with its logarithmic braided structure. A morphism
`a : N ⊠ X ⟶ X` is, by the universal property of the tensor product, the same as the logarithmic
intertwining operator `actY a := a ∘ 𝒴_⊠` of type `(X / N X)`.

* `twisted_intertwiner`: McRae's twisted condition
  `(N ◁ π) ≫ M_{N,X} ≫ (φ ▷ X) ≫ a = (N ◁ π) ≫ a` says exactly that
  `Ω₀Ω₀(actY a ∘ (φ ⊗ 1))` and `actY a` agree after precomposing the second slot with `π`.
* `twisted_modes`: hence, for `v` with `φ v = v` and `y ∈ range π`, the modes
  `(actY a)_{n;k}(v) y` vanish for `k ≥ 1` and for non-integral `n`: on the image of `π`, the
  operator `actY a (v, x)` has only integral powers of `x` and no logarithms.
* `unit_intertwiner`: the unit law `(ι ▷ X) ≫ a = λ_X` says `actY a ∘ (ι ⊗ 1) = Y_X`.
* `modHom_intertwiner`: a module map `f` intertwines the action operators.

Every step is the universal property (`tensorMap_intertwiner`, `tensorBraid_intertwiner`,
`tensorLeftUnit_intertwiner`) plus `Ω₀ ∘ Ω₀ = monodromy` (`omegaEquiv_zero_omegaEquiv_zero`).
-/

set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.McRaeO5
open CategoryTheory MonoidalCategory BraidedCategory VOA.LogTensor VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Classification.COne.McRaeO4c

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

/-- The canonical logarithmic tensor intertwiner of two objects of `C`. -/
abbrev canY (N P : LogModuleCat W) :
    LogIntertwiningOperator N.act.toWeakModule P.act.toWeakModule
      (tensorObject hC2 N P).act.toWeakModule :=
  tensorIntertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration

/-- **The action intertwiner** `actY a = a ∘ 𝒴_⊠` of a morphism `a : N ⊠ X ⟶ X`. -/
def actY {N X Z : LogModuleCat W} (a : tensorObject hC2 N X ⟶ Z) :
    LogIntertwiningOperator N.act.toWeakModule X.act.toWeakModule Z.act.toWeakModule :=
  postcompose (toWeakHom a) (canY hC2 N X)

/-! ## Generic composition rules -/

section Generic
variable {M₁ M₂ : Type u} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  {A₁ : WeakModule W M₁} {A₂ : WeakModule W M₂}

omit hC2 in
theorem post_comp {P Q R : LogModuleCat W} (f : P ⟶ Q) (g : Q ⟶ R)
    (Y : LogIntertwiningOperator A₁ A₂ P.act.toWeakModule) :
    postcompose (toWeakHom (f ≫ g)) Y = postcompose (toWeakHom g) (postcompose (toWeakHom f) Y) := by
  apply Subtype.ext
  funext n k
  ext x y
  rfl

end Generic

theorem post_tensorMorphism {N N' P P' : LogModuleCat W} (f : N ⟶ N') (g : P ⟶ P') :
    postcompose (toWeakHom (tensorMorphism hC2 f g)) (canY hC2 N P) =
      precompose (toWeakHom f) (toWeakHom g) (canY hC2 N' P') :=
  tensorMap_intertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration
    N'.act P'.act N'.finiteGeneration P'.finiteGeneration (toWeakHom f) (toWeakHom g)

theorem post_swap (N P : LogModuleCat W) (r : ℤ) :
    postcompose (toWeakHom (swapIso hC2 N P r).hom) (canY hC2 N P) =
      omegaEquiv P.act.toWeakModule N.act.toWeakModule (tensorObject hC2 P N).act.toWeakModule r
        (canY hC2 P N) :=
  tensorBraid_intertwiner hC2 N.act P.act N.finiteGeneration P.finiteGeneration r

/-- `(f ⊠ g) ≫ R` corresponds to `(R ∘ 𝒴_⊠) ∘ (f ⊗ g)`. -/
theorem post_tensorMorphism_comp {N N' P P' Z : LogModuleCat W} (f : N ⟶ N') (g : P ⟶ P')
    (R : tensorObject hC2 N' P' ⟶ Z) :
    postcompose (toWeakHom (tensorMorphism hC2 f g ≫ R)) (canY hC2 N P) =
      precompose (toWeakHom f) (toWeakHom g) (actY hC2 R) :=
  ((post_comp _ _ _).trans (congrArg (postcompose (toWeakHom R))
    (post_tensorMorphism hC2 f g))).trans (postcompose_precompose' _ _ _ _)

/-- `c_{N,P} ≫ R` corresponds to `Ω₀(R ∘ 𝒴_⊠)`. -/
theorem post_swap_comp {N P Z : LogModuleCat W} (R : tensorObject hC2 P N ⟶ Z) :
    postcompose (toWeakHom ((swapIso hC2 N P 0).hom ≫ R)) (canY hC2 N P) =
      omegaEquiv P.act.toWeakModule N.act.toWeakModule Z.act.toWeakModule 0 (actY hC2 R) :=
  ((post_comp _ _ _).trans (congrArg (postcompose (toWeakHom R)) (post_swap hC2 N P 0))).trans
    (omega_postcompose _ _ 0).symm

/-! ## The twisted condition -/

section Braided
variable {N X Z : LogModuleCat W}

/-- The monodromy `M_{N,X} ≫ R` corresponds to `Ω₀Ω₀(R ∘ 𝒴_⊠)`. -/
theorem post_monodromy_comp (R : tensorObject hC2 N X ⟶ Z) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    postcompose (toWeakHom (monodromy N X ≫ R)) (canY hC2 N X) =
      omegaEquiv X.act.toWeakModule N.act.toWeakModule Z.act.toWeakModule 0
        (omegaEquiv N.act.toWeakModule X.act.toWeakModule Z.act.toWeakModule 0 (actY hC2 R)) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  have h1 : postcompose (toWeakHom (monodromy N X ≫ R)) (canY hC2 N X) =
      postcompose (toWeakHom ((swapIso hC2 N X 0).hom ≫ (swapIso hC2 X N 0).hom ≫ R))
        (canY hC2 N X) := by
    congr 2
  refine h1.trans ((post_swap_comp hC2 _).trans ?_)
  exact congrArg (omegaEquiv _ _ _ 0) (post_swap_comp hC2 R)

/-- **The twisted condition as an intertwiner identity.** -/
theorem twisted_intertwiner (π : X ⟶ X) (φ : N ⟶ N) (a : tensorObject hC2 N X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    N ◁ π ≫ monodromy N X ≫ φ ▷ X ≫ a = N ◁ π ≫ a →
    precompose (toWeakHom (𝟙 N)) (toWeakHom π)
        (omegaEquiv X.act.toWeakModule N.act.toWeakModule X.act.toWeakModule 0
          (omegaEquiv N.act.toWeakModule X.act.toWeakModule X.act.toWeakModule 0
            (precompose (toWeakHom φ) (toWeakHom (𝟙 X)) (actY hC2 a)))) =
      precompose (toWeakHom (𝟙 N)) (toWeakHom π) (actY hC2 a) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  intro h
  have e := congrArg (fun F => postcompose (toWeakHom F) (canY hC2 N X)) h
  have eL : postcompose (toWeakHom (N ◁ π ≫ monodromy N X ≫ φ ▷ X ≫ a)) (canY hC2 N X) =
      precompose (toWeakHom (𝟙 N)) (toWeakHom π)
        (omegaEquiv X.act.toWeakModule N.act.toWeakModule X.act.toWeakModule 0
          (omegaEquiv N.act.toWeakModule X.act.toWeakModule X.act.toWeakModule 0
            (precompose (toWeakHom φ) (toWeakHom (𝟙 X)) (actY hC2 a)))) := by
    refine (post_tensorMorphism_comp hC2 (𝟙 N) π _).trans ?_
    refine congrArg (precompose (toWeakHom (𝟙 N)) (toWeakHom π)) ?_
    refine (post_monodromy_comp hC2 _).trans ?_
    exact congrArg (fun Y => omegaEquiv X.act.toWeakModule N.act.toWeakModule
        X.act.toWeakModule 0 (omegaEquiv N.act.toWeakModule X.act.toWeakModule
          X.act.toWeakModule 0 Y))
      (post_tensorMorphism_comp hC2 φ (𝟙 X) a)
  have eR : postcompose (toWeakHom (N ◁ π ≫ a)) (canY hC2 N X) =
      precompose (toWeakHom (𝟙 N)) (toWeakHom π) (actY hC2 a) :=
    post_tensorMorphism_comp hC2 (𝟙 N) π a
  exact eL.symm.trans (e.trans eR)

/-- **Part (a) of O5.** On the image of `π`, for `φ`-fixed `v`, the action operator
`actY a (v, x)` has no logarithms and only integral powers of `x`. -/
theorem twisted_modes (π : X ⟶ X) (φ : N ⟶ N) (a : tensorObject hC2 N X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    letI := logarithmicBraidedCategory hC2
    N ◁ π ≫ monodromy N X ≫ φ ▷ X ≫ a = N ◁ π ≫ a →
    ∀ (v : N) (_ : φ.1 v = v) (x : X) (n : ℂ),
      (∀ k, 1 ≤ k → (actY hC2 a).1 n k v (π.1 x) = 0) ∧
      ((∀ j : ℤ, n ≠ j) → (actY hC2 a).1 n 0 v (π.1 x) = 0) := by
  letI := logarithmicMonoidalCategory hC2
  letI := logarithmicBraidedCategory hC2
  intro h v hv x n
  have E := twisted_intertwiner hC2 π φ a h
  set Z := precompose (toWeakHom φ) (toWeakHom (𝟙 X)) (actY hC2 a) with hZ
  have hmono : ∀ k, monoModes Z.1 n k v (π.1 x) = (actY hC2 a).1 n k v (π.1 x) := by
    intro k
    have e := congrArg (fun Y : LogIntertwiningOperator N.act.toWeakModule X.act.toWeakModule
      X.act.toWeakModule => Y.1 n k v x) E
    simp only [precompose_apply] at e
    rw [← omegaEquiv_zero_omegaEquiv_zero]
    exact e
  have hZY : ∀ j, Z.1 n j v (π.1 x) = (actY hC2 a).1 n j v (π.1 x) := by
    intro j
    rw [hZ, precompose_apply]
    change (actY hC2 a).1 n j (φ.1 v) (π.1 x) = _
    rw [hv]
  exact monoModes_fixed Z.2.logFin hZY hmono

end Braided

/-! ## The unit law and module maps -/

section Unit
variable {N X Y : LogModuleCat W}

/-- **Unit law.** `(ι ▷ X) ≫ a = λ_X` says `actY a ∘ (ι ⊗ 1) = Y_X`. -/
theorem unit_intertwiner (ι : (unitObject : LogModuleCat W) ⟶ N) (a : tensorObject hC2 N X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    ι ▷ X ≫ a = (λ_ X).hom →
    precompose (toWeakHom ι) (toWeakHom (𝟙 X)) (actY hC2 a) =
      logModuleIntertwiner X.act.toWeakModule := by
  letI := logarithmicMonoidalCategory hC2
  intro h
  have e := congrArg (fun F => postcompose (toWeakHom F) (canY hC2 unitObject X)) h
  exact (post_tensorMorphism_comp hC2 ι (𝟙 X) a).symm.trans
    (e.trans (tensorLeftUnit_intertwiner hC2 X.act X.finiteGeneration))

/-- On `W`-vectors `u` (through the unit `ι`), the integral log-free modes of `actY a` are the
module modes of `X`. -/
theorem unit_modes (ι : (unitObject : LogModuleCat W) ⟶ N) (a : tensorObject hC2 N X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    ι ▷ X ≫ a = (λ_ X).hom →
    ∀ (u : V) (j : ℤ) (x : X), (actY hC2 a).1 (j : ℂ) 0 (ι.1 u) x = mode (X.act.YM u) j x := by
  intro h u j x
  have e := congrArg (fun Y : LogIntertwiningOperator (unitObject : LogModuleCat W).act.toWeakModule
    X.act.toWeakModule X.act.toWeakModule => Y.1 (j : ℂ) 0 u x) (unit_intertwiner hC2 ι a h)
  simp only [precompose_apply] at e
  refine e.trans ?_
  change ofOrd (weakModuleModes X.act.toWeakModule) (j : ℂ) 0 u x = _
  rw [ofOrd_zero, weakModuleModes_apply_intCast]

/-- On `W`-vectors the non-integral or logarithmic modes of `actY a` vanish. -/
theorem unit_modes_zero (ι : (unitObject : LogModuleCat W) ⟶ N) (a : tensorObject hC2 N X ⟶ X) :
    letI := logarithmicMonoidalCategory hC2
    ι ▷ X ≫ a = (λ_ X).hom →
    ∀ (u : V) (n : ℂ) (k : ℕ) (x : X), (k ≠ 0 ∨ ∀ j : ℤ, (j : ℂ) ≠ n) →
      (actY hC2 a).1 n k (ι.1 u) x = 0 := by
  intro h u n k x hk
  have e := congrArg (fun Y : LogIntertwiningOperator (unitObject : LogModuleCat W).act.toWeakModule
    X.act.toWeakModule X.act.toWeakModule => Y.1 n k u x) (unit_intertwiner hC2 ι a h)
  simp only [precompose_apply] at e
  refine e.trans ?_
  change ofOrd (weakModuleModes X.act.toWeakModule) n k u x = 0
  rcases hk with hk | hk
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [ofOrd_succ]; rfl
  · unfold ofOrd
    split_ifs
    · rw [weakModuleModes_of_not_int _ hk]; rfl
    · rfl

/-- **Module maps.** `a ≫ f = (N ◁ f) ≫ b` says `f ∘ actY a = actY b ∘ (1 ⊗ f)`. -/
theorem modHom_intertwiner (a : tensorObject hC2 N X ⟶ X) (b : tensorObject hC2 N Y ⟶ Y)
    (f : X ⟶ Y) :
    letI := logarithmicMonoidalCategory hC2
    a ≫ f = N ◁ f ≫ b →
    postcompose (toWeakHom f) (actY hC2 a) =
      precompose (toWeakHom (𝟙 N)) (toWeakHom f) (actY hC2 b) := by
  letI := logarithmicMonoidalCategory hC2
  intro h
  have e := congrArg (fun F => postcompose (toWeakHom F) (canY hC2 N X)) h
  exact (post_comp _ _ _).symm.trans (e.trans (post_tensorMorphism_comp hC2 (𝟙 N) f b))

/-- Mode form of `modHom_intertwiner`. -/
theorem modHom_modes (a : tensorObject hC2 N X ⟶ X) (b : tensorObject hC2 N Y ⟶ Y)
    (f : X ⟶ Y) :
    letI := logarithmicMonoidalCategory hC2
    a ≫ f = N ◁ f ≫ b →
    ∀ (n : ℂ) (k : ℕ) (v : N) (x : X),
      f.1 ((actY hC2 a).1 n k v x) = (actY hC2 b).1 n k v (f.1 x) := by
  intro h n k v x
  exact congrArg (fun Y : LogIntertwiningOperator N.act.toWeakModule X.act.toWeakModule
    Y.act.toWeakModule => Y.1 n k v x) (modHom_intertwiner hC2 a b f h)

end Unit

end VOA.Classification.COne.McRaeO5
