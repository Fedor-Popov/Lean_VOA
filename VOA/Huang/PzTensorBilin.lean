/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocTauStable

/-!
# Bilinear functions of homogeneous pairs; the coefficient functions are bilinear

A function `G : HomPair P₁ P₂ → ℂ` is **bilinear** if, for fixed weight labels `(α₁, α₂)`, the map
`(w₁, w₂) ↦ G(w₁, α₁, w₂, α₂)` is bilinear on `P₁(α₁) × P₂(α₂)`.  These form a subspace
`bilin P₁ P₂` — it is the full dual `(P₁ ⊗ P₂)* = ∏_{α₁,α₂} (P₁(α₁) ⊗ P₂(α₂))*` of the
Huang–Lepowsky `P(z)`-tensor product theory, in the "homogeneous pair" presentation used for the
coefficient functions `B_{n,k}`.

`coefFun_mem_bilin`: every coefficient function `B_{n,k}(f, w₃)` of a product of intertwining
operators among irreducible modules of a strongly rational `V` is bilinear (additivity in `w₁`,
`w₂` of the analytic product function — the defining series converge — and linearity of the
expansion coefficients).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorBilin

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.LogRemovalSemisimple
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Bilinear functions of homogeneous pairs -/

section Bilin

variable {P₁ P₂ : LWModule W}

/-- Evaluation of `G` on a pair of weight-space elements with fixed labels. -/
def ev (G : HomPair P₁ P₂ → ℂ) (α₁ α₂ : ℂ) (a : P₁.isMod.weight α₁) (b : P₂.isMod.weight α₂) :
    ℂ :=
  G ⟨a, α₁, b, α₂, a.2, b.2⟩

/-- `G` is bilinear in the two vectors for fixed labels. -/
def IsBilin (G : HomPair P₁ P₂ → ℂ) : Prop :=
  ∀ α₁ α₂ : ℂ,
    (∀ a a' b, ev G α₁ α₂ (a + a') b = ev G α₁ α₂ a b + ev G α₁ α₂ a' b) ∧
    (∀ (c : ℂ) a b, ev G α₁ α₂ (c • a) b = c * ev G α₁ α₂ a b) ∧
    (∀ a b b', ev G α₁ α₂ a (b + b') = ev G α₁ α₂ a b + ev G α₁ α₂ a b') ∧
    (∀ (c : ℂ) a b, ev G α₁ α₂ a (c • b) = c * ev G α₁ α₂ a b)

/-- The subspace of bilinear functions. -/
def bilin (P₁ P₂ : LWModule W) : Submodule ℂ (HomPair P₁ P₂ → ℂ) where
  carrier := {G | IsBilin G}
  add_mem' {G G'} hG hG' α₁ α₂ := by
    obtain ⟨a1, a2, a3, a4⟩ := hG α₁ α₂
    obtain ⟨b1, b2, b3, b4⟩ := hG' α₁ α₂
    refine ⟨fun a a' b => ?_, fun c a b => ?_, fun a b b' => ?_, fun c a b => ?_⟩ <;>
      simp only [ev, Pi.add_apply] at * <;>
      first
      | (rw [a1, b1]; ring) | (rw [a2, b2]; ring) | (rw [a3, b3]; ring) | (rw [a4, b4]; ring)
  zero_mem' α₁ α₂ := by
    refine ⟨fun a a' b => ?_, fun c a b => ?_, fun a b b' => ?_, fun c a b => ?_⟩ <;>
      simp [ev]
  smul_mem' c {G} hG α₁ α₂ := by
    obtain ⟨a1, a2, a3, a4⟩ := hG α₁ α₂
    refine ⟨fun a a' b => ?_, fun d a b => ?_, fun a b b' => ?_, fun d a b => ?_⟩ <;>
      simp only [ev, Pi.smul_apply, smul_eq_mul] at * <;>
      first
      | (rw [a1]; ring) | (rw [a2]; ring) | (rw [a3]; ring) | (rw [a4]; ring)

theorem mem_bilin {G : HomPair P₁ P₂ → ℂ} : G ∈ bilin P₁ P₂ ↔ IsBilin G := Iff.rfl

/-- Two homogeneous pairs with the same data are equal (proof irrelevance). -/
theorem homPair_ext {x y : HomPair P₁ P₂} (h1 : x.w₁ = y.w₁) (h2 : x.α₁ = y.α₁)
    (h3 : x.w₂ = y.w₂) (h4 : x.α₂ = y.α₂) : x = y := by
  cases x; cases y; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

/-- Additivity in the first vector, in `HomPair` form. -/
theorem IsBilin.add_left {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂)
    {y : P₁.carrier} (hy : y ∈ P₁.isMod.weight x.α₁) :
    G ⟨x.w₁ + y, x.α₁, x.w₂, x.α₂, add_mem x.h₁ hy, x.h₂⟩
      = G x + G ⟨y, x.α₁, x.w₂, x.α₂, hy, x.h₂⟩ :=
  (hG x.α₁ x.α₂).1 ⟨x.w₁, x.h₁⟩ ⟨y, hy⟩ ⟨x.w₂, x.h₂⟩

theorem IsBilin.smul_left {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂) (c : ℂ) :
    G ⟨c • x.w₁, x.α₁, x.w₂, x.α₂, Submodule.smul_mem _ c x.h₁, x.h₂⟩ = c * G x :=
  (hG x.α₁ x.α₂).2.1 c ⟨x.w₁, x.h₁⟩ ⟨x.w₂, x.h₂⟩

theorem IsBilin.add_right {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂)
    {y : P₂.carrier} (hy : y ∈ P₂.isMod.weight x.α₂) :
    G ⟨x.w₁, x.α₁, x.w₂ + y, x.α₂, x.h₁, add_mem x.h₂ hy⟩
      = G x + G ⟨x.w₁, x.α₁, y, x.α₂, x.h₁, hy⟩ :=
  (hG x.α₁ x.α₂).2.2.1 ⟨x.w₁, x.h₁⟩ ⟨x.w₂, x.h₂⟩ ⟨y, hy⟩

theorem IsBilin.smul_right {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂)
    (c : ℂ) :
    G ⟨x.w₁, x.α₁, c • x.w₂, x.α₂, x.h₁, Submodule.smul_mem _ c x.h₂⟩ = c * G x :=
  (hG x.α₁ x.α₂).2.2.2 c ⟨x.w₁, x.h₁⟩ ⟨x.w₂, x.h₂⟩

/-- A bilinear function vanishes on pairs with a zero first vector. -/
theorem IsBilin.zero_left {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂)
    (h : x.w₁ = 0) : G x = 0 := by
  have := hG.smul_left x 0
  rw [zero_mul] at this
  rw [← this]
  congr 1
  exact homPair_ext (by change x.w₁ = (0 : ℂ) • x.w₁; rw [zero_smul, h]) rfl rfl rfl

/-- A bilinear function vanishes on pairs with a zero second vector. -/
theorem IsBilin.zero_right {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x : HomPair P₁ P₂)
    (h : x.w₂ = 0) : G x = 0 := by
  have := hG.smul_right x 0
  rw [zero_mul] at this
  rw [← this]
  congr 1
  exact homPair_ext rfl rfl (by change x.w₂ = (0 : ℂ) • x.w₂; rw [zero_smul, h]) rfl

/-! ### Relational forms (no dependent rewriting needed) -/

/-- Equal data give equal values. -/
theorem G_congr (G : HomPair P₁ P₂ → ℂ) {x y : HomPair P₁ P₂} (h1 : x.w₁ = y.w₁)
    (h2 : x.α₁ = y.α₁) (h3 : x.w₂ = y.w₂) (h4 : x.α₂ = y.α₂) : G x = G y := by
  rw [homPair_ext h1 h2 h3 h4]

theorem IsBilin.addL {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x y z : HomPair P₁ P₂)
    (h1 : y.α₁ = x.α₁) (h2 : z.α₁ = x.α₁) (h3 : y.w₂ = x.w₂) (h4 : z.w₂ = x.w₂)
    (h5 : y.α₂ = x.α₂) (h6 : z.α₂ = x.α₂) (h7 : x.w₁ = y.w₁ + z.w₁) : G x = G y + G z := by
  have hz1 : z.w₁ ∈ P₁.isMod.weight y.α₁ := by rw [h1, ← h2]; exact z.h₁
  have key := (hG y.α₁ y.α₂).1 ⟨y.w₁, y.h₁⟩ ⟨z.w₁, hz1⟩ ⟨y.w₂, y.h₂⟩
  have e1 : G x = ev G y.α₁ y.α₂ (⟨y.w₁, y.h₁⟩ + ⟨z.w₁, hz1⟩) ⟨y.w₂, y.h₂⟩ :=
    G_congr G (by simp [h7]) h1.symm h3.symm h5.symm
  have e2 : G z = ev G y.α₁ y.α₂ ⟨z.w₁, hz1⟩ ⟨y.w₂, y.h₂⟩ :=
    G_congr G rfl (h2.trans h1.symm) (h4.trans h3.symm) (h6.trans h5.symm)
  rw [e1, key, e2]
  rfl

theorem IsBilin.smulL {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x y : HomPair P₁ P₂) (c : ℂ)
    (h1 : y.α₁ = x.α₁) (h3 : y.w₂ = x.w₂) (h5 : y.α₂ = x.α₂) (h7 : x.w₁ = c • y.w₁) :
    G x = c * G y := by
  have key := (hG y.α₁ y.α₂).2.1 c ⟨y.w₁, y.h₁⟩ ⟨y.w₂, y.h₂⟩
  have e1 : G x = ev G y.α₁ y.α₂ (c • ⟨y.w₁, y.h₁⟩) ⟨y.w₂, y.h₂⟩ :=
    G_congr G (by simp [h7]) h1.symm h3.symm h5.symm
  rw [e1, key]
  rfl

theorem IsBilin.addR {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x y z : HomPair P₁ P₂)
    (h1 : y.α₁ = x.α₁) (h2 : z.α₁ = x.α₁) (h3 : y.w₁ = x.w₁) (h4 : z.w₁ = x.w₁)
    (h5 : y.α₂ = x.α₂) (h6 : z.α₂ = x.α₂) (h7 : x.w₂ = y.w₂ + z.w₂) : G x = G y + G z := by
  have hz2 : z.w₂ ∈ P₂.isMod.weight y.α₂ := by rw [h5, ← h6]; exact z.h₂
  have key := (hG y.α₁ y.α₂).2.2.1 ⟨y.w₁, y.h₁⟩ ⟨y.w₂, y.h₂⟩ ⟨z.w₂, hz2⟩
  have e1 : G x = ev G y.α₁ y.α₂ ⟨y.w₁, y.h₁⟩ (⟨y.w₂, y.h₂⟩ + ⟨z.w₂, hz2⟩) :=
    G_congr G h3.symm h1.symm (by simp [h7]) h5.symm
  have e2 : G z = ev G y.α₁ y.α₂ ⟨y.w₁, y.h₁⟩ ⟨z.w₂, hz2⟩ :=
    G_congr G (h4.trans h3.symm) (h2.trans h1.symm) rfl (h6.trans h5.symm)
  rw [e1, key, e2]
  rfl

theorem IsBilin.smulR {G : HomPair P₁ P₂ → ℂ} (hG : IsBilin G) (x y : HomPair P₁ P₂) (c : ℂ)
    (h1 : y.α₁ = x.α₁) (h3 : y.w₁ = x.w₁) (h5 : y.α₂ = x.α₂) (h7 : x.w₂ = c • y.w₂) :
    G x = c * G y := by
  have key := (hG y.α₁ y.α₂).2.2.2 c ⟨y.w₁, y.h₁⟩ ⟨y.w₂, y.h₂⟩
  have e1 : G x = ev G y.α₁ y.α₂ ⟨y.w₁, y.h₁⟩ (c • ⟨y.w₂, y.h₂⟩) :=
    G_congr G h3.symm h1.symm (by simp [h7]) h5.symm
  rw [e1, key]
  rfl

/-- Membership in `bilin` from the relational forms. -/
theorem isBilin_of {G : HomPair P₁ P₂ → ℂ}
    (hA : ∀ x y z : HomPair P₁ P₂, y.α₁ = x.α₁ → z.α₁ = x.α₁ → y.w₂ = x.w₂ → z.w₂ = x.w₂ →
      y.α₂ = x.α₂ → z.α₂ = x.α₂ → x.w₁ = y.w₁ + z.w₁ → G x = G y + G z)
    (hS : ∀ (x y : HomPair P₁ P₂) (c : ℂ), y.α₁ = x.α₁ → y.w₂ = x.w₂ → y.α₂ = x.α₂ →
      x.w₁ = c • y.w₁ → G x = c * G y)
    (hA' : ∀ x y z : HomPair P₁ P₂, y.α₁ = x.α₁ → z.α₁ = x.α₁ → y.w₁ = x.w₁ → z.w₁ = x.w₁ →
      y.α₂ = x.α₂ → z.α₂ = x.α₂ → x.w₂ = y.w₂ + z.w₂ → G x = G y + G z)
    (hS' : ∀ (x y : HomPair P₁ P₂) (c : ℂ), y.α₁ = x.α₁ → y.w₁ = x.w₁ → y.α₂ = x.α₂ →
      x.w₂ = c • y.w₂ → G x = c * G y) : IsBilin G := by
  intro α₁ α₂
  refine ⟨fun a a' b => ?_, fun c a b => ?_, fun a b b' => ?_, fun c a b => ?_⟩
  · exact hA _ ⟨a, α₁, b, α₂, a.2, b.2⟩ ⟨a', α₁, b, α₂, a'.2, b.2⟩ rfl rfl rfl rfl rfl rfl
      (Submodule.coe_add _ _)
  · exact hS _ ⟨a, α₁, b, α₂, a.2, b.2⟩ c rfl rfl rfl (Submodule.coe_smul _ _)
  · exact hA' _ ⟨a, α₁, b, α₂, a.2, b.2⟩ ⟨a, α₁, b', α₂, a.2, b'.2⟩ rfl rfl rfl rfl rfl rfl
      (Submodule.coe_add _ _)
  · exact hS' _ ⟨a, α₁, b, α₂, a.2, b.2⟩ c rfl rfl rfl (Submodule.coe_smul _ _)

end Bilin

/-! ## The coefficient functions are bilinear -/

theorem one_norm_lt {t : ℂ} (ht : t ∈ overlapDomain) : ‖(1 : ℂ)‖ < ‖1 + Complex.exp t‖ := by
  rw [norm_one]; exact one_lt_norm ht

section Coef

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
include hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₃ hf

theorem prodFun_add_left {α₁ α₂ : ℂ} {a a' : P₁.carrier} {b : P₂.carrier}
    (ha : a ∈ P₁.isMod.weight α₁) (ha' : a' ∈ P₁.isMod.weight α₁)
    (hb : b ∈ P₂.isMod.weight α₂) :
    ∀ t ∈ overlapDomain,
      prodFun Y₁ Y₂ f (a + a') b w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
        = prodFun Y₁ Y₂ f a b w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
          + prodFun Y₁ Y₂ f a' b w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t := by
  intro t ht
  have s := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ ha hb h₃ hf one_ne_zero (one_norm_lt ht)
  have s' := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ ha' hb h₃ hf one_ne_zero (one_norm_lt ht)
  unfold prodFun prodValue
  rw [← Summable.tsum_add s s']
  refine tsum_congr fun k => ?_
  simp only [prodCoeff, map_add, LinearMap.add_apply]
  ring

theorem prodFun_add_right {α₁ α₂ : ℂ} {a : P₁.carrier} {b b' : P₂.carrier}
    (ha : a ∈ P₁.isMod.weight α₁) (hb : b ∈ P₂.isMod.weight α₂)
    (hb' : b' ∈ P₂.isMod.weight α₂) :
    ∀ t ∈ overlapDomain,
      prodFun Y₁ Y₂ f a (b + b') w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
        = prodFun Y₁ Y₂ f a b w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t
          + prodFun Y₁ Y₂ f a b' w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) t := by
  intro t ht
  have s := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ ha hb h₃ hf one_ne_zero (one_norm_lt ht)
  have s' := summable_prodValue hV i₁ i₂ i₃ i₄ hY₁ hY₂ ha hb' h₃ hf one_ne_zero (one_norm_lt ht)
  unfold prodFun prodValue
  rw [← Summable.tsum_add s s']
  refine tsum_congr fun k => ?_
  simp only [prodCoeff, map_add, LinearMap.add_apply]
  ring

omit hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₃ hf in
theorem prodFun_smul_left (c : ℂ) (a : P₁.carrier) (b : P₂.carrier) (σ ν₀ t : ℂ) :
    prodFun Y₁ Y₂ f (c • a) b w₃ σ ν₀ t = c * prodFun Y₁ Y₂ f a b w₃ σ ν₀ t := by
  unfold prodFun prodValue
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [prodCoeff, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

omit hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₃ hf in
theorem prodFun_smul_right (c : ℂ) (a : P₁.carrier) (b : P₂.carrier) (σ ν₀ t : ℂ) :
    prodFun Y₁ Y₂ f a (c • b) w₃ σ ν₀ t = c * prodFun Y₁ Y₂ f a b w₃ σ ν₀ t := by
  unfold prodFun prodValue
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [prodCoeff, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

include iQ in
/-- **The coefficient functions are bilinear.** -/
theorem coefFun_mem_bilin (n : ℂ) (k : ℕ) :
    coefFun Y₁ Y₂ f w₃ α₃ h₄ n k ∈ bilin P₁ P₂ := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  intro α₁ α₂
  refine ⟨fun a a' b => ?_, fun c a b => ?_, fun a b b' => ?_, fun c a b => ?_⟩
  · simp only [ev, coefFun, prodExpCoeff]
    have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 b.2 h₃ hf
    have e' := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a'.2 b.2 h₃ hf
    rw [Submodule.coe_add, logCoeff_congr hU hs hne
      (prodFun_add_left hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₃ hf a.2 a'.2 b.2)
      (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (add_mem a.2 a'.2) b.2 h₃ hf)]
    exact logCoeff_add hU hs hne e e' _ _
  · simp only [ev, coefFun, prodExpCoeff]
    have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 b.2 h₃ hf
    rw [Submodule.coe_smul, logCoeff_congr hU hs hne
      (fun t _ => prodFun_smul_left c (a : P₁.carrier) (b : P₂.carrier) _ _ t)
      (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ (Submodule.smul_mem _ c a.2) b.2 h₃ hf)]
    exact logCoeff_smul hU hs hne c e _ _
  · simp only [ev, coefFun, prodExpCoeff]
    have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 b.2 h₃ hf
    have e' := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 b'.2 h₃ hf
    rw [Submodule.coe_add, logCoeff_congr hU hs hne
      (prodFun_add_right hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₃ hf a.2 b.2 b'.2)
      (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 (add_mem b.2 b'.2) h₃ hf)]
    exact logCoeff_add hU hs hne e e' _ _
  · simp only [ev, coefFun, prodExpCoeff]
    have e := prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 b.2 h₃ hf
    rw [Submodule.coe_smul, logCoeff_congr hU hs hne
      (fun t _ => prodFun_smul_right c (a : P₁.carrier) (b : P₂.carrier) _ _ t)
      (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ a.2 (Submodule.smul_mem _ c b.2) h₃ hf)]
    exact logCoeff_smul hU hs hne c e _ _

end Coef

end VOA.Huang.PzTensorBilin
