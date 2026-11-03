/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocExpansion

/-!
# Simultaneous block spaces for the converse to associativity

The arguments of a block include all homogeneous vectors, the supported functional, and
the real overlap coordinate. Thus membership in the span means one finite family works
simultaneously for all those arguments. Scalars are absorbed into an actual intertwiner.

`productSpan_le_iterateSpan` is the forward associativity theorem in this language.
`associativityConverse_iff_span_le` is a lossless interface for the missing reverse inclusion.
Neither inclusion is asserted without its displayed hypothesis.
-/

namespace VOA.Huang.AssocConverse

open VOA VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- All simultaneous test data, at `z₂ = 1` and `z₁ = 1 + x`. -/
structure TestData (P₁ P₂ P₃ P₄ : LWModule W) where
  α₁ : ℂ
  α₂ : ℂ
  α₃ : ℂ
  h₄ : ℂ
  w₁ : P₁.carrier
  w₂ : P₂.carrier
  w₃ : P₃.carrier
  f : P₄.carrier →ₗ[ℂ] ℂ
  hw₁ : w₁ ∈ P₁.isMod.weight α₁
  hw₂ : w₂ ∈ P₂.isMod.weight α₂
  hw₃ : w₃ ∈ P₃.isMod.weight α₃
  hf : SupportedAt P₄.isMod f h₄
  x : ℝ
  xpos : 0 < x
  xlt : x < 1

/-- An actual product channel, with irreducible intermediate module. -/
structure ProductChannel (P₁ P₂ P₃ P₄ : LWModule W) where
  Q : LWModule W
  irreducible : Q.IsIrreducibleLW
  left : IntertwiningOperator P₁.isMod Q.isMod P₄.isMod
  right : IntertwiningOperator P₂.isMod P₃.isMod Q.isMod

/-- An actual iterate channel, with irreducible intermediate module. -/
structure IterateChannel (P₁ P₂ P₃ P₄ : LWModule W) where
  Q : LWModule W
  irreducible : Q.IsIrreducibleLW
  outer : IntertwiningOperator Q.isMod P₃.isMod P₄.isMod
  inner : IntertwiningOperator P₁.isMod P₂.isMod Q.isMod

variable {P₁ P₂ P₃ P₄ : LWModule W}

noncomputable def ProductChannel.eval (C : ProductChannel P₁ P₂ P₃ P₄)
    (d : TestData P₁ P₂ P₃ P₄) : ℂ :=
  prodValue C.left.val C.right.val d.f d.w₁ d.w₂ d.w₃
    (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₂ + d.α₃ - 1 - C.Q.h) (1 + d.x) 1

noncomputable def IterateChannel.eval (C : IterateChannel P₁ P₂ P₃ P₄)
    (d : TestData P₁ P₂ P₃ P₄) : ℂ :=
  iterValue C.outer.val C.inner.val d.f d.w₁ d.w₂ d.w₃
    (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₁ + d.α₂ - 1 - C.Q.h) d.x 1

noncomputable def ProductChannel.scale (a : ℂ) (C : ProductChannel P₁ P₂ P₃ P₄) :
    ProductChannel P₁ P₂ P₃ P₄ := { C with left := a • C.left }

noncomputable def IterateChannel.scale (a : ℂ) (C : IterateChannel P₁ P₂ P₃ P₄) :
    IterateChannel P₁ P₂ P₃ P₄ := { C with outer := a • C.outer }

theorem ProductChannel.eval_scale (a : ℂ) (C : ProductChannel P₁ P₂ P₃ P₄) :
    (C.scale a).eval = a • C.eval := by
  funext d
  change prodValue (a • C.left.val) C.right.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₂ + d.α₃ - 1 - C.Q.h) (1 + d.x) 1
    = a * prodValue C.left.val C.right.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₂ + d.α₃ - 1 - C.Q.h) (1 + d.x) 1
  unfold prodValue
  simp_rw [prodCoeff_smul_left, mul_assoc]
  rw [tsum_mul_left]

theorem IterateChannel.eval_scale (a : ℂ) (C : IterateChannel P₁ P₂ P₃ P₄) :
    (C.scale a).eval = a • C.eval := by
  funext d
  change iterValue (a • C.outer.val) C.inner.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₁ + d.α₂ - 1 - C.Q.h) d.x 1
    = a * iterValue C.outer.val C.inner.val d.f d.w₁ d.w₂ d.w₃
      (d.α₁ + d.α₂ + d.α₃ - d.h₄ - 2) (d.α₁ + d.α₂ - 1 - C.Q.h) d.x 1
  unfold iterValue
  simp_rw [iterCoeff_smul_left, mul_assoc]
  rw [tsum_mul_left]

/-- Span membership with scalar-closed generators is an unweighted finite sum.
This works even when the indexing type is empty. -/
theorem mem_span_range_iff_finite_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    {ι : Type*} (v : ι → E) (hs : ∀ (a : ℂ) (i : ι), ∃ j, v j = a • v i) (f : E) :
    f ∈ Submodule.span ℂ (Set.range v) ↔ ∃ (r : ℕ) (c : Fin r → ι), f = ∑ j, v (c j) := by
  classical
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨1, fun _ => i, by simp⟩
    | zero => exact ⟨0, Fin.elim0, by simp⟩
    | add x y hx hy hfx hfy =>
      obtain ⟨r, c, rfl⟩ := hfx
      obtain ⟨s, d, rfl⟩ := hfy
      refine ⟨r + s, Fin.addCases c d, ?_⟩
      simp [Fin.sum_univ_add]
    | smul a x hx hfx =>
      obtain ⟨r, c, rfl⟩ := hfx
      choose d hd using fun j : Fin r => hs a (c j)
      exact ⟨r, d, by simp only [Finset.smul_sum, hd]⟩
  · rintro ⟨r, c, rfl⟩
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨c j, rfl⟩

noncomputable def productSpan (P₁ P₂ P₃ P₄ : LWModule W) :
    Submodule ℂ (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  Submodule.span ℂ (Set.range (ProductChannel.eval (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (P₄ := P₄)))

noncomputable def iterateSpan (P₁ P₂ P₃ P₄ : LWModule W) :
    Submodule ℂ (TestData P₁ P₂ P₃ P₄ → ℂ) :=
  Submodule.span ℂ (Set.range (IterateChannel.eval (P₁ := P₁) (P₂ := P₂) (P₃ := P₃) (P₄ := P₄)))

theorem mem_productSpan_iff (f : TestData P₁ P₂ P₃ P₄ → ℂ) :
    f ∈ productSpan P₁ P₂ P₃ P₄ ↔
      ∃ (r : ℕ) (c : Fin r → ProductChannel P₁ P₂ P₃ P₄), f = ∑ j, (c j).eval :=
  mem_span_range_iff_finite_sum _ (fun a C => ⟨C.scale a, C.eval_scale a⟩) f

theorem mem_iterateSpan_iff (f : TestData P₁ P₂ P₃ P₄ → ℂ) :
    f ∈ iterateSpan P₁ P₂ P₃ P₄ ↔
      ∃ (r : ℕ) (c : Fin r → IterateChannel P₁ P₂ P₃ P₄), f = ∑ j, (c j).eval :=
  mem_span_range_iff_finite_sum _ (fun a C => ⟨C.scale a, C.eval_scale a⟩) f

/-- Forward associativity gives inclusion of simultaneous spaces. -/
theorem productSpan_le_iterateSpan (h : AssociativityInput W)
    (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) :
    productSpan P₁ P₂ P₃ P₄ ≤ iterateSpan P₁ P₂ P₃ P₄ := by
  classical
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨C, rfl⟩
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, heq⟩ :=
    h P₁ P₂ P₃ P₄ C.Q i₁ i₂ i₃ i₄ C.irreducible C.left.val C.right.val
      C.left.property C.right.property
  refine (mem_iterateSpan_iff _).mpr ⟨r,
    fun j => ⟨Qs j, iQs j, ⟨Y₃ j, hY₃ j⟩, ⟨Y₄ j, hY₄ j⟩⟩, ?_⟩
  funext d
  simpa [ProductChannel.eval, IterateChannel.eval] using
    heq d.α₁ d.α₂ d.α₃ d.h₄ d.w₁ d.w₂ d.w₃ d.f d.hw₁ d.hw₂ d.hw₃ d.hf
      (1 + d.x) 1 (by linarith [d.xpos]) (by linarith [d.xlt])

/-- The missing reverse inclusion, with no change to the quantifiers in the target. -/
def ReverseSpanInclusion (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW →
      iterateSpan P₁ P₂ P₃ P₄ ≤ productSpan P₁ P₂ P₃ P₄

theorem associativityConverse_of_span_le (h : ReverseSpanInclusion W) :
    AssociativityConverse W := by
  classical
  apply associativityConverse_of_atOne
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₃ Y₄ hY₃ hY₄
  let C : IterateChannel P₁ P₂ P₃ P₄ := ⟨Q, iQ, ⟨Y₃, hY₃⟩, ⟨Y₄, hY₄⟩⟩
  have hc : C.eval ∈ iterateSpan P₁ P₂ P₃ P₄ := Submodule.subset_span ⟨C, rfl⟩
  obtain ⟨r, c, heq⟩ := (mem_productSpan_iff C.eval).mp (h P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄ hc)
  refine ⟨r, fun j => (c j).Q, fun j => (c j).irreducible,
    fun j => (c j).left.val, fun j => (c j).right.val,
    fun j => (c j).left.property, fun j => (c j).right.property, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf x hx0 hx1
  have := congrFun heq ⟨α₁, α₂, α₃, h₄, w₁, w₂, w₃, f, h₁, h₂, h₃, hf, x, hx0, hx1⟩
  simpa [C, ProductChannel.eval, IterateChannel.eval] using this

theorem span_le_of_associativityConverse (h : AssociativityConverse W) :
    ReverseSpanInclusion W := by
  classical
  intro P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨C, rfl⟩
  obtain ⟨r, Qs, iQs, Y₁, Y₂, hY₁, hY₂, heq⟩ := h P₁ P₂ P₃ P₄ C.Q
    i₁ i₂ i₃ i₄ C.irreducible C.outer.val C.inner.val C.outer.property C.inner.property
  refine (mem_productSpan_iff _).mpr ⟨r,
    fun j => ⟨Qs j, iQs j, ⟨Y₁ j, hY₁ j⟩, ⟨Y₂ j, hY₂ j⟩⟩, ?_⟩
  funext d
  simpa [ProductChannel.eval, IterateChannel.eval] using
    heq d.α₁ d.α₂ d.α₃ d.h₄ d.w₁ d.w₂ d.w₃ d.f d.hw₁ d.hw₂ d.hw₃ d.hf
      (1 + d.x) 1 (by linarith [d.xpos]) (by linarith [d.xlt])

theorem associativityConverse_iff_span_le :
    AssociativityConverse W ↔ ReverseSpanInclusion W :=
  ⟨span_le_of_associativityConverse, associativityConverse_of_span_le⟩

end VOA.Huang.AssocConverse
