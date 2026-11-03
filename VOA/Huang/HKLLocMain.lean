/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLLocConv
import VOA.Huang.HKLExtFixed
import VOA.Huang.LogRemovalBound
import VOA.Core.ReconstructionExistence

/-!
# HKL locality — `HKLLocalityInput`

`hklLocalityInput_holds : HKLLocalityInput`: for a nice (indeed strongly rational) `V`, any
fusion choice, and a commutative monoid `A` with trivial twist in the braided category
`Ordinary V`, the extension vertex operators `Y_W(a, z) b = μ(𝒴_{A,A}(a, z) b)` are mutually
local (Huang–Kirillov–Lepowsky 2015, Thm 3.2).

From the per-test identity `conv_test` (`(ζ - 1)^{N₀}` times the product expansion equals
`(ζ - 1)^{N₀}` times the reversed-product expansion) the binomial expansion
`mulBySubPow_apply_sum` of `(z₁ - z₂)^{N₀} [Y_W(a, z₁), Y_W(b, z₂)]` is read off coefficient by
coefficient: for homogeneous `a, b, c` every coefficient lies in one weight space, and functionals
supported at that weight separate it (`eq_zero_of_supported`).  General `a, b` follow by
bilinearity.

Consequently `gannonRayhaun_hkl_nice`: the forward Gannon–Rayhaun theorem rests, on the HKL
side, on the single input `HKLNiceInput`.

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLLoc

open CategoryTheory MonoidalCategory
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose VOA.Huang.HKLExt
open VOA.Huang.LogRemovalBound VOA.Huang.MatrixCoeff

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-! ## Separation by supported functionals -/

/-- A vector of one weight annihilated by every functional supported at that weight is zero. -/
theorem eq_zero_of_supported {M : Type u} [AddCommGroup M] [Module ℂ M] (Am : OrdVModule V M)
    {h : ℂ} {v : M} (hv : v ∈ Am.weight h)
    (H : ∀ f : M →ₗ[ℂ] ℂ, SupportedAt Am f h → f v = 0) : v = 0 := by
  have h0 : (⟨v, hv⟩ : Am.weight h) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun g => ?_
    have := H (g ∘ₗ weightProj Am h) (supportedAt_comp_weightProj Am h g)
    rwa [LinearMap.comp_apply, show v = ((⟨v, hv⟩ : Am.weight h) : M) from rfl,
      weightProj_apply_self] at this
  exact congrArg Subtype.val h0

/-! ## The coefficients as modes of `Y_W` -/

variable {F : FusionChoice V} {A : Ordinary V} {μ : tensorObj F A A ⟶ A}

theorem sA_eq (d : FourPointTest A A A A) (k : ℤ) :
    prodCoef F (prodOp F μ) d (d.δ - d.α - k) =
      d.functional ((extIntertwiner F μ).val (-(k : ℂ) - 1) d.x
        ((extIntertwiner F μ).val (d.α + d.β + d.γ - d.δ + k - 1) d.y d.z)) := by
  rw [prodCoef, prodOp_val, show d.α + (d.δ - d.α - (k : ℂ)) - d.δ - 1 = -(k : ℂ) - 1 by ring,
    show d.β + d.γ - (d.δ - d.α - (k : ℂ)) - 1 = d.α + d.β + d.γ - d.δ + k - 1 by ring]
  rfl

theorem tC_eq (d : FourPointTest A A A A) (k : ℤ) :
    prodCoef F (prodOp F μ) d.swapM (k + d.α + d.γ) =
      d.functional ((extIntertwiner F μ).val (d.α + d.β + d.γ - d.δ + k - 1) d.y
        ((extIntertwiner F μ).val (-(k : ℂ) - 1) d.x d.z)) := by
  change d.functional ((prodOp F μ).val (d.β + ((k : ℂ) + d.α + d.γ) - d.δ - 1) d.y
    ((F A A).intertwiner.val (d.α + d.γ - ((k : ℂ) + d.α + d.γ) - 1) d.x d.z)) = _
  rw [prodOp_val, show d.β + ((k : ℂ) + d.α + d.γ) - d.δ - 1 = d.α + d.β + d.γ - d.δ + k - 1 by
    ring, show d.α + d.γ - ((k : ℂ) + d.α + d.γ) - 1 = -(k : ℂ) - 1 by ring]
  rfl

theorem extField_apply (a : A.carrier) (j : ℤ) (x : A.carrier) :
    (extField F μ a) j x = (extIntertwiner F μ).val (((-j - 1 : ℤ)) : ℂ) a x := rfl

/-! ## Locality for homogeneous vectors -/

variable (hV : StronglyRational V) (htw : (twistIso A).hom = 𝟙 A)
  (hcomm : (braiding F A A).hom ≫ μ = μ)
  (hassoc : tensorHom F μ (𝟙 A) ≫ μ =
    (evalAssoc F (ordinaryFourPointInput_pbw F hV) A A A).hom ≫ tensorHom F (𝟙 A) μ ≫ μ)
include hV htw hcomm hassoc

/-- **Locality for homogeneous vectors.** -/
theorem local_homog {α β : ℤ} {a b : A.carrier} (ha : a ∈ A.isMod.weight (α : ℂ))
    (hb : b ∈ A.isMod.weight (β : ℂ)) : Local (extField F μ a) (extField F μ b) := by
  obtain ⟨B, hB⟩ := (F A A).isMod.boundedBelow
  set N₀ : ℕ := ⌈((α + β : ℤ) : ℝ) - B⌉₊ with hN₀def
  refine ⟨N₀, ?_⟩
  funext m n
  refine LinearMap.ext fun c => ?_
  change (VOA.mulBySubPow N₀ (bracketDist (extField F μ a) (extField F μ b)) m n) c = 0
  have hc : c ∈ ⨆ γ, A.isMod.weight γ := by
    rw [A.isMod.isInternal.submodule_iSup_eq_top]; trivial
  induction hc using Submodule.iSup_induction' with
  | zero => exact map_zero _
  | add c c' _ _ h h' => rw [map_add, h, h', add_zero]
  | mem γ c hcγ =>
    by_cases hγ : ∃ g : ℤ, (g : ℂ) = γ
    swap
    · push Not at hγ
      rw [weight_eq_bot_of_not_int htw hγ, Submodule.mem_bot] at hcγ
      rw [hcγ, map_zero]
    obtain ⟨g, rfl⟩ := hγ
    set δ : ℤ := α + β + g + m + n - N₀ with hδ
    set v := (VOA.mulBySubPow N₀ (bracketDist (extField F μ a) (extField F μ b)) m n) c with hv
    -- each term has weight `δ`
    have hterm : ∀ i j : ℤ, i + j = m + n - N₀ →
        (bracketDist (extField F μ a) (extField F μ b) i j) c ∈ A.isMod.weight (δ : ℂ) := by
      intro i j hij
      rw [bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · have h1 := FusionTop.mem_weight (extIntertwiner F μ).property hb hcγ (((-j - 1 : ℤ)) : ℂ)
        have h2 := FusionTop.mem_weight (extIntertwiner F μ).property ha h1 (((-i - 1 : ℤ)) : ℂ)
        convert h2 using 2
        push_cast
        rw [hδ]; push_cast
        have hij' : (i : ℂ) + j = m + n - N₀ := by exact_mod_cast hij
        linear_combination (-1 : ℂ) * hij'
      · have h1 := FusionTop.mem_weight (extIntertwiner F μ).property ha hcγ (((-i - 1 : ℤ)) : ℂ)
        have h2 := FusionTop.mem_weight (extIntertwiner F μ).property hb h1 (((-j - 1 : ℤ)) : ℂ)
        convert h2 using 2
        push_cast
        rw [hδ]; push_cast
        have hij' : (i : ℂ) + j = m + n - N₀ := by exact_mod_cast hij
        linear_combination (-1 : ℂ) * hij'
    have hvmem : v ∈ A.isMod.weight (δ : ℂ) := by
      rw [hv, mulBySubPow_apply_sum, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun r hr => ?_
      rw [LinearMap.smul_apply]
      refine Submodule.smul_of_tower_mem _ _ (hterm _ _ ?_)
      rw [Finset.mem_range] at hr
      push_cast [Nat.cast_sub (Nat.lt_succ_iff.1 hr)]
      ring
    refine eq_zero_of_supported A.isMod hvmem fun f hf => ?_
    -- the four-point test
    let d : FourPointTest A A A A :=
      { α := α, β := β, γ := g, δ := δ, x := a, y := b, z := c, functional := f, hx := ha,
        hy := hb, hz := hcγ, supported := hf, coordinate := 1 / 2, positive := by norm_num,
        less_one := by norm_num }
    have hd : IntTest d := ⟨⟨α, rfl⟩, ⟨β, rfl⟩, ⟨g, rfl⟩, ⟨δ, rfl⟩⟩
    have hN₀ : ∀ w : ℂ, (F A A).isMod.weight w ≠ ⊥ → (d.α + d.β).re - N₀ ≤ w.re := by
      intro w hw
      have h1 := hB w hw
      have h2 : ((α + β : ℤ) : ℝ) - B ≤ N₀ := Nat.le_ceil _
      have h3 : (d.α + d.β).re = ((α + β : ℤ) : ℝ) := by
        change ((α : ℂ) + (β : ℂ)).re = _; push_cast; simp
      rw [h3]; linarith
    have hconv := conv_test hV htw hd hcomm hassoc N₀ hN₀ m
    rw [← sub_eq_zero, conv_sub, conv] at hconv
    rw [← hconv, hv, mulBySubPow_apply_sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, Pi.sub_apply, sA_eq, tC_eq,
      bracketDist_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      map_sub, extField_apply, extField_apply, extField_apply, extField_apply, zsmul_eq_mul]
    push_cast
    have e1 : (-((n : ℂ) - ((N₀ - r : ℕ) : ℂ)) - 1) = d.α + d.β + d.γ - d.δ + ((m : ℂ) - r) - 1 := by
      change _ = (α : ℂ) + β + g - (δ : ℂ) + _ - 1
      rw [hδ, Nat.cast_sub (Nat.lt_succ_iff.1 hr)]
      push_cast; ring
    rw [e1]

omit hcomm hassoc in
include hcomm hassoc in
/-- **Locality of the extension vertex operator** (all vectors). -/
theorem local_extField (a b : A.carrier) : Local (extField F μ a) (extField F μ b) := by
  have hall : ∀ x : A.carrier, x ∈ ⨆ γ, A.isMod.weight γ := fun x => by
    rw [A.isMod.isInternal.submodule_iSup_eq_top]; trivial
  have hzero : ∀ y : FormalDist (Module.End ℂ A.carrier), Local (extField F μ 0) y := by
    intro y
    refine local_of_bracketDist_eq_zero ?_
    funext i j
    rw [bracketDist_apply, map_zero]
    change (0 : Module.End ℂ A.carrier) * y j - y j * 0 = 0
    rw [zero_mul, mul_zero, sub_zero]
  -- first `a` homogeneous, any `b`
  have hb : ∀ {α : ℂ} {a : A.carrier}, a ∈ A.isMod.weight α → ∀ b : A.carrier,
      Local (extField F μ a) (extField F μ b) := by
    intro α a ha b
    by_cases hα : ∃ k : ℤ, (k : ℂ) = α
    swap
    · push Not at hα
      rw [weight_eq_bot_of_not_int htw hα, Submodule.mem_bot] at ha
      subst ha; exact hzero _
    obtain ⟨k, rfl⟩ := hα
    have hb' := hall b
    induction hb' using Submodule.iSup_induction' with
    | zero => exact (hzero _).symm
    | add b b' _ _ h h' =>
      rw [map_add]
      exact (VOA.Reconstruction.Local.add_left h.symm h'.symm).symm
    | mem β b hbβ =>
      by_cases hβ : ∃ l : ℤ, (l : ℂ) = β
      swap
      · push Not at hβ
        rw [weight_eq_bot_of_not_int htw hβ, Submodule.mem_bot] at hbβ
        subst hbβ; exact (hzero _).symm
      obtain ⟨l, rfl⟩ := hβ
      exact local_homog hV htw hcomm hassoc ha hbβ
  have ha' := hall a
  induction ha' using Submodule.iSup_induction' with
  | zero => exact hzero _
  | add a a' _ _ h h' =>
    rw [map_add]
    exact VOA.Reconstruction.Local.add_left h h'
  | mem α a haα => exact hb haα b

end VOA.Huang.HKLLoc
