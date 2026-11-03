/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.Sl2SemiInfiniteNormalOrder

/-!
# State translation from operator translation

The vacuum recursion and super Goddard uniqueness turn operator translation
covariance into the state-field derivative identity. No conformal vector is
needed.
-/

namespace VOA.Sl2CosetConcrete

open Sl2SemiInfinite
open Module (End)

universe u
variable {M : Type u} [AddCommGroup M] [Module ℂ M]
variable {V : SuperVertexAlgebra M}

/-- Translation on a state is the first positive vacuum coefficient. -/
theorem translation_vacuum_coefficient (H : TranslationCovariant V) (x : M) :
    H.T x = (V.Y x) 1 V.vacuum := by
  have h := congrArg (fun f : End ℂ M => f V.vacuum) (H.covariant x 0)
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, H.vacuum_zero,
    map_zero, sub_zero, V.Y_apply_vacuum_zero, zero_add, one_smul,
    LinearMap.smul_apply] using h

/-- The field of a homogeneous translated state is the derivative field. -/
theorem translation_state_hom (H : TranslationCovariant V) {p : ZMod 2}
    {x : M} (hx : x ∈ V.parity p) : V.Y (H.T x) = deriv (V.Y x) := by
  symm
  apply V.goddard_uniquenessε _ (H.T x) (H.T_mem_parity hx)
  · intro q y hy
    exact (V.locality x hx y hy).derivL
  · apply TranslationCovariant.vacuum_recursion_eqε H
    · intro s hs
      by_cases h : s + 1 = 0
      · simp [deriv_apply, h]
      · rw [deriv_apply, LinearMap.smul_apply,
          V.Y_apply_vacuum_eq_zero x (by omega), smul_zero]
    · simpa only [deriv_apply, zero_add, one_smul] using
        (translation_vacuum_coefficient H x).symm
    · intro s
      have h := congrArg (fun f : End ℂ M => f V.vacuum)
        ((H.covariant x).deriv' s)
      simpa only [LinearMap.sub_apply, Module.End.mul_apply, H.vacuum_zero,
        map_zero, sub_zero, LinearMap.smul_apply] using h

/-- Operator translation gives state-field translation for every state. -/
theorem translation_state (H : TranslationCovariant V) (x : M) :
    V.Y (H.T x) = deriv (V.Y x) := by
  obtain ⟨x₀, h₀, x₁, h₁, rfl⟩ := (BRST.parGrading V).exists_parity_decomp x
  simp only [map_add, translation_state_hom H h₀, translation_state_hom H h₁]

/-- The mode of a translated state has the usual shifted derivative formula. -/
theorem translation_mode (H : TranslationCovariant V) (x : M) (n : ℤ) :
    mode (V.Y (H.T x)) n = (-n) • mode (V.Y x) (n - 1) := by
  rw [translation_state]
  simp only [mode_apply, deriv_apply]
  rw [show -n - 1 + 1 = -n by omega, show -(n - 1) - 1 = -n by omega]

end VOA.Sl2CosetConcrete
