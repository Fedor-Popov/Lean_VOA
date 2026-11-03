/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSpanning
import VOA.Modularity.JFunction

/-!
# The Moonshine corollary, honestly  (Gannon Question 5.3.4 / Thm 5.3.8 corollary)

This file is abstract: nothing here is instantiated at `V♮`.  (`V♮` is constructed in
`VOA/Moonshine`; `Moonshine.moonshine` proves `dim V♮ₙ = [qⁿ]JShift` directly.)  What is here:

* the formal character series `charSeries W = Σ_n dim 𝒱_n qⁿ` (`= q^{c/24}·χ_𝒱`), and its relation to
  the adjoint module's `gradedDim`;
* the right-hand side `JShift = q·J` (`JFunction`);
* Gannon's **Question 5.3.4 in abstract form**: for a VOA with `c = 24`, `𝒱₁ = ⊥`, holomorphic and
  `C₂`-cofinite (all as named hypotheses), `charSeries W = JShift` (`MoonshineCharacter`);
* and what Zhu's theorem gives towards it: for a holomorphic VOA with `h = 0` and `c = 24`, the
  trace-spanning data of `BlockSpanning` force the modular representation to be **trivial**, so the
  character is a genuine **`SL₂(ℤ)`-invariant function** on `ℍ` (`char_SL2Z_invariant_of_spanning`).
  The remaining step to `= J` is the hauptmodul uniqueness (a weight-`0` level-one modular function
  with a simple pole at the cusp is `j + const`; Mathlib: `ModularFormClass.levelOne_weight_zero_const`),
  which needs the holomorphy of `qEvalAt` on `ℍ` (Stage-2 datum) — recorded, not claimed.

## Status
All declarations real; the theorem `char_SL2Z_invariant_of_spanning` is proved (axiom-clean) from
the named data.  `MoonshineCharacter W` is a `Prop`, never asserted.
-/

namespace VOA

open scoped BigOperators MatrixGroups

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The formal character series and its relation to `gradedDim` -/

/-- **The character series** `Σ_{n ≥ 0} (dim 𝒱ₙ) qⁿ = q^{c/24}·χ_𝒱(τ)` as a power series. -/
noncomputable def charSeries (W : VertexOperatorAlgebra 𝒱) : PowerSeries ℂ :=
  PowerSeries.mk (fun n => (Module.finrank ℂ (W.grading n) : ℂ))

@[simp] theorem coeff_charSeries (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    PowerSeries.coeff n (charSeries W) = (Module.finrank ℂ (W.grading n) : ℂ) := by
  rw [charSeries, PowerSeries.coeff_mk]

/-- The adjoint module's graded dimension at degree `n − c/24` is `dim 𝒱ₙ`. -/
theorem gradedDim_adjoint (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    gradedDim (adjointModule W) ((n : ℂ) - W.centralCharge / 24)
      = (Module.finrank ℂ (W.grading n) : ℂ) := by
  rw [gradedDim, show (n : ℂ) - W.centralCharge / 24 + W.centralCharge / 24 = (n : ℂ) from by ring]
  change (Module.finrank ℂ (adjWeight W (n : ℂ)) : ℂ) = _
  rw [adjWeight_cast]

/-- `charSeries` records `gradedDim (adjointModule W)` at the integer points `n − c/24`. -/
theorem coeff_charSeries_eq_gradedDim (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    PowerSeries.coeff n (charSeries W)
      = gradedDim (adjointModule W) ((n : ℂ) - W.centralCharge / 24) := by
  rw [coeff_charSeries, ← gradedDim_adjoint W n, Int.cast_natCast]

/-! ## Gannon's Question 5.3.4, abstractly -/

/-- **The Moonshine hypotheses**, as named data: central charge `24`, `𝒱₁ = 0`, holomorphic,
`C₂`-cofinite (Gannon §5.3.5). -/
structure MoonshineHypotheses (W : VertexOperatorAlgebra 𝒱) : Prop where
  centralCharge_eq : W.centralCharge = 24
  grading_one_eq_bot : W.grading 1 = ⊥
  holomorphic : Holomorphic W
  c2 : C2Cofinite W

/-- **The Moonshine character identity** `χ_𝒱 = J`, formally: `Σ dim 𝒱ₙ qⁿ = q·J`.  A `Prop` —
Gannon's Question 5.3.4 for `𝒱`; **never asserted here**.  At `𝒱 = V♮` this is Monstrous Moonshine's
`χ_{V♮} = J`, which awaits `Examples/MoonshineModule`. -/
def MoonshineCharacter (W : VertexOperatorAlgebra 𝒱) : Prop := charSeries W = JShift

/-- Under the Moonshine hypotheses, the character identity has the right constant terms: both sides
start with `1` (`dim 𝒱₀ ≥ 1` is needed for equality; here we record the shape `[q⁰]JShift = 1`). -/
theorem moonshineCharacter_coeff_zero_iff (W : VertexOperatorAlgebra 𝒱)
    (h : MoonshineCharacter W) : (Module.finrank ℂ (W.grading 0) : ℂ) = 1 := by
  have := congrArg (PowerSeries.coeff 0) h
  rw [coeff_charSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_JShift] at this
  exact_mod_cast this

/-- Under the Moonshine hypotheses `𝒱₁ = ⊥`, the `q¹`-coefficient of the character vanishes — as it
must for `J = j − 744` (`[q¹]JShift = 744 − 744 = 0`). -/
theorem coeff_one_charSeries_of_grading_one_eq_bot (W : VertexOperatorAlgebra 𝒱)
    (h1 : W.grading 1 = ⊥) : PowerSeries.coeff 1 (charSeries W) = 0 := by
  rw [coeff_charSeries, Nat.cast_one, h1, finrank_bot, Nat.cast_zero]

/-! ## What Zhu's theorem gives: `SL₂(ℤ)`-invariance of a holomorphic `c = 24` character -/

/-- `S² = −1` in `SL₂(ℤ)`. -/
theorem S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(ST)³ = −1` in `SL₂(ℤ)`. -/
theorem S_mul_T_pow_three : (ModularGroup.S * ModularGroup.T) ^ 3 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.S, ModularGroup.T, pow_succ, Matrix.mul_apply, Fin.sum_univ_two]

section Holomorphic
variable {W : VertexOperatorAlgebra 𝒱}

/-- The one-module family (a holomorphic VOA has a single irreducible). -/
noncomputable def singleFam (V : IrrModule W) : Unit → IrrModule W := fun _ => V

/-- **The modular representation of a holomorphic `c = 24` VOA is trivial**, given the
trace-spanning/independence data for its single module of conformal weight `0`, provided the
character is not identically zero: `ρ(T) = e^{2πi(0 − 1)} = 1`, `ρ(−1) = 1` (from the law at `−1`),
`ρ(S)² = ρ(−1) = 1` and `ρ(S)³ = ρ((ST)³)·ρ(T)^{−3} = 1`, so `ρ(S) = 1`. -/
theorem modularRepOf_eq_one_of_holomorphic (V : IrrModule W)
    (hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)))
    (hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)))
    (hcw : HasConformalWeight V.isMod 0) (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) : modularRepOf (singleFam V) (fun _ => (0 : ℂ)) hsp hind A = 1 := by
  set ρ := modularRepOf (singleFam V) (fun _ => (0 : ℂ)) hsp hind with hρ
  -- entries of `1×1` matrices
  have hentry : ∀ B : SL(2, ℤ), ρ B = Matrix.of (fun _ _ => rhoOf (singleFam V) (fun _ => (0 : ℂ)) hsp B () ()) := by
    intro B
    refine Matrix.ext (fun i j => ?_)
    rcases i; rcases j
    rfl
  have hmul1 : ∀ B C : SL(2, ℤ), (ρ B * ρ C) () () = ρ B () () * ρ C () () := by
    intro B C
    rw [Matrix.mul_apply, Fintype.sum_unique]
  -- ρ(T) = 1
  have hT : ρ ModularGroup.T = 1 := by
    have h := rhoOf_T (singleFam V) (fun _ => (0 : ℂ)) hsp hind (fun _ => hcw)
    refine Matrix.ext (fun i j => ?_)
    rcases i; rcases j
    change rhoOf (singleFam V) (fun _ => (0 : ℂ)) hsp ModularGroup.T () () = 1
    rw [h, modularRepT_diag, modularTEntry, hc]
    rw [show (2 * (Real.pi : ℂ) * Complex.I * (0 - 24 / 24))
        = ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) from by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  -- ρ(−1) = 1, from the law at `−1` applied to `𝟙` (weight `0`) at a point where `χ ≠ 0`
  have hvac0 : W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := by
    rw [mem_sqWeightSpace_iff, Nat.cast_zero, zero_smul, Lsq_zero_apply]
    refine finsum_eq_zero_of_forall_eq_zero (fun a => ?_)
    by_cases ha : a < 0
    · rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
    · push_neg at ha
      rw [VertexOperatorAlgebra.L_def,
        show mode (W.Y W.conformalVector) (a + 1) W.vacuum
          = W.smul W.conformalVector (a + 1) W.vacuum from rfl,
        W.smul_vacuum_nonneg _ (by omega), smul_zero]
  have hneg : ρ (-1) = 1 := by
    obtain ⟨τ, hτ⟩ := hne
    have hlaw := traceFun_neg_one_law (singleFam V) (fun _ => (0 : ℂ)) hsp 0 W.vacuum hvac0 () τ
    rw [pow_zero, one_mul, Fintype.sum_unique] at hlaw
    have hρ1 : rhoOf (singleFam V) (fun _ => (0 : ℂ)) hsp (-1) () () = 1 := by
      have := hlaw
      have hx : traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ
          * (rhoOf (singleFam V) (fun _ => (0 : ℂ)) hsp (-1) () () - 1) = 0 := by
        linear_combination -this
      rcases mul_eq_zero.mp hx with h0 | h0
      · exact absurd h0 hτ
      · exact sub_eq_zero.mp h0
    refine Matrix.ext (fun i j => ?_)
    rcases i; rcases j
    exact hρ1.trans (Matrix.one_apply_eq ()).symm
  -- ρ(S) = 1
  have hS2 : ρ ModularGroup.S * ρ ModularGroup.S = 1 := by
    rw [← map_mul, S_mul_S, hneg]
  have hS3 : ρ ModularGroup.S * (ρ ModularGroup.S * ρ ModularGroup.S) = 1 := by
    have h := congrArg ρ S_mul_T_pow_three
    rw [map_pow, map_mul, hT, mul_one, hneg, pow_succ, pow_succ, pow_one] at h
    rw [← mul_assoc]
    exact h
  have hS : ρ ModularGroup.S = 1 := by
    rw [hS2, mul_one] at hS3
    exact hS3
  -- ρ is the trivial homomorphism
  have htriv : ρ = 1 :=
    monoidHom_ext_SL2Z (f := ρ) (g := 1) (by rw [hS]; rfl) (by rw [hT]; rfl)
  rw [htriv]
  rfl

/-- **The character of a holomorphic `c = 24` VOA is `SL₂(ℤ)`-invariant**, given the
trace-spanning/independence data: `χ(Aτ) = χ(τ)` for every `A ∈ SL₂(ℤ)`.  This is the whole content
of Zhu's theorem for `V♮`; what remains for `χ = J` is the hauptmodul uniqueness (analytic). -/
theorem char_SL2Z_invariant_of_spanning (V : IrrModule W)
    (hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)))
    (hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)))
    (hcw : HasConformalWeight V.isMod 0) (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ := by
  have hvac0 : W.vacuum ∈ sqWeightSpace W ((0 : ℕ) : ℂ) := by
    rw [mem_sqWeightSpace_iff, Nat.cast_zero, zero_smul, Lsq_zero_apply]
    refine finsum_eq_zero_of_forall_eq_zero (fun a => ?_)
    by_cases ha : a < 0
    · rw [sqBracketCoeff_zero_of_neg ha, zero_smul]
    · push_neg at ha
      rw [VertexOperatorAlgebra.L_def,
        show mode (W.Y W.conformalVector) (a + 1) W.vacuum
          = W.smul W.conformalVector (a + 1) W.vacuum from rfl,
        W.smul_vacuum_nonneg _ (by omega), smul_zero]
  have hlaw := zhu_modularity_of_spanning (singleFam V) (fun _ => (0 : ℂ)) hsp hind (fun _ => hcw)
    A 0 W.vacuum hvac0 () τ
  rw [pow_zero, one_mul, Fintype.sum_unique] at hlaw
  have h1 := modularRepOf_eq_one_of_holomorphic V hsp hind hcw hc hne A
  change traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ)
    = traceFun (singleFam V) (fun _ => (0 : ℂ)) default W.vacuum τ
  refine hlaw.trans ?_
  change (modularRepOf (singleFam V) (fun _ => (0 : ℂ)) hsp hind A) () default * _ = _
  rw [h1, Matrix.one_apply_eq, one_mul]
  rfl

end Holomorphic

/-! ## Residual

* **`V♮`** — constructed in `VOA/Moonshine` (`Moonshine.moonshine`); `MoonshineCharacter` is not
  instantiated at it in the library.
* **The hauptmodul step** — from `char_SL2Z_invariant_of_spanning` (χ is `SL₂(ℤ)`-invariant) and the
  simple pole `[q⁰]charSeries = 1` to `χ = j + const`: needs holomorphy of `qEvalAt` on `ℍ` (the
  Stage-2 growth datum) and Mathlib's `ModularFormClass.levelOne_weight_zero_const` applied to
  `χ − j`, i.e. an analytic `j`; the formal `jShift` here is its `q`-expansion.
* `[q²]jShift = 196884` is proved: `coeff_two_jShift`, `coeff_two_JShift` (`JFunction.lean`). -/

end VOA
