/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.JInvariantAnalytic
import VOA.Modularity.MoonshineCorollary

/-!
# The hauptmodul step for the character

`Modularity.MoonshineCorollary.char_SL2Z_invariant_of_spanning` proves that the character of a
holomorphic `C₂`-cofinite VOA of central charge `24` is `SL₂(ℤ)`-**invariant**, and
`Modularity.JInvariantAnalytic.jInvariant_smul` proves the same for the analytic `j`.  Hence:

* `char_sub_jInvariant_smul` — the difference `χ − j` is `SL₂(ℤ)`-invariant of weight `0`.
  **Proved**, with no analytic hypothesis.
* `char_eq_jInvariant_add_const` — once that difference *underlies a `ModularForm 𝒮ℒ 0`*,
  Mathlib's `levelOne_weight_zero_const` gives `χ = j + const` (Gannon's Question 5.3.4 shape).

## What is and is not here

The invariance half is a theorem.  The remaining content of "χ − j is a modular form" is purely
analytic and is carried as the datum `F : ModularForm 𝒮ℒ 0`: holomorphy of `χ` on `ℍ` — for which
`Modularity.QEvalHolomorphic.differentiableOn_char_adjoint` is available — together with the
matching of the two simple poles at the cusp (`[q⁻¹]χ = [q⁻¹]j = 1`), which needs the `q`-expansion
of the *analytic* `j`.  The statement is in the abstract Q-5.3.4 form and is not
instantiated at `V♮` (constructed separately as `Moonshine.moonshine`, `VOA/Moonshine`).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators MatrixGroups ModularForm

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **`χ − j` is `SL₂(ℤ)`-invariant.**  Both halves are theorems: the character's invariance
is `char_SL2Z_invariant_of_spanning`, and `j`'s is `jInvariant_smul`. -/
theorem char_sub_jInvariant_smul (V : IrrModule W)
    (hsp : TraceSpanning (singleFam V) (fun _ => (0 : ℂ)))
    (hind : TraceIndependent (singleFam V) (fun _ => (0 : ℂ)))
    (hcw : HasConformalWeight V.isMod 0) (hc : W.centralCharge = 24)
    (hne : ∃ τ : UpperHalfPlane, traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ ≠ 0)
    (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum (A • τ) - jInvariant (A • τ)
      = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ - jInvariant τ := by
  rw [char_SL2Z_invariant_of_spanning V hsp hind hcw hc hne A τ, jInvariant_smul A τ]

/-- **The hauptmodul step.**  If the (already `SL₂(ℤ)`-invariant) difference `χ − j` underlies
a weight-`0` level-one modular form, then `χ = j + const` — Gannon's Question 5.3.4 in the
abstract form. -/
theorem char_eq_jInvariant_add_const (V : IrrModule W) (F : ModularForm 𝒮ℒ 0)
    (hF : ∀ z : UpperHalfPlane,
      F z = traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum z - jInvariant z) :
    ∃ c : ℂ, ∀ τ : UpperHalfPlane,
      traceFun (singleFam V) (fun _ => (0 : ℂ)) () W.vacuum τ = jInvariant τ + c :=
  eq_jInvariant_add_const F _ hF

end VOA
