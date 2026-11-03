/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BuhlSpanningMain
import VOA.Huang.ModuleC2C1
import VOA.Huang.HuangODEContra
import VOA.Huang.VerlindeFusion

/-!
# `ModuleC2Input` discharged: the downstream consequences

`BuhlSpanning.moduleC2Input_holds` proves the named input `FusionC2.ModuleC2Input` (irreducible
modules of a strongly rational VOA are `C₂`-cofinite; Buhl 2002, Abe–Buhl–Dong 2004).  This file
records what thereby becomes unconditional:

* `huangODEInput_holds : HuangODEInput` — Huang's ODEs for products and iterates of
  intertwining operators among irreducible modules of every strongly rational VOA (so
  `HuangODEContra.summable_prodTerm_of_moduleC2Input moduleC2Input_holds …` and
  `summable_iterTerm_of_moduleC2Input moduleC2Input_holds …` are unconditional convergence
  statements);
* `finiteDimensional_intertwiningSpace_of_stronglyRational`,
  `finiteDimensional_intertwiningSpace_of_nice`, `finiteDimensional_fusion_of_nice` — fusion rules
  are finite;
* `moduleC1Input_holds` — irreducible modules are graded `C₁`-cofinite (Huang's hypothesis).

No `sorry`, no axioms beyond Lean's three, no `Pr`/`VOA.pbw`.
-/

namespace VOA.Huang.ModuleC2

open VOA VOA.Huang.FusionC2 VOA.Huang.BuhlSpanning

universe u w

/-- **Huang's ODE input holds for every strongly rational VOA.** -/
theorem huangODEInput_holds : VOA.Huang.Convergence.HuangODEInput.{u} :=
  VOA.Huang.HuangODEContra.huangODEInput_of_moduleC2Input' moduleC2Input_holds

/-- Irreducible modules of a strongly rational VOA are graded `C₁`-cofinite. -/
theorem moduleC1Input_holds : ModuleC1Input.{u} :=
  moduleC2Input_iff_moduleC1Input.mp moduleC2Input_holds

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Finite fusion rules for strongly rational `V`**, unconditionally. -/
theorem finiteDimensional_intertwiningSpace_of_stronglyRational (hV : StronglyRational W)
    {P₁ P₂ P₃ : LWModule W} (h₁ : P₁.IsIrreducibleLW) (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod P₃.isMod) :=
  finiteDimensional_intertwiningSpace_stronglyRational moduleC2Input_holds hV h₁ h₂ h₃

/-- **Finite fusion rules for nice `V`**, unconditionally. -/
theorem finiteDimensional_intertwiningSpace_of_nice (hV : Classification.COne.Nice W)
    {P₁ P₂ P₃ : LWModule W} (h₁ : P₁.IsIrreducibleLW) (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) :
    FiniteDimensional ℂ (intertwiningSpace P₁.isMod P₂.isMod P₃.isMod) :=
  finiteDimensional_intertwiningSpace_nice moduleC2Input_holds hV h₁ h₂ h₃

/-- The fusion rules of a nice VOA's modular-data family are honest dimensions,
unconditionally. -/
theorem finiteDimensional_fusion_of_nice (hV : Classification.COne.Nice W) {ι : Type w}
    [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι) (a b c : ι) :
    FiniteDimensional ℂ
      (intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod (D.Mfam c).isMod) :=
  VOA.Huang.VerlindeFusion.finiteDimensional_fusion moduleC2Input_holds hV D a b c

end VOA.Huang.ModuleC2
