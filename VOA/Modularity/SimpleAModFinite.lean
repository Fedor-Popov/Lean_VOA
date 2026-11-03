/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AModBridge
import VOA.Modules.ZhuVermaAnArchZhu534

/-!
# Simple `A(𝒱)`-modules are finite-dimensional — and `SimpleAModsRealized` silently says so

Link **L2** of the count behind Zhu Thm 5.3.3 is `#Irr A(𝒱) = #IrrAModIsoClass`, which the
repo reduces to the two named gates `AllIrrBottomRecovers` and
`ZhuVermaAnArchZhu534.SimpleAModsRealized`.  This file settles the *scoping* half of that reduction,
in both directions, and it shows that the gate needs a finiteness hypothesis.

## The obstruction (`simpleAModsRealized_finiteDimensional`)

`SimpleAModsRealized W` demands, for every simple `U`, an `IrrRealization W U`, whose field
`bottomEquiv` is a **`ℂ`-linear equivalence** from the bottom `L(U)_h` onto `U.carrier`, and whose
field `finiteWeights` declares *every* weight space of `L(U)` finite-dimensional.  Composing the two
gives, with no further hypotheses,

  `SimpleAModsRealized W → ∀ U, IsSimpleAMod U → FiniteDimensional ℂ U.carrier`.

So the gate as typed is **not** a theorem for a general vertex operator algebra: Frenkel–Zhu give
`A(V^k(𝔰𝔩₂)) ≅ U(𝔰𝔩₂)`, which has infinite-dimensional simple modules.  Dong–Jiang's `L(U)` is a
theorem about ℕ-gradable modules with no finiteness on the graded pieces; the finiteness enters only
through the repo's `OrdVModule.finrank` field, which `IrrRealization` inherits.  The gate therefore
needs a finiteness hypothesis on `A(𝒱)` — it is *mis-scoped*, not merely unproved.

## The repair is free (`finiteDimensional_of_isSimpleAMod`)

The hypothesis to add costs the count nothing: `FiniteDimensional ℂ (A W)` is *already*
carried by every declaration that consumes the count (`Modularity.CuspFunctionalCount`,
`Modularity.CuspPoint`, `Modularity.WedderburnAMod`).  Under it, every simple bundled
`A(𝒱)`-module *is* finite-dimensional — a simple module is cyclic, hence a quotient of `A(𝒱)`.
That is proved here unconditionally, via the `L1` bridge `isSimpleAMod_iff_isSimpleModule`.

## Main results

* `finiteDimensional_of_isSimpleAMod` — `FiniteDimensional ℂ (A 𝒱)` ⟹ every simple `AMod` is
  finite-dimensional (unconditional);
* `simpleAModsRealized_finiteDimensional` — the certificate that `SimpleAModsRealized` *implies*
  that conclusion, i.e. the named consequence that makes the finiteness hypothesis mandatory
  (unconditional);
* `AMod.cyclic_of_isSimpleAMod` — the cyclicity used by both.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  No `Modules` declaration is modified.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- The `ℂ`-linear orbit map `a ↦ ρ a x` of a bundled `AMod`.  It is `ℂ`-linear because `ρ` is. -/
noncomputable def AMod.orbitMap (U : AMod W) (x : U.carrier) : A W →ₗ[ℂ] U.carrier :=
  (LinearMap.applyₗ x).comp U.ρ

@[simp] theorem AMod.orbitMap_apply (U : AMod W) (x : U.carrier) (a : A W) :
    U.orbitMap x a = U.ρ a x := rfl

/-- **A simple bundled `A(𝒱)`-module is cyclic**: the orbit map at any nonzero vector is onto. -/
theorem AMod.orbitMap_surjective_of_isSimpleAMod (U : AMod W) (hU : IsSimpleAMod U)
    {x : U.carrier} (hx : x ≠ 0) : Function.Surjective (U.orbitMap x) := by
  letI := instRingA W
  letI := U.moduleA
  haveI : IsSimpleModule (A W) U.carrier := (isSimpleAMod_iff_isSimpleModule U).mp hU
  intro y
  have hmem : x ∈ Submodule.span (A W) ({x} : Set U.carrier) :=
    Submodule.subset_span (by simp)
  have hspan : Submodule.span (A W) ({x} : Set U.carrier) = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top (Submodule.span (A W) ({x} : Set U.carrier))).resolve_left
      (fun hc => hx (by rwa [hc, Submodule.mem_bot] at hmem))
  have hy : y ∈ Submodule.span (A W) ({x} : Set U.carrier) := by rw [hspan]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  exact ⟨a, by rw [AMod.orbitMap_apply, ← AMod.smul_def]; exact ha⟩

/-- **Every simple bundled `A(𝒱)`-module is finite-dimensional when `A(𝒱)` is.**  A simple
module is cyclic, hence a `ℂ`-linear quotient of `A(𝒱)`. -/
theorem finiteDimensional_of_isSimpleAMod
    (hfd : FiniteDimensional ℂ (A W)) (U : AMod W) (hU : IsSimpleAMod U) :
    FiniteDimensional ℂ U.carrier := by
  haveI := hfd
  obtain ⟨x, y, hxy⟩ := hU.1
  rcases eq_or_ne x 0 with rfl | hx
  · exact Module.Finite.of_surjective (U.orbitMap y)
      (U.orbitMap_surjective_of_isSimpleAMod hU (Ne.symm hxy))
  · exact Module.Finite.of_surjective (U.orbitMap x)
      (U.orbitMap_surjective_of_isSimpleAMod hU hx)

/-- **The certificate: `SimpleAModsRealized` forces finite-dimensionality of every simple
`A(𝒱)`-module.**  The realization's `bottomEquiv` is a `ℂ`-linear equivalence out of the bottom
weight space, which `finiteWeights` declares finite-dimensional.  Hence the gate cannot hold for a
vertex operator algebra whose Zhu algebra has an infinite-dimensional simple module (e.g.
`A(V^k(𝔰𝔩₂)) ≅ U(𝔰𝔩₂)`), and any use of it must carry a finiteness hypothesis. -/
theorem simpleAModsRealized_finiteDimensional
    (hreal : SimpleAModsRealized W) (U : AMod W) (hU : IsSimpleAMod U) :
    FiniteDimensional ℂ U.carrier := by
  obtain ⟨R⟩ := hreal U hU
  haveI : FiniteDimensional ℂ ((R.graded.toLWModule R.finiteWeights).toAMod.carrier) :=
    R.finiteWeights R.lowestWeight
  exact R.bottomEquiv.toLinearEquiv.finiteDimensional

end VOA
