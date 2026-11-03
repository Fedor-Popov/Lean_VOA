/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Examples.TrivialRationalityLattice
import VOA.Modules.StronglyRational

/-!
# The trivial VOA is strongly rational — the positive witness

`Modules/StronglyRational.lean` defines `StronglyFinite` (Creutzig–Gannon, arXiv:1605.04630v1,
§2.2) and `StronglyRational` (Dong–Mason, arXiv:math/0201318v1, §3; McRae, arXiv:2108.01898v3,
§2.2).  Both are four-conjunct bundles, and a bundle that no VOA satisfies would make every
theorem about it worthless — and every future `¬ StronglyRational …` vacuously true.

This file closes that gap.  `trivialVOA = ℂ𝟙` (the rank-zero lattice VOA,
`Examples/ZhuInstantiation.lean`) satisfies **all four** conjuncts, and each is discharged
separately rather than by fiat:

* **simple** — `trivial_isSimple`, from `𝒱 = ℂ𝟙` and `𝟙 ≠ 0`;
* **self-dual** (`𝒱 ≅ 𝒱∨`, in McRae §2.2's nondegenerate-invariant-form formulation) —
  `trivial_selfDual`, via the canonical FHL form, which is genuinely nondegenerate here because
  `L₁` annihilates all of `ℂ𝟙` (strong CFT type) and `𝒱` is simple;
* **`C₂`-cofinite** — a quotient of a one-dimensional space;
* **rational** (`AdmissiblyRational`, Zhu / Dong–Li–Mason) — `trivial_admissiblyRational`
  (`Examples/TrivialAdmissiblyRational.lean`).

⚠ **The self-duality here is not the vacuous predicate.**  `Modules/Contragredient.lean`'s
`SelfContragredient` holds of *every* module (`selfContragredient_of_ordVModule`), so a witness for
it would prove nothing.  `trivial_selfDual` is a witness for
`VertexOperatorAlgebra.SelfDual` — the existence of a **nondegenerate fully invariant bilinear
form** — which by `selfDual_iff` is equivalent to Dong–Mason's strong CFT type `L₁𝒱₁ = 0`, a
condition that genuinely fails for VOAs of CFT type with a non-quasiprimary weight-one state
(Dong–Mason, arXiv:math/0201318v1, §2, note such examples exist).

⚠ **Consistency cross-check.**  `trivialVOA` is also the VOA for which
`Examples/TrivialRationalityLattice.lean` proves `Regular trivialVOA`, and
`Examples/ZhuInstantiation.lean` proves `IsSemisimpleRing (A trivialVOA)`.  So the two routes to
`StronglyRational` agree: `trivial_stronglyRational` (through `𝒱 = ℂ𝟙`) and
`trivial_stronglyRational_of_regular` (through `stronglyRational_of_regular`, the
Creutzig–Gannon "in addition regular" route) both land, as they must.

## Status
`sorry`-free, `admit`-free, `native_decide`-free, no new axioms, `VOA.pbw`-free.
-/

namespace VOA

/-- `trivialVOA` is simple: its space is `ℂ𝟙` with `𝟙 ≠ 0`. -/
theorem trivial_isSimple : trivialVOA.IsSimple :=
  VertexOperatorAlgebra.isSimple_of_span_vacuum trivialVacuum_ne_zero trivial_span_vacuum

/-- `trivialVOA` is of **strong CFT type**: `L₁` annihilates `𝒱₁` (indeed all of `𝒱 = ℂ𝟙`).
Dong–Mason, arXiv:math/0201318v1, §2, eq. (2.2). -/
theorem trivial_L_one_grading_one_eq_zero (v : LatGen.LatModuleGen (stdLattice 0))
    (_hv : v ∈ trivialVOA.grading 1) : trivialVOA.L 1 v = 0 :=
  VertexOperatorAlgebra.L_one_eq_zero_of_span_vacuum trivial_span_vacuum v

/-- `trivialVOA` is **self-dual**: it carries a nondegenerate fully invariant bilinear form.
This is McRae §2.2 clause (2), *not* the vacuous `SelfContragredient`. -/
theorem trivial_selfDual : trivialVOA.SelfDual :=
  VertexOperatorAlgebra.selfDual_of_L_one_grading_one_eq_zero trivialVacuum_ne_zero
    trivial_L_one_grading_one_eq_zero trivial_isSimple

/-- **The trivial VOA is strongly rational** (Dong–Mason §3 / McRae §2.2). -/
theorem trivial_stronglyRational : StronglyRational trivialVOA :=
  stronglyRational_of_span_vacuum trivialVacuum_ne_zero trivial_span_vacuum

/-- **The trivial VOA is strongly finite** (Creutzig–Gannon §2.2). -/
theorem trivial_stronglyFinite : StronglyFinite trivialVOA :=
  trivial_stronglyRational.toStronglyFinite

/-- The **Creutzig–Gannon route** to the same conclusion: `StronglyFinite` plus `Regular`
(`Examples/TrivialRationalityLattice.trivial_regular`).  It agrees with
`trivial_stronglyRational`, as `Prop`-valued statements must. -/
theorem trivial_stronglyRational_of_regular : StronglyRational trivialVOA :=
  stronglyRational_of_regular trivial_stronglyFinite trivial_regular

/-- The CFT-type conjunct, spelled out at the witness: `𝒱ₙ = 0` for `n < 0`, `𝒱₀ = ℂ𝟙`,
`dim 𝒱₀ = 1`, and every `𝒱ₙ` finite-dimensional. -/
theorem trivial_cftType :
    (∀ n : ℤ, n < 0 → trivialVOA.grading n = ⊥) ∧
      trivialVOA.grading 0 = ℂ ∙ trivialVOA.vacuum ∧
      Module.finrank ℂ (trivialVOA.grading 0) = 1 ∧
      ∀ n : ℤ, FiniteDimensional ℂ (trivialVOA.grading n) :=
  trivial_stronglyFinite.cftType

/-- ⚠ The contrast that makes the witness meaningful: `SelfContragredient` holds for the adjoint
module of `trivialVOA` — but it holds for **every** module of **every** VOA
(`selfContragredient_of_ordVModule`), so unlike `trivial_selfDual` it says nothing. -/
theorem trivial_selfContragredient_is_uninformative :
    SelfContragredient (adjointModule trivialVOA) :=
  selfContragredient_of_ordVModule _

end VOA
