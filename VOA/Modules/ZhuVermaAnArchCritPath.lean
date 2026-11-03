/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchInducedAssign
import VOA.Modules.ZhuVermaAnArchGenBottom

/-!
# The critical path of the Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` (Theorem 5.3.4)

This file **audits** the dependency graph of the final Zhu bijection and proves the single cleanest
headline conditional theorem, `zhuBijection_critpath`, stating the full
`Φ(𝒱) ↔ Irr A(𝒱)` bijection given **exactly** the minimal remaining hypothesis set, with every
already-proven piece plugged in as a term.

## Audit conclusion — what the unconditional bijection actually consumes

Tracing every headline of the architecture
(`ZhuVermaAnArchTier3Discharge.zhuBijection_of_layerData`,
`ZhuVermaAnArchFreenessAssemble.zhuBijection_of_freenessData`,
`ZhuVermaAnArchGenBottom.zhuBijection_of_genFromBottom`,
`ZhuVermaAnArchInducedAssign.zhuBijection_of_bottomSurvives`,
`ZhuVermaAnArchGameTwo.zhuBijection_of_universal`,
`ZhuVermaAnArchRigidity.zhuBijection_of_rigidity`,
`ZhuBijection.zhuBijection_of_inducedAssignment`), they ALL funnel through one backbone:

```
zhuBijection_of_bottomSurvives / _genFromBottom / _layerData / _freenessData
        ↓
zhuBijection_of_universal        (GeneratedFromBottom ⟹ IrredBottomRigidity)
        ↓
zhuBijection_of_rigidity         (IrredBottomRigidity ⟹ RealizesSelf)
        ↓
zhuBijection_of_inducedAssignment  (RealizesSelf ⟹ Bijective (forwardMap))
```

and `forwardMap : LWModuleIsoClass W → AModIsoClass W` is built (`ZhuBijection`) from the
**bundled `A(𝒱)`-module** `AMod W`, whose only algebraic laws are

* `ρ_one`  : `[𝟙]` acts as `1`              (`ZhuModule.actA_one`),
* `ρ_mul`  : `[u * v] = [u] · [v]` for the **Zhu product `*` of `A(𝒱) = A₀(𝒱)`**
            (`ZhuModule.actA_mk_mul`).

These are the **`A₀(𝒱)` (n = 0) descended-action facts** (5.3.9a/5.3.9b), already PROVEN
axiom-clean in `Modules.ZhuModule`.  The generalized-Verma realization `M(U)` / `M̄(U)` is built
(`ZhuVermaAnArchVHatRepMU`, `ZhuVermaAnArchAssembly`, `ZhuVermaAnArchMULW`) from a
**`V̂`-representation** `ρ : VHatRep W M` — the *loop/affine* Lie-algebra action (`VHatModeData`:
loop-mode action + descent through `Im D` + the Lie-morphism bracket compatibility) — together with
the **module Jacobi 5.3.1b** (`isModuleJacobi_quotientRep`, unconditional on the defect quotient)
and the `ℂ`-grading by `L₀ = h + n`.

## Headline result: A_n associativity (n ≥ 1) is NOT on the critical path

The associative-algebra structure `IsAssociativeAlgebra W n` (n ≥ 1) and the homomorphism
`AnFull.AssocHom` / the `AssocVecExpand` expansion (files
`ZhuVermaAnArchAssocCore`, `ZhuVermaAnArchAnAssoc`, `ZhuVermaAnArchAnAssocCore2`,
`ZhuVermaAnArchAssoc`, `ZhuVermaAnArchAssocHom`, `ZhuVermaAnArchAssocHomVec`,
`ZhuVermaAnArchAssocScalarN`) do **not appear anywhere** in the transitive import closure of the
bijection headlines, and no field of any consumed hypothesis structure (`AMod`, `MUModuleData`,
`MUVHatData`, `VHatModeData`, `LUFamily`, `RealizesIrrData`, `BottomSurvives`,
`InducedAssignment`, `GeneratedFromBottom`) refers to `A_n`-associativity for `n ≥ 1`.

The bijection needs only:
* **`A₀(𝒱)` associativity / the descended action** — already proven (`ZhuModule`); and
* **the bimodule / generalized-Verma structure** of `M(U)` — carried as the hypotheses below.

So the ~1300-line `AssocVecExpand` `A_n`-associativity job is a *sibling* result, useful for the
finer Frenkel–Zhu `A_n`-bimodule theory, but it is **off** the `Φ(𝒱) ↔ Irr A(𝒱)` critical path.

## The minimal remaining hypothesis set

`zhuBijection_critpath` consumes **exactly**:

1. `A : InducedAssignment W` — the lifting datum `U ↦ M̄(U)` (its three fields `realize`,
   `realizes` = **bottom survival**, `isoInvariant` = **functoriality**).  Built in the architecture
   from `MUVHatData` (`ρ`/`VHatModeData`, `MUGradedAction`, the grading, the bottom residual
   `BottomOrbit`/freeness `GradedModeVanish`).  No `A_n`-assoc (n ≥ 1).
2. `hall : AllLWIrreducible W` — the ambient irreducibility scope of the statement (`Φ(𝒱)` = the
   *irreducible* classes).
3. `hirr : A.RealizeIrreducible` — the realizations `M̄(U)` are irreducible (`L(U)`).
4. `hgen : GeneratedFromBottom W` — the universal property of `M(U)` (generation-from-bottom /
   Frobenius reciprocity for irreducibles) ⟹ irreducible-bottom rigidity (the injective half).

Every other piece — `forwardMap`, the `A₀(𝒱)`-action laws, the round-trip
`forwardMap ∘ invFun = id`, the rigidity reduction — is supplied as a **term**.

## Status

Axiom-clean `[propext, Classical.choice, Quot.sound]`.  No `sorry`, no new axiom, no `pbw`.
-/

namespace VOA

open scoped BigOperators
open VertexOperatorAlgebra

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The minimal bundled critical-path hypotheses -/

/-- **The minimal hypothesis bundle on the critical path of the Zhu bijection (Theorem 5.3.4).**

Every field is a genuine, named obligation of the generalized-Verma / Frenkel–Zhu theory — and
**none** of them is `A_n`-associativity for `n ≥ 1`.  This is the exact data the unconditional
`Φ(𝒱) ↔ Irr A(𝒱)` bijection consumes.

* `A` — the lifting datum `U ↦ M̄(U)` (carrier, field `Y_{M̄(U)}`, module Jacobi 5.3.1b, grading all
  internal; the only analytic field is **bottom survival** `A.realizes`, plus **functoriality**
  `A.isoInvariant`);
* `hall` — the ambient irreducibility scope (the bijection is between the *irreducible* classes);
* `hirr` — the realizations are irreducible (`M̄(U) = L(U)`);
* `hgen` — generation-from-bottom (the universal property of `M(U)`), the injective-half crux. -/
structure CritPathData (W : VertexOperatorAlgebra 𝒱) where
  /-- The lifting datum `U ↦ M̄(U)` (the generalized-Verma realization; bottom survival +
  functoriality).  Built from `MUVHatData` (`ρ`/`VHatModeData`, `MUGradedAction`, grading,
  bottom residual / freeness); no `A_n`-assoc for `n ≥ 1`. -/
  A : InducedAssignment W
  /-- **Ambient irreducibility scope.** Every bundled lowest-weight module is irreducible — the
  standing restriction of Theorem 5.3.4. -/
  hall : InducedAssignment.AllLWIrreducible W
  /-- **The realizations are irreducible** (`M̄(U) = L(U)`). -/
  hirr : A.RealizeIrreducible
  /-- **Generation-from-bottom** — the universal property of `M(U)` (Frobenius reciprocity for
  irreducibles), the injective-half crux. -/
  hgen : InducedAssignment.GeneratedFromBottom W

namespace CritPathData

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The Zhu bijection `Φ(𝒱) ↔ Irr A(𝒱)` from the minimal critical-path bundle.** The forward map
`forwardMap W = ([M] ↦ [M_h])` is a bijection.  Every already-proven piece is plugged in:
`forwardMap` and its `A₀(𝒱)`-action laws (`ZhuBijection`/`ZhuModule`), the rigidity reduction
(`zhuBijection_of_rigidity`), and the universal-property bridge
(`GeneratedFromBottom ⟹ IrredBottomRigidity`, `zhuBijection_of_universal`).
**No `A_n`-associativity for `n ≥ 1` is consumed.** -/
theorem bijective (D : CritPathData W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal D.A D.hall D.hirr D.hgen

end CritPathData

/-! ## The single cleanest headline conditional theorem -/

/-- **`zhuBijection_critpath` — the full `Φ(𝒱) ↔ Irr A(𝒱)` bijection of Zhu Theorem 5.3.4, on the
minimal critical path.**

Given **exactly** the minimal remaining hypothesis set —

* `A : InducedAssignment W`              (the `U ↦ M̄(U)` lifting datum: bottom survival +
                                          functoriality; built from `ρ`/`VHatModeData`,
                                          `MUGradedAction`, grading, bottom residual / freeness
                                          `GradedModeVanish`; **no `A_n`-assoc for `n ≥ 1`**),
* `hall : AllLWIrreducible W`            (the irreducibility scope of the statement),
* `hirr : A.RealizeIrreducible`          (the realizations are `L(U)`),
* `hgen : GeneratedFromBottom W`         (the universal property of `M(U)` / the injective half)

— the forward map `forwardMap W : Φ(𝒱) → Irr A(𝒱)`, `[M] ↦ [M_h]`, is a **bijection**.

This is the cleanest statement of Theorem 5.3.4: the easy direction `[M] ↦ [M_h]` rests on the
**`A₀(𝒱)`** descended action (PROVEN, `ZhuModule`); the inverse / injectivity rests on the
generation-from-bottom universal property (`hgen`) of the generalized-Verma module, whose existence
is the `A : InducedAssignment` datum.  **`A_n` associativity (`n ≥ 1`) is not in the hypothesis
list** — it is off the critical path. -/
theorem zhuBijection_critpath {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W)
    (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible)
    (hgen : InducedAssignment.GeneratedFromBottom W) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_universal A hall hirr hgen

/-! ## Equivalent entry points (all consume the same A₀-only minimal data)

For downstream callers that prefer to supply the bottom-survival datum or the generation-from-bottom
family directly (rather than a pre-assembled `InducedAssignment` + `GeneratedFromBottom`), the
following two corollaries re-expose `zhuBijection_critpath` through the two sibling assemblies. Both
still avoid `A_n`-associativity for `n ≥ 1`. -/

/-- **Critical path via bottom survival.** Identical content, with the lifting datum supplied as a
`BottomSurvives W` (per-`U` realization + bottom survival + functoriality). -/
theorem zhuBijection_critpath_of_bottomSurvives {W : VertexOperatorAlgebra 𝒱}
    (B : InducedAssignment.BottomSurvives W)
    (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : (InducedAssignment.inducedAssignment_of_bottomSurvives B).RealizeIrreducible)
    (hgen : InducedAssignment.GeneratedFromBottom W) :
    Function.Bijective (forwardMap W) :=
  InducedAssignment.zhuBijection_of_bottomSurvives B hall hirr hgen

/-- **Critical path via generation-from-bottom.** Identical content, with the injective half
supplied as the canonical `L(U)`-family `F` + functoriality `hiso` + the lifting family `R`
(`RealizesIrrFamily`, the universal property of `M(U)`). -/
theorem zhuBijection_critpath_of_genFromBottom {W : VertexOperatorAlgebra 𝒱}
    (A : InducedAssignment W) (hall : InducedAssignment.AllLWIrreducible W)
    (hirr : A.RealizeIrreducible) (F : InducedAssignment.LUFamily W)
    (hiso : ∀ U₁ U₂ : AMod W, Nonempty (AModEquiv W U₁ U₂) →
      LWModule.Iso W (F.K U₁) (F.K U₂))
    (R : InducedAssignment.RealizesIrrFamily F) :
    Function.Bijective (forwardMap W) :=
  zhuBijection_of_genFromBottom A hall hirr F hiso R

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
