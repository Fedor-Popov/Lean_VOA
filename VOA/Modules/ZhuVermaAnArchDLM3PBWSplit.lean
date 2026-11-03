/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3Survival
import VOA.Modules.ZhuVermaAnArchBottomAn

/-!
# The PBW input of DLM3 §4, as a **named hypothesis** (never an axiom)

Dong–Li–Mason (`q-alg/9612010v2`) build `M_n(U) = U(V̂) ⊗_{U(P_n)} U` and then write

> "If we give `U` degree `n`, the `ℤ`-gradation of `V̂` lifts to `M_n(U)` … **The PBW theorem
> implies that** `M_n(U)(i) = U(V̂)_{i−n} U`."

This file originally packaged two consequences of the Poincaré–Birkhoff–Witt argument as a
`structure` of `Prop`-valued fields threaded explicitly through every theorem that needs it.
The companion `ZhuVermaAnArchDLM3PBWIndependence` proves level independence unconditionally,
so the exact remaining trust boundary is bottom injectivity alone; the two-field structure is
retained as the existing API. **No `axiom` is declared here**, and this parameterized file does not
use the theorem `VOA.pbw : PBWPrinciple`.
`ZhuVermaAnArchDLM3AdjointBottom` proves concrete `adjointPBWFreeness` and
`adjointBottomProjection` instances, and `Examples.HeisenbergPBWFreeness` gives a nonzero
rank-one Heisenberg specialization, all without `pbw`. For the general
`regularAMod` used downstream, the companion `ZhuVermaAnArchDLM3PBWAxiom` supplies
`voaPBWFreeness` and `voaPBWBottomProjection` by specializing the generic relative-induction field
of `pbw`; `voaPBWBottomInjective` is the specialization theorem, not a second axiom. No implication
from the affine-vacuum field alone is claimed.

## What PBW gives, and what is carried

`U(V̂)` is free as a right `U(P_n)`-module (PBW applied to the vector-space splitting
`V̂ = 𝔫 ⊕ P_n`), equivalently the Harish-Chandra decomposition
`U(V̂) = U(P_n) ⊕ 𝔫 · U(V̂)` holds.  On the induced module this yields exactly:

1. **faithfulness of the bottom** — `u ↦ [1 ⊗ u]` is injective (`bottom_injective`), i.e.
   `M_n(U)(n) ⊇ U`; and
2. **directness of the level filtration** — the levels `M_n(U)(k)` are independent
   (`levels_iSupIndep`), i.e. the `ℤ`-grading of `M_n(U)` is an internal direct sum. This field is
   supplied unconditionally by `levCover_iSupIndep` in `ZhuVermaAnArchDLM3PBWIndependence`.

Both are recorded in `PBWFreeness`.  From them this file derives, as *theorems*:

* `PBWFreeness.isInternal` — `DirectSum.IsInternal (levCover P)`, the hypothesis `hInt` consumed by
  `bottomSurvives_an` / `bottomSurvives_full_an` (`ZhuVermaAnArchBottomAn`);
* `PBWFreeness.bottomProjection` (at `n = 0`) — the degree-`0` projection `π₀ : M_0(U) → U` of
  `ZhuVermaAnArchDLM3Survival`, i.e. the `BottomProjection` datum through which DLM3 extend
  `U* = Hom_ℂ(U,ℂ)` to all of `M_0(U)`;
* `PBWFreeness.deg0Proj_indBottom` — `π₀` fixes the bottom.

The **spanning** half of DLM3's PBW step is *not* carried: at `n = 0` it is already proved without
any PBW assumption in `ZhuVermaAnArchDLM3Survival` (`levCover_spanning`,
`levCover_zero_eq_range`, `levCover_eq_bot_of_neg`). Level independence is also unconditional.
Thus only bottom injectivity is the mathematical residue in general. Concrete adjoint and
Heisenberg instances are proved without `pbw`; the project-wide general instance is supplied by
the theorem `voaPBWBottomInjective`, derived from `pbw.inducedBottom`.

## References
DLM3 (`q-alg/9612010v2`) §4, (4.1) and the paragraph after it;
DLM2 (`q-alg/9509005`) §6 (same PBW step at `n = 0`);
`ZhuVermaAnArchDLM3Survival` (`BottomProjection`, `bottomProjectionOfDisjoint`,
`levCover_zero_eq_range`), `ZhuVermaAnArchDLM3Level` (`levCover`, `levCover_spanning`),
`ZhuVermaAnArchBottomAn` (`deg0Proj`, `bottomSurvives_an`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {n : ℕ} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- **The PBW input of DLM3 §4, carried as data.**

`U(V̂)` free over `U(P_n)` (equivalently the Harish-Chandra split
`U(V̂) = U(P_n) ⊕ 𝔫·U(V̂)`) motivated the two fields below on
`M_n(U) = U(V̂) ⊗_{U(P_n)} U`. The companion Euler-operator theorem proves the second field
unconditionally, reducing this package to bottom injectivity (`pbwFreeness_iff_bottom_injective`).
Concrete adjoint and Heisenberg instances are proved without the trusted PBW principle. The
companion `voaPBWFreeness` supplies the general package, including the downstream `regularAMod`
case, from the generic relative-induction field of the theorem `VOA.pbw : PBWPrinciple`
. Every parameterized downstream statement displays its
assumption in the signature. A
`#print axioms` result of `[propext, Classical.choice, Quot.sound]` does not report this explicit
parameter and therefore must not be read as an unconditional or satisfiability result. -/
structure PBWFreeness (P : ParabolicRep W n U) : Prop where
  /-- **PBW, part 1** — the bottom `U` embeds: `u ↦ [1 ⊗ u]` is injective. -/
  bottom_injective : Function.Injective (indBottom P)
  /-- **PBW part 2, a theorem** — the levels `M_n(U)(k) = U(V̂)_{k−n}U` are
  independent. `levCover_iSupIndep` supplies this field unconditionally; together with
  `levCover_spanning` it gives the internal `ℤ`-grading of `M_n(U)`. -/
  levels_iSupIndep : iSupIndep (levCover P)

namespace PBWFreeness

variable {P : ParabolicRep W n U}

/-- **The `ℤ`-grading of `M_n(U)` is an internal direct sum.** This base-file declaration reads
independence from the two-field package; `levCover_iSupIndep` proves it unconditionally.
Spanning is `levCover_spanning`. This is the `hInt` argument of
`bottomSurvives_an` / `bottomSurvives_full_an`. -/
theorem isInternal (hP : PBWFreeness P) : DirectSum.IsInternal (levCover P) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hP.levels_iSupIndep
    (levCover_spanning P)

/-- The bottom level is disjoint from the span of all other levels. -/
theorem disjoint_levels (hP : PBWFreeness P) :
    Disjoint (levCover P (n : ℤ)) (⨆ k : {k : ℤ // k ≠ (n : ℤ)}, levCover P (k : ℤ)) := by
  have h := (iSupIndep_def.mp hP.levels_iSupIndep) (n : ℤ)
  refine h.mono_right ?_
  refine iSup_le fun k => ?_
  exact le_iSup_of_le (k : ℤ) (le_iSup (fun _ : (k : ℤ) ≠ (n : ℤ) => levCover P (k : ℤ)) k.2)

end PBWFreeness

section LevelZero

variable {Q : ParabolicRep W 0 U}

/-- **The degree-`0` projection `π₀ : M_0(U) → U` from `PBWFreeness`.** At `n = 0`, spanning and
level independence are theorems, so the companion boundary API constructs this projection from
bottom injectivity alone. Concrete adjoint and Heisenberg instances are axiom-free; the project
supplies the general downstream projection as `voaPBWBottomProjection`, derived from the generic
relative-induction field of the theorem `VOA.pbw`. -/
noncomputable def PBWFreeness.bottomProjection (hP : PBWFreeness Q) : BottomProjection Q := by
  refine bottomProjectionOfDisjoint Q hP.bottom_injective ?_
  have h := hP.disjoint_levels
  rwa [Nat.cast_zero, levCover_zero_eq_range] at h

@[simp] theorem PBWFreeness.bottomProjection_bottom (hP : PBWFreeness Q) (u : U) :
    hP.bottomProjection.proj (indBottom Q u) = u :=
  hP.bottomProjection.proj_bottom u

/-- `π₀` (the internal-grading degree-`0` projection of `ZhuVermaAnArchBottomAn`) fixes the
bottom of `M_0(U)`. -/
theorem PBWFreeness.deg0Proj_indBottom (hP : PBWFreeness Q) (u : U) :
    VHatRep.deg0Proj hP.isInternal (indBottom Q u) = indBottom Q u := by
  refine VHatRep.deg0Proj_eq_self hP.isInternal ?_
  have h := indBottom_mem_levCover Q u
  rwa [Nat.cast_zero] at h

end LevelZero

end DLM3
end VHat

end VOA

-- Axiom check. Explicit `PBWFreeness` parameters are not shown by `#print axioms`.
