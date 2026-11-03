/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchDLM3PBWIndependence

/-!
# The exact trust boundary for the DLM3 bottom projection

At level zero, the unconditional theorems `levCover_spanning`, `levCover_zero_eq_range`, and
`levCover_iSupIndep` remove the spanning and level-independence parts of the PBW argument.  The
exact remaining proposition is only that the bottom map is injective.

`BottomSeparation` records the geometric form used by the projection construction: injectivity of
the bottom and disjointness from the other levels.  The Euler-operator theorem
`levCover_iSupIndep` proves the disjointness unconditionally, so this file proves that
`BottomSeparation`, existence of a `BottomProjection`, and bottom injectivity are equivalent. This
file is axiom-free and parameterized by that exact residue. The companion
`ZhuVermaAnArchDLM3PBWAxiom` supplies it generally by specializing the relative-induction field of
the theorem `VOA.pbw : PBWPrinciple`; no implication from the
principle's affine-vacuum field alone is claimed.

## References

Dong--Li--Mason (`q-alg/9612010v2`) Section 4, equation (4.1);
`ZhuVermaAnArchDLM3Survival` (`bottomProjectionOfDisjoint`, `levCover_zero_eq_range`);
`ZhuVermaAnArchDLM3PBWSplit` (`PBWFreeness`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat
namespace DLM3

variable {W : VertexOperatorAlgebra 𝒱} {U : Type u} [AddCommGroup U] [Module ℂ U]

/-- **The exact level-zero separation assumption needed for `BottomProjection`.**

The first field says that `u ↦ [1 ⊗ u]` really embeds the proposed bottom.  The second says that
this bottom has zero intersection with the span of every nonzero level.  The second field is
retained because it states the geometric separation property directly; by
`bottomSeparation_iff_bottom_injective` below it adds no assumption beyond the first field. -/
structure BottomSeparation (Q : ParabolicRep W 0 U) : Prop where
  /-- The canonical bottom map has trivial kernel. -/
  bottom_injective : Function.Injective (indBottom Q)
  /-- The bottom range meets the span of all nonzero levels only at zero. -/
  bottom_disjoint_other :
    Disjoint (LinearMap.range (indBottom Q))
      (⨆ k : {k : ℤ // k ≠ (0 : ℤ)}, levCover Q (k : ℤ))

namespace BottomSeparation

variable {Q : ParabolicRep W 0 U}

/-- A separated bottom produces the DLM3 projection.  This uses only the unconditional spanning
theorems packaged by `bottomProjectionOfDisjoint`. -/
noncomputable def bottomProjection (h : BottomSeparation Q) : BottomProjection Q :=
  bottomProjectionOfDisjoint Q h.bottom_injective h.bottom_disjoint_other

end BottomSeparation

namespace BottomProjection

variable {Q : ParabolicRep W 0 U}

/-- A bottom projection forces the exact separation property: its retraction law proves
injectivity, and its off-bottom vanishing proves disjointness from all nonzero levels. -/
theorem bottomSeparation (Pr : BottomProjection Q) : BottomSeparation Q := by
  refine ⟨Pr.indBottom_injective, ?_⟩
  rw [Submodule.disjoint_def]
  intro z hzBottom hzOther
  obtain ⟨u, rfl⟩ := hzBottom
  have hkill : Pr.proj (indBottom Q u) = 0 := by
    refine Submodule.iSup_induction
      (fun k : {k : ℤ // k ≠ (0 : ℤ)} => levCover Q (k : ℤ))
      (motive := fun x => Pr.proj x = 0) hzOther ?_ ?_ ?_
    · intro k x hx
      exact Pr.proj_levCover k.2 hx
    · exact map_zero Pr.proj
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  have hu : u = 0 := by
    rw [← Pr.proj_bottom u, hkill]
  rw [hu, map_zero]

end BottomProjection

namespace PBWFreeness

variable {Q : ParabolicRep W 0 U}

/-- Full `PBWFreeness` implies the geometric boundary datum through its bottom projection. -/
theorem bottomSeparation (hP : PBWFreeness Q) : BottomSeparation Q :=
  hP.bottomProjection.bottomSeparation

end PBWFreeness

/-- **Exactness of the reduced trust boundary.**  At level zero, carrying a projection is
equivalent to assuming only bottom injectivity and bottom-versus-other-level separation. -/
theorem nonempty_bottomProjection_iff_bottomSeparation (Q : ParabolicRep W 0 U) :
    Nonempty (BottomProjection Q) ↔ BottomSeparation Q := by
  constructor
  · rintro ⟨Pr⟩
    exact Pr.bottomSeparation
  · intro h
    exact ⟨h.bottomProjection⟩

/-- The geometric separation datum is exactly bottom injectivity: independence of the other
levels is the unconditional Euler-operator theorem `levCover_iSupIndep`. -/
theorem bottomSeparation_iff_bottom_injective (Q : ParabolicRep W 0 U) :
    BottomSeparation Q ↔ Function.Injective (indBottom Q) := by
  constructor
  · exact BottomSeparation.bottom_injective
  · intro hinj
    exact (bottomProjectionOfInjective Q hinj).bottomSeparation

/-- **Exact reduced trust boundary.** A level-zero bottom projection exists if and only if the
canonical bottom map is injective; spanning and independence of levels are theorems. -/
theorem nonempty_bottomProjection_iff_bottom_injective (Q : ParabolicRep W 0 U) :
    Nonempty (BottomProjection Q) ↔ Function.Injective (indBottom Q) := by
  rw [nonempty_bottomProjection_iff_bottomSeparation,
    bottomSeparation_iff_bottom_injective]

end DLM3
end VHat

end VOA

-- Axiom check: this reports only Lean/Mathlib's standard logical axioms.
