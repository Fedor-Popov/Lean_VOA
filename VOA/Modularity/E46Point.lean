/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.CuspPoint

/-!
# Interior points of `ℍ` as `ℂ`-points of `E46`

`Modularity.CuspPoint` exhibits the cusp as a `ℂ`-point `evInfty : E46 →ₐ[ℂ] ℂ` of the level-one
structure ring `E46 = ℂ[E₄, E₆]`.  Residual **(a)** — transporting Zhu's count from the cusp to a
point `z₀ ∈ ℍ` — compares the fibre of the relation module at `evInfty` with the fibre at an
*interior* point, so the interior points must be `ℂ`-points too.

Because `E46` is a subalgebra of the *function* algebra `UpperHalfPlane → ℂ`, that direction is
free: evaluation at `z₀` is already an algebra map, and it is surjective (it fixes the constants),
so its kernel is a maximal ideal with residue field `ℂ` — exactly like `ker evInfty`.

## Main results

* `evAt` — evaluation `E46 →ₐ[ℂ] ℂ` at a point of `ℍ`;
* `evAt_surjective`, `evInfty_surjective`;
* `ker_evAt_isMaximal`, `ker_evInfty_isMaximal` — both points are genuine `ℂ`-points;
* `evAt_ne_evInfty_of_apply_ne` — a separating criterion.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  This is infrastructure for (a); it does **not** by
itself transport the count.
-/

namespace VOA

open Filter Topology

/-- **Evaluation of `E46` at an interior point** `z₀ ∈ ℍ`. -/
noncomputable def evAt (z₀ : UpperHalfPlane) : E46 →ₐ[ℂ] ℂ where
  toFun f := (f : UpperHalfPlane → ℂ) z₀
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem evAt_apply (z₀ : UpperHalfPlane) (f : E46) :
    evAt z₀ f = (f : UpperHalfPlane → ℂ) z₀ := rfl

/-- A `ℂ`-algebra map to `ℂ` is surjective: it fixes the constants. -/
theorem algHom_to_C_surjective (φ : E46 →ₐ[ℂ] ℂ) : Function.Surjective φ := by
  intro c
  refine ⟨algebraMap ℂ E46 c, ?_⟩
  rw [AlgHom.commutes]
  rfl

theorem evAt_surjective (z₀ : UpperHalfPlane) : Function.Surjective (evAt z₀) :=
  algHom_to_C_surjective _

theorem evInfty_surjective : Function.Surjective evInfty :=
  algHom_to_C_surjective _

/-- **Every `ℂ`-point of `E46` has a maximal kernel.**  `E46 ⧸ ker φ ≃ ℂ`, a field. -/
theorem ker_isMaximal (φ : E46 →ₐ[ℂ] ℂ) :
    (RingHom.ker (φ : E46 →+* ℂ)).IsMaximal := by
  exact RingHom.ker_isMaximal_of_surjective (φ : E46 →+* ℂ) (algHom_to_C_surjective φ)

/-- The interior point `z₀` is a `ℂ`-point of `E46`. -/
theorem ker_evAt_isMaximal (z₀ : UpperHalfPlane) :
    (RingHom.ker ((evAt z₀) : E46 →+* ℂ)).IsMaximal :=
  ker_isMaximal _

/-- The cusp is a `ℂ`-point of `E46`. -/
theorem ker_evInfty_isMaximal : (RingHom.ker (evInfty : E46 →+* ℂ)).IsMaximal :=
  ker_isMaximal _

/-- If some element of `E46` takes different values at `z₀` and at the cusp, the two points are
distinct — the separating criterion the transport argument needs. -/
theorem evAt_ne_evInfty_of_apply_ne {z₀ : UpperHalfPlane} {f : E46}
    (hf : evAt z₀ f ≠ evInfty f) : evAt z₀ ≠ evInfty := by
  intro hc
  exact hf (by rw [hc])

end VOA
