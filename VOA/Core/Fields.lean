/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexAlgebra
import VOA.Foundations.IteratedLaurent

/-!
# The iterated product field `Y(u,z₁)Y(v,z₂)x`  (Gannon §5.1.2; Kac §4)

The vertex-algebra half of the "fields framework" underlying the
reconstruction/duality theorems.  For states `u, v, x`, the iterated product
`Y(u,z₁)Y(v,z₂)x` is the two-variable distribution with `z₁ᵐz₂ⁿ`-coefficient
`uₘ(vₙ x)`.  Its key property is that it **lies in `𝒱((z₁))((z₂))`**: by VA5 (regularity)
`vₙ x = 0` for `n ≪ 0`, which kills the entire `z₁`-column, so the `z₂`-support is
bounded below uniformly in the `z₁`-power (`IsBddBelow₂`, from `Foundations.IteratedLaurent`).

Combined with the `(z₁-z₂)ᴺ` cancellation, this gives the ready-to-use principle
`Yprod_ext`: two states whose iterated product fields agree after multiplication by
`(z₁-z₂)ᴺ` are *equal as product fields*.  This is the lower-truncation input the Goddard
uniqueness theorem consumes.

## Dependencies
* `VOA.Core.VertexAlgebra`, `VOA.Foundations.IteratedLaurent`.

## Status
Complete & `sorry`-free / axiom-free.  `Yprod`, `Yprod_bddBelow` and the cancellation
corollary `Yprod_ext` are proved — the lower-truncation input that the Goddard uniqueness
theorem (`Core.Goddard`) consumes, used in the reconstruction cascade
(`Core.Dong` Dong's lemma for all `n`, `Core.Reconstruction`); see `README.md`.

## References
* Gannon §5.1.2; Kac, *VA for Beginners* §4 (fields, lower truncation, uniqueness).
-/

namespace VOA

open Module (End)

universe u

namespace PreVertexAlgebra

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- The iterated product field `Y(u,z₁)Y(v,z₂)x` as a two-variable distribution: its
`z₁ᵐz₂ⁿ`-coefficient is `uₘ(vₙ x)` (Gannon §5.1.2). -/
def Yprod (V : PreVertexAlgebra 𝒱) (u v x : 𝒱) : FormalDist₂ 𝒱 :=
  fun m n => (V.Y u) m ((V.Y v) n x)

@[simp] theorem Yprod_apply (V : PreVertexAlgebra 𝒱) (u v x : 𝒱) (m n : ℤ) :
    V.Yprod u v x m n = (V.Y u) m ((V.Y v) n x) := rfl

/-- **The iterated product field lies in `𝒱((z₁))((z₂))`.**  By VA5 (regularity) the inner
coefficients `(Y v)ₙ x` vanish for `n ≪ 0`, so the whole `z₁`-column vanishes there and the
`z₂`-support is bounded below uniformly in `m` (Gannon §5.1.2). -/
theorem Yprod_bddBelow (V : PreVertexAlgebra 𝒱) (u v x : 𝒱) : IsBddBelow₂ (V.Yprod u v x) := by
  obtain ⟨N, hN⟩ := V.regularity v x
  refine ⟨-N, fun m n hn => ?_⟩
  change (V.Y u) m ((V.Y v) n x) = 0
  have hv : (V.Y v) n x = 0 := by
    have h := hN (-n - 1) (by omega)
    rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h
  rw [hv, map_zero]

/-- **Cancellation principle for product fields.**  If the iterated product fields of two
states `w₁, w₂` (with second/inner state `v`/`v'` and applied to `x`/`x'`) agree after
multiplication by `(z₁-z₂)ᴺ`, then they agree on the nose.  Direct from the
`(z₁-z₂)ᴺ`-cancellation on `𝒱((z₁))((z₂))` (`eq_zero_of_mulBySubPow_of_bddBelow`). -/
theorem Yprod_ext (V : PreVertexAlgebra 𝒱) {u v x u' v' x' : 𝒱} (N : ℕ)
    (h : mulBySubPow N (V.Yprod u v x) = mulBySubPow N (V.Yprod u' v' x')) :
    V.Yprod u v x = V.Yprod u' v' x' := by
  have hsub : mulBySubPow N (V.Yprod u v x - V.Yprod u' v' x') = 0 := by
    rw [map_sub, h, sub_self]
  have hbb : IsBddBelow₂ (V.Yprod u v x - V.Yprod u' v' x') := by
    obtain ⟨B₁, hB₁⟩ := V.Yprod_bddBelow u v x
    obtain ⟨B₂, hB₂⟩ := V.Yprod_bddBelow u' v' x'
    refine ⟨min B₁ B₂, fun m n hn => ?_⟩
    change V.Yprod u v x m n - V.Yprod u' v' x' m n = 0
    rw [hB₁ m n (lt_of_lt_of_le hn (min_le_left _ _)),
        hB₂ m n (lt_of_lt_of_le hn (min_le_right _ _)), sub_zero]
  have := eq_zero_of_mulBySubPow_of_bddBelow N _ hsub hbb
  rwa [sub_eq_zero] at this

end PreVertexAlgebra

end VOA
