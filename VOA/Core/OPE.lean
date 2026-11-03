/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Core.VertexAlgebra
import Mathlib.Algebra.Lie.OfAssociative

/-!
# The operator product expansion — structural OPE lemmas  (Gannon §5.1.2–5.1.3)

The *structural* half of the Jacobi/Borcherds package — the part that follows from VA4
(locality) + Proposition 5.1.2 alone, with **no** duality input.  It is factored into this
small upstream module so that `Core.Reconstruction` can consume it (in `mode_commutator`) while
the **full** Jacobi/Borcherds identities, which additionally need the duality `nth_product`
/`assoc_neg`, are assembled downstream in `Core.BorcherdsIdentity` (which re-exports everything
here).

* `bracket_deltaSum` — the OPE δ-decomposition `[Y(u,z₁),Y(v,z₂)] = ∑_{j<N} cⱼ ∂_{z₂}ʲ δ(z₁/z₂)`.
* `mode_bracket_ope` / `mode_commutator_structural` — the commutator of modes as a finite
  falling-factorial sum of modes of the OPE coefficients `cⱼ`.

## Dependencies
* `VOA.Core.VertexAlgebra`; `Mathlib.Algebra.Lie.OfAssociative`.

## Status
Complete & `sorry`-free / axiom-free.  `bracket_deltaSum`,
`mode_bracket_ope`, `mode_commutator_structural` are proved from VA4 + Prop 5.1.2
(`#print axioms = [propext, Classical.choice, Quot.sound]`).

## References
* Gannon §5.1.3, eqs. (5.1.7); Frenkel–Lepowsky–Meurman; Lepowsky–Li Ch. 3; Kac.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Pointwise evaluation of a finite sum of two-variable distributions -/

/-- Evaluating a `Finset`-sum of two-variable distributions coefficient-wise. -/
theorem formalDist₂_sum_apply {ι : Type*} {𝒲 : Type*} [AddCommGroup 𝒲] (s : Finset ι)
    (F : ι → FormalDist₂ 𝒲) (m n : ℤ) : (∑ i ∈ s, F i) m n = ∑ i ∈ s, F i m n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]; rfl
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change F a m n + (∑ i ∈ t, F i) m n = F a m n + ∑ i ∈ t, F i m n
    rw [ih]

/-! ## The operator product expansion (VA4 + Proposition 5.1.2) -/

/-- **The operator product expansion.**  In a vertex algebra, the locality axiom VA4
together with Proposition 5.1.2 (`local_iff_deltaSum`) gives, for every pair of states
`u, v`, a finite δ-function decomposition of the commutator of their fields:
`[Y(u,z₁), Y(v,z₂)] = ∑_{j<N} cⱼ(z₂) ∂_{z₂}ʲ δ(z₁/z₂)` for some `N` and coefficient
distributions `cⱼ` (Gannon §5.1.2–5.1.3; this is the singular part of the OPE). -/
theorem bracket_deltaSum (V : PreVertexAlgebra 𝒱) (u v : 𝒱) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ 𝒱)),
      bracketDist (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) := by
  obtain ⟨N, hN⟩ := V.locality u v
  exact ⟨N, (local_iff_deltaSum _ N).mp hN⟩

/-! ## The commutator formula in OPE form -/

/-- **The commutator formula, OPE form.**  Given the δ-decomposition
`[Y(u,z₁),Y(v,z₂)] = ∑_{j<N} cⱼ(z₂) ∂_{z₂}ʲ δ(z₁/z₂)` (from `bracket_deltaSum`),
extracting the `z₁ᵃ z₂ᵇ` coefficient yields the commutator of modes as a finite
falling-factorial sum of modes of the OPE coefficients:
`[u₍ₐ₎, v₍ᵦ₎] = ∑_{j<N} (a)(a-1)⋯(a-j+1) · (cⱼ)₍ₐ₊ᵦ₋ⱼ₎`. -/
theorem mode_bracket_ope (V : PreVertexAlgebra 𝒱) (u v : 𝒱) {N : ℕ}
    {c : Fin N → FormalDist (End ℂ 𝒱)}
    (h : bracketDist (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j)) (a b : ℤ) :
    ⁅mode (V.Y u) a, mode (V.Y v) b⁆ = ∑ j : Fin N,
      (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))) • mode (c j) (a + b - ((j : ℕ) : ℤ)) := by
  have hcomm : ⁅mode (V.Y u) a, mode (V.Y v) b⁆
      = bracketDist (V.Y u) (V.Y v) (-a - 1) (-b - 1) := by
    simp only [bracketDist_apply, LieRing.of_associative_ring_bracket, mode_apply]
  rw [hcomm, h, formalDist₂_sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [deltaDeriv_apply,
    show (∏ i ∈ Finset.range (j : ℕ), (-(-a - 1) - 1 - (i : ℤ)))
        = ∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ)) from
      Finset.prod_congr rfl (fun i _ => by ring)]
  congr 1
  rw [mode_apply]
  congr 1
  ring

/-- **The structural commutator formula** (Gannon 5.1.7c, structural form): combining the
operator product expansion `bracket_deltaSum` with the coefficient extraction
`mode_bracket_ope`.  For every `u, v` and modes `a, b`, the commutator `[u₍ₐ₎, v₍ᵦ₎]` is
a finite falling-factorial sum of modes of the OPE coefficients of `[Y(u,z₁),Y(v,z₂)]`. -/
theorem mode_commutator_structural (V : PreVertexAlgebra 𝒱) (u v : 𝒱) (a b : ℤ) :
    ∃ (N : ℕ) (c : Fin N → FormalDist (End ℂ 𝒱)),
      bracketDist (V.Y u) (V.Y v) = ∑ j : Fin N, deltaDeriv (j : ℕ) (c j) ∧
      ⁅mode (V.Y u) a, mode (V.Y v) b⁆ = ∑ j : Fin N,
        (∏ i ∈ Finset.range (j : ℕ), (a - (i : ℤ))) • mode (c j) (a + b - ((j : ℕ) : ℤ)) := by
  obtain ⟨N, c, hc⟩ := bracket_deltaSum V u v
  exact ⟨N, c, hc, mode_bracket_ope V u v hc a b⟩

end VOA
