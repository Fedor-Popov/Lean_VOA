/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Exact layers of a submodule inclusion

This file packages a small reusable linear-algebra primitive:
if `Q ≤ P`, the exact layer is the quotient `P / Q`, realized internally as
`P ⧸ Q.comap P.subtype`.  The file is intentionally VOA-free.
-/

namespace VOA

open Module (finrank)

universe u

section ExactLayer

variable {K : Type u} [DivisionRing K]
variable {V W : Type*}
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

namespace Submodule

/-- The exact layer `P / Q` for an inclusion `Q ≤ P`, realized as a quotient of `P`. -/
abbrev Layer (P Q : Submodule K V) (_h : Q ≤ P) : Type _ :=
  P ⧸ Q.comap P.subtype

namespace Layer

/-- Restrict a linear map to a submodule it preserves. -/
def mapWithin (P : Submodule K V) (P' : Submodule K W)
    (f : V →ₗ[K] W) (hP : ∀ x, x ∈ P → f x ∈ P') : P →ₗ[K] P' where
  toFun x := ⟨f x, hP x x.property⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- A map preserving `P` and `Q` induces a map on exact layers. -/
def map (P Q : Submodule K V) (P' Q' : Submodule K W)
    (h : Q ≤ P) (h' : Q' ≤ P')
    (f : V →ₗ[K] W) (hP : ∀ x, x ∈ P → f x ∈ P') (hQ : ∀ x, x ∈ Q → f x ∈ Q') :
    Layer P Q h →ₗ[K] Layer P' Q' h' :=
  (Q.comap P.subtype).mapQ (Q'.comap P'.subtype) (mapWithin P P' f hP) (by
    intro x hx
    change f x ∈ Q'
    exact hQ x (by simpa using hx))

@[simp] theorem map_mkQ
    (P Q : Submodule K V) (P' Q' : Submodule K W)
    (h : Q ≤ P) (h' : Q' ≤ P')
    (f : V →ₗ[K] W) (hP : ∀ x, x ∈ P → f x ∈ P') (hQ : ∀ x, x ∈ Q → f x ∈ Q')
    (x : P) :
    map P Q P' Q' h h' f hP hQ ((Q.comap P.subtype).mkQ x) =
      (Q'.comap P'.subtype).mkQ (mapWithin P P' f hP x) := by
  apply Submodule.mapQ_apply

/-- The layer exact-sequence rank identity, expressed against the pullback
`Q.comap P.subtype` inside `P`. -/
theorem finrank_layer_add_finrank_comap
    (P Q : Submodule K V) (h : Q ≤ P) [FiniteDimensional K P] :
    finrank K (Layer P Q h) + finrank K (Q.comap P.subtype) = finrank K P := by
  simpa [Layer] using
    (Submodule.finrank_quotient_add_finrank (R := K)
      (M := P) (N := Q.comap P.subtype))

/-- The layer exact-sequence rank identity, rewritten using `Q ≤ P`. -/
theorem finrank_layer_add_finrank
    (P Q : Submodule K V) (h : Q ≤ P) [FiniteDimensional K P] :
  finrank K (Layer P Q h) + finrank K Q = finrank K P := by
  have hQfin : finrank K Q = finrank K (Q.comap P.subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)).symm
  rw [hQfin]
  exact finrank_layer_add_finrank_comap P Q h

end Layer

end Submodule

end ExactLayer

end VOA
