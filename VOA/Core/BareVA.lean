/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.VertexAlgebra
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.Dong

/-!
# `BarePreVA` — a vertex algebra without the grading

`PreVertexAlgebra` (Gannon Def. 5.1.3(a)) bundles an internal `ℤ`-grading with finite-dimensional
homogeneous pieces alongside the axioms VA2–VA5.  `BarePreVA` is `PreVertexAlgebra` with the grading
fields removed and nothing else changed; every `PreVertexAlgebra` gives one by forgetting
(`PreVertexAlgebra.toBarePreVA`).

**Warning.** VA2–VA5 alone do **not** imply the Borcherds/Jacobi identity: neither
`PreVertexAlgebra` nor `BarePreVA` has a translation-covariance axiom `Y(Tu,z) = ∂_z Y(u,z)`, and there
is a 3-dimensional `PreVertexAlgebra` on which both Borcherds and translation covariance fail
(`Notes/Textbook/certificates/L03_VertexAlgebraNoCovariance.lean`).  The library's Borcherds
chain (`Borcherds`, `BorcherdsIdentity`) is stated for
`VertexOperatorAlgebra`, whose VOA3 axiom supplies covariance.  Restating that chain over `BarePreVA`
as it stands is therefore a dead end; it would first need a covariance (or Jacobi) axiom.

## Status

The structure, the forgetful maps, and `isField_Y`.  Nothing Borcherds-related is proved over it.
-/

namespace VOA

open Module (End)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **A vertex algebra without the grading**: axioms VA2–VA5 only.

Same fields as `PreVertexAlgebra` minus `grading`, `isInternal`, `finrank`, `vacuum_mem`, and
`grading_mode`.  It has no translation-covariance axiom, so it does not by itself support the
Borcherds/Jacobi identity (see the module docstring). -/
structure BarePreVA (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] where
  /-- The state–field correspondence `Y(u,z) = ∑ₙ u₍ₙ₎ z^{-n-1}`, linear in `u`. -/
  Y : 𝒱 →ₗ[ℂ] (End ℂ 𝒱)⟦z^±⟧
  /-- The vacuum vector `𝟙`. -/
  vacuum : 𝒱
  /-- **VA2.** `Y(𝟙, z) = id`. -/
  vacuum_Y : Y vacuum = (1 : (End ℂ 𝒱)⟦z^±⟧)
  /-- **VA3 (creation).** `Y(u,z)𝟙` is regular at `z = 0` with value `u`. -/
  creation : ∀ u : 𝒱, mode (Y u) (-1) vacuum = u ∧ ∀ n : ℤ, 0 ≤ n → mode (Y u) n vacuum = 0
  /-- **VA4 (locality).** Any two vertex operators are mutually local. -/
  locality : ∀ u v : 𝒱, Local (Y u) (Y v)
  /-- **VA5 (regularity).** `u₍ₙ₎v = 0` for `n` large. -/
  regularity : ∀ u v : 𝒱, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (Y u) n v = 0

namespace BarePreVA

/-- The `n`-th product `u₍ₙ₎v`, matching `PreVertexAlgebra.smul`. -/
def smul (V : BarePreVA 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) : 𝒱 := mode (V.Y u) n v

@[simp] theorem smul_def (V : BarePreVA 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.smul u n v = mode (V.Y u) n v := rfl

/-- **The vertex operators are fields** — VA5 restated as lower truncation.  Same proof as
`PreVertexAlgebra.isField_Y`, which is where the grading's absence is first visible: it never
appeared in that argument either. -/
theorem isField_Y (V : BarePreVA 𝒱) (u : 𝒱) : IsField (V.Y u) := by
  intro x
  obtain ⟨N, hN⟩ := V.regularity u x
  refine ⟨-N, fun n hn => ?_⟩
  have h := hN (-n - 1) (by omega)
  rwa [mode_apply, show (-(-n - 1) - 1 : ℤ) = n by ring] at h

end BarePreVA

/-- **Forgetting the grading.**  Every vertex algebra is a `BarePreVA`. -/
def PreVertexAlgebra.toBarePreVA (V : PreVertexAlgebra 𝒱) : BarePreVA 𝒱 where
  Y := V.Y
  vacuum := V.vacuum
  vacuum_Y := V.vacuum_Y
  creation := V.creation
  locality := V.locality
  regularity := V.regularity

@[simp] theorem PreVertexAlgebra.toBarePreVA_Y (V : PreVertexAlgebra 𝒱) : V.toBarePreVA.Y = V.Y := rfl

@[simp] theorem PreVertexAlgebra.toBarePreVA_vacuum (V : PreVertexAlgebra 𝒱) :
    V.toBarePreVA.vacuum = V.vacuum := rfl

@[simp] theorem PreVertexAlgebra.toBarePreVA_smul (V : PreVertexAlgebra 𝒱) (u : 𝒱) (n : ℤ) (v : 𝒱) :
    V.toBarePreVA.smul u n v = V.smul u n v := rfl

/-- Every vertex operator algebra is a `BarePreVA`, through its underlying vertex algebra. -/
def VertexOperatorAlgebra.toBarePreVA (W : VertexOperatorAlgebra 𝒱) : BarePreVA 𝒱 :=
  W.toPreVertexAlgebra.toBarePreVA

@[simp] theorem VertexOperatorAlgebra.toBarePreVA_Y (W : VertexOperatorAlgebra 𝒱) :
    W.toBarePreVA.Y = W.Y := rfl

@[simp] theorem VertexOperatorAlgebra.toBarePreVA_smul (W : VertexOperatorAlgebra 𝒱)
    (u : 𝒱) (n : ℤ) (v : 𝒱) : W.toBarePreVA.smul u n v = W.smul u n v := rfl

end VOA
