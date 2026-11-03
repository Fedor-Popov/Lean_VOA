/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Core.TranslationCovariant

/-!
# Vertex algebras: pre-vertex algebras with translation covariance

`PreVertexAlgebra` (Gannon Def. 5.1.3(a), axioms VA1–VA5) has no translation-covariance axiom, and
`TranslationCovariantCounterexample` shows that VA1–VA5 imply neither covariance nor the Borcherds
identity.  The genuine notion adds the axiom:

* `VertexAlgebra 𝒱`: a `PreVertexAlgebra 𝒱` with `translation_covariant :
  toPreVertexAlgebra.IsTranslationCovariant`, i.e. `Y(T u, z) = ∂_z Y(u, z)` with `T u = u₍₋₂₎𝟙`.
* `VertexOperatorAlgebra.toVertexAlgebra`: every VOA is a vertex algebra (VOA3, through
  `VertexOperatorAlgebra.isTranslationCovariant`).

The underlying pre-vertex algebra of a VOA is reached by dot notation (`W.toPreVertexAlgebra`),
so this file does not depend on how `VertexOperatorAlgebra` reaches `PreVertexAlgebra`.

Upgrading individual constructions from `PreVertexAlgebra` to `VertexAlgebra` (proving covariance)
is later work.
-/

namespace VOA

universe u

/-- A **vertex algebra**: a `PreVertexAlgebra` (Gannon Def. 5.1.3(a), VA1–VA5) that is
**translation covariant**, `Y(T u, z) = ∂_z Y(u, z)` with `T u = u₍₋₂₎𝟙`.  The covariance axiom is
genuinely extra: `TranslationCovariantCounterexample.not_isTranslationCovariant`. -/
structure VertexAlgebra (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱]
    extends PreVertexAlgebra 𝒱 where
  /-- **Translation covariance** `Y(T u, z) = ∂_z Y(u, z)`. -/
  translation_covariant : toPreVertexAlgebra.IsTranslationCovariant

/-- **Every vertex operator algebra is a vertex algebra**: its underlying pre-vertex algebra is
translation covariant by VOA3 (`VertexOperatorAlgebra.isTranslationCovariant`). -/
def VertexOperatorAlgebra.toVertexAlgebra {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : VertexAlgebra 𝒱 where
  toPreVertexAlgebra := W.toPreVertexAlgebra
  translation_covariant := W.isTranslationCovariant

@[simp] theorem VertexOperatorAlgebra.toVertexAlgebra_toPreVertexAlgebra {𝒱 : Type u}
    [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱) :
    W.toVertexAlgebra.toPreVertexAlgebra = W.toPreVertexAlgebra := rfl

end VOA

section AxiomAudit
#print axioms VOA.VertexAlgebra
#print axioms VOA.VertexOperatorAlgebra.toVertexAlgebra
end AxiomAudit
