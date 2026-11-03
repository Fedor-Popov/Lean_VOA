/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeInvolution
import VOA.Examples.TripletLattice
import VOA.Modules.StronglyRational
import VOA.Modules.Rationality
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The classification of `c = 1` VOAs (Gannon–Rayhaun): the statement

This file states **Theorem 3.1** of T. Gannon and B. C. Rayhaun, *Classification of rational
`c = 1` vertex operator algebras and vertex operator superalgebras*, arXiv:2609.00122. It proves
nothing about the classification. It fixes the vocabulary that later files reuse.

**Theorem 3.1.** If `V` is a nice VOA with `c = 1`, then `V` is isomorphic to exactly one of
* `V_{2m}` (`m ≥ 1`), the lattice VOA of `√(2m) ℤ`;
* `V_{2m}⁺` (`m ≥ 2`), the fixed points of the lift `θ` of `−1`;
* `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}`, the fixed points of finite subgroups of `Aut V₂ ≅ PSL₂(ℂ)`
  (the groups themselves, not their binary covers).

## Definitions

* `VOAIsomorphic V T`: a linear equivalence that preserves the vacuum, every product and the
  conformal vector.
* `PseudoUnitary V` (GR Def. 2.4): every irreducible module not isomorphic to `V` has all its
  conformal weights with positive real part.
* `Nice V` (GR Def. 2.6): `StronglyRational V ∧ PseudoUnitary V`.
* `V2m m`, `V2mPlus m`: the rank-one lattice VOA and its `θ`-orbifold.
* `InCOneList V`: membership in the list of Theorem 3.1.
* `GannonRayhaunStatement`: the forward direction of Theorem 3.1, as a `Prop`.

## Fidelity notes

* **Strongly rational.** `StronglyRational` (`Modules/StronglyRational.lean`) is simple,
  self-dual (a nondegenerate invariant form), `C₂`-cofinite and admissibly rational. CFT type is
  built into `VertexOperatorAlgebra`. This matches GR Def. 2.1.
* **The exceptional orbifolds.** They are stated existentially: *some* subgroup `G ≤ Aut V₂`
  isomorphic to `A₄` (resp. `S₄`, `A₅`). All such subgroups of `PSL₂(ℂ)` are conjugate, so the
  orbifold does not depend on the choice. This file does not prove that such subgroups exist.
* **Universes.** Modules in `PseudoUnitary` live in the universe of the VOA, as `ModuleEquiv`
  requires.
* **Pseudo-unitarity uses `Re`.** For a rational VOA every conformal weight is rational (DLM),
  so `0 < Re h` is GR's `h > 0`.
-/

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet

universe u v

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {𝒲 : Type v} [AddCommGroup 𝒲] [Module ℂ 𝒲]

/-- **Isomorphism of VOAs.** A linear equivalence that is a VOA homomorphism (vacuum and every
product) and sends the conformal vector to the conformal vector. -/
def VOAIsomorphic (V : VertexOperatorAlgebra 𝒱) (T : VertexOperatorAlgebra 𝒲) : Prop :=
  ∃ e : 𝒱 ≃ₗ[ℂ] 𝒲, IsVOAHom V T e.toLinearMap ∧ e V.conformalVector = T.conformalVector

/-- **Pseudo-unitarity** (Gannon–Rayhaun Def. 2.4): every irreducible module that is not
isomorphic to `V` has strictly positive conformal weights. -/
def PseudoUnitary (V : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module ℂ M] (N : OrdVModule V M),
    N.IsIrreducible → IsEmpty (ModuleEquiv V N (adjointModule V)) →
      ∀ α : ℂ, N.weight α ≠ ⊥ → 0 < α.re

/-- **Nice** (Gannon–Rayhaun Def. 2.6): strongly rational and pseudo-unitary. -/
def Nice (V : VertexOperatorAlgebra 𝒱) : Prop :=
  StronglyRational V ∧ PseudoUnitary V

/-- **`V_{2m}`**: the lattice VOA of the rank-one lattice `√(2m) ℤ` (`latP m`), central charge 1. -/
noncomputable def V2m (m : ℕ) (hm : 1 ≤ m) : VertexOperatorAlgebra (LatModuleGen (latP m)) :=
  latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)

/-- The lift `θ` of `−1` to `V_{2m}`. -/
noncomputable def thetaV2m (m : ℕ) (hm : 1 ≤ m) : Aut (V2m m hm) :=
  thetaAut (latP m) (latP_even m) (latP_posDef m hm)

/-- **`V_{2m}⁺`**: the fixed points of `θ`. -/
noncomputable def V2mPlus (m : ℕ) (hm : 1 ≤ m) :=
  orbifoldVOA (Subgroup.zpowers (thetaV2m m hm))

/-- `V` is the fixed-point algebra of a subgroup of `Aut V₂` isomorphic to the group `H`. -/
def IsV2Orbifold (V : VertexOperatorAlgebra 𝒱) (H : Type) [Group H] : Prop :=
  ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* H) ∧ VOAIsomorphic V (orbifoldVOA G)

/-- **The list of Gannon–Rayhaun Theorem 3.1.** -/
def InCOneList (V : VertexOperatorAlgebra 𝒱) : Prop :=
  (∃ (m : ℕ) (hm : 1 ≤ m), VOAIsomorphic V (V2m m hm)) ∨
  (∃ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m ∧ VOAIsomorphic V (V2mPlus m hm)) ∨
  IsV2Orbifold V (alternatingGroup (Fin 4)) ∨
  IsV2Orbifold V (Equiv.Perm (Fin 4)) ∨
  IsV2Orbifold V (alternatingGroup (Fin 5))

/-- **Gannon–Rayhaun Theorem 3.1, forward direction**, stated as a `Prop`: every nice VOA of
central charge `1` is in the list. Not proved here. -/
def GannonRayhaunStatement : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱),
    Nice V → V.centralCharge = 1 → InCOneList V

/-! ## Labels, the converse, and "exactly one" -/

/-- **Labels of the list in Theorem 3.1.** `lat m` is `V_{2m}`, `plus m` is `V_{2m}⁺`; `tetra`,
`octa`, `icosa` are `V₂^{A₄}`, `V₂^{S₄}`, `V₂^{A₅}`. -/
inductive COneLabel
  | lat (m : ℕ)
  | plus (m : ℕ)
  | tetra
  | octa
  | icosa
  deriving DecidableEq

/-- `V` is isomorphic to the VOA with label `l`. The side conditions `m ≥ 1` (lattice) and
`m ≥ 2` (plus) are part of the predicate, so invalid labels are never realized. -/
def HasCOneLabel (V : VertexOperatorAlgebra 𝒱) : COneLabel → Prop
  | .lat m => ∃ hm : 1 ≤ m, VOAIsomorphic V (V2m m hm)
  | .plus m => ∃ hm : 1 ≤ m, 2 ≤ m ∧ VOAIsomorphic V (V2mPlus m hm)
  | .tetra => IsV2Orbifold V (alternatingGroup (Fin 4))
  | .octa => IsV2Orbifold V (Equiv.Perm (Fin 4))
  | .icosa => IsV2Orbifold V (alternatingGroup (Fin 5))

/-- Being in the list means having some label. -/
theorem inCOneList_iff_exists_label (V : VertexOperatorAlgebra 𝒱) :
    InCOneList V ↔ ∃ l, HasCOneLabel V l := by
  constructor
  · rintro (⟨m, hm, h⟩ | ⟨m, hm, h2, h⟩ | h | h | h)
    · exact ⟨.lat m, hm, h⟩
    · exact ⟨.plus m, hm, h2, h⟩
    · exact ⟨.tetra, h⟩
    · exact ⟨.octa, h⟩
    · exact ⟨.icosa, h⟩
  · rintro ⟨l, hl⟩
    cases l with
    | lat m => obtain ⟨hm, h⟩ := hl; exact Or.inl ⟨m, hm, h⟩
    | plus m => obtain ⟨hm, h2, h⟩ := hl; exact Or.inr (Or.inl ⟨m, hm, h2, h⟩)
    | tetra => exact Or.inr (Or.inr (Or.inl hl))
    | octa => exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
    | icosa => exact Or.inr (Or.inr (Or.inr (Or.inr hl)))

/-- **Gannon–Rayhaun, "pairwise non-isomorphic"** (part of Theorem 3.1), as a `Prop`: a VOA has
at most one label. Combined with `GannonRayhaunStatement`, a nice `c = 1` VOA has exactly one.
Not proved here; the paper compares vacuum characters. -/
def GannonRayhaunDistinct : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱) (l l' : COneLabel),
    HasCOneLabel V l → HasCOneLabel V l' → l = l'

/-- **Gannon–Rayhaun Proposition 3.2 (converse)**, as a `Prop`: every VOA in the list is nice
and has central charge `1`. Not proved here. For `V₂^{A₅}`, the paper's proof of `C₂`-cofiniteness
and rationality rests on S. Xu, arXiv:2608.13872. -/
def GannonRayhaunConverse : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱),
    InCOneList V → Nice V ∧ V.centralCharge = 1

end VOA.Classification.COne
