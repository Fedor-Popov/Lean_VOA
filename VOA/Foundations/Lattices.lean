/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Complex.Basic

/-!
# Integral lattices and their group algebras  (Gannon §1.2.1, pp. 29–32)

The combinatorial data behind lattice VOAs (`Examples.Lattice`).

* An **integral lattice** `L` is a finite-rank free `ℤ`-module with a symmetric `ℤ`-valued
  bilinear form `⟨·,·⟩` (`IntegralLattice`, bundled as a structure carrying the module and
  the form — the lightest faithful encoding, since the form is *data* attached to `L`, and
  named lattices like `ℤⁿ` are then just terms, not global instances polluting `ℤ`).
* `L` is **even** if `2 ∣ ⟨v,v⟩` for all `v`; **positive-definite** if `⟨v,v⟩ > 0` for
  `v ≠ 0`. (The genuine positive-definiteness is over `ℝ`; on the integral points the two
  agree for nondegenerate forms, and we take the simpler `ℤ`-condition here.)
* The **dual lattice** `L* = {x ∈ L ⊗ ℝ : ⟨x,v⟩ ∈ ℤ ∀ v ∈ L}` (`dual`), with `L ⊆ L*`
  (`le_dual`). `L` is **self-dual** (unimodular) iff `L = L*` (`SelfDual`); these give
  *holomorphic* lattice VOAs. (`|L*/L| = |det L|` is the discriminant — left as a stretch.)
* The **group algebra** `ℂ{L} := AddMonoidAlgebra ℂ L` with `eᵘ·eᵛ = e^{u+v}`
  (`latticeAlgebra`). For *odd* `L` one must twist by a 2-cocycle
  `eᵅeᵝ = (-1)^{⟨α,β⟩} eᵝeᵅ`; that twisted product is in `Foundations.LatticeAlgebraTwisted`.

## Dependencies
Mathlib bilinear forms (`Matrix.toBilin'`, `BilinForm.baseChange`), free modules, and
`AddMonoidAlgebra`. Only the even/dual/self-dual predicates are bespoke.

## Status
Complete & `sorry`-free for the predicates (`Even`, `PosDef`, `dual`,
`SelfDual`), `le_dual` (`L ⊆ L*`), and `latticeAlgebra`. Smoke tests: `ℤⁿ` is an
integral, positive-definite lattice and `√2·ℤ` is even (all proved). The concrete
**self-duality of `ℤⁿ`** (`stdLattice_selfDual`) is **proved** `sorry`-free via the
`ℝ ⊗ ℤⁿ ≅ ℝⁿ` coordinate computation (`stdLatticeBasis`, `stdLattice_formℝ_basis`
orthonormality, `stdLattice_formℝ_repr`/`stdLattice_toReal_repr`). Not done in this file: the
discriminant identity `|L*/L| = |det L|`; `E₈`/Leech as named instances; and the
cocycle-twisted odd product (`Foundations.LatticeAlgebraTwisted`).

## References
* Gannon §1.2.1, §5.2.2; Conway–Sloane, *Sphere Packings, Lattices and Groups*;
  FLM Ch. 6–8 (lattice VOAs).
-/

namespace VOA

open scoped TensorProduct
open Module

universe u

/-- An **integral lattice** (Gannon §1.2.1): a finite-rank free `ℤ`-module `carrier`
together with a symmetric `ℤ`-valued bilinear form `form`. The form is data, so we bundle
it with the module rather than treating it as a typeclass. -/
structure IntegralLattice where
  /-- The underlying `ℤ`-module. -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [free : Module.Free ℤ carrier]
  [finite : Module.Finite ℤ carrier]
  /-- The bilinear (Gram) form `⟨·,·⟩`. -/
  form : LinearMap.BilinForm ℤ carrier
  /-- The form is symmetric. -/
  isSymm : form.IsSymm

attribute [instance] IntegralLattice.addCommGroup IntegralLattice.free IntegralLattice.finite

namespace IntegralLattice

variable (L : IntegralLattice)

/-- An integral lattice is **even** when `⟨v,v⟩` is always even (Gannon §1.2.1). -/
def Even : Prop := ∀ v : L.carrier, 2 ∣ L.form v v

/-- An integral lattice is **positive-definite** when `⟨v,v⟩ > 0` for `v ≠ 0`
(Gannon §1.2.1; genuine positivity is over `ℝ`, see the module docstring). -/
def PosDef : Prop := ∀ v : L.carrier, v ≠ 0 → 0 < L.form v v

/-! ### The dual lattice -/

/-- The real form `⟨·,·⟩_ℝ` on `L ⊗ ℝ = ℝ ⊗[ℤ] L`, obtained by base change. -/
noncomputable def formℝ : LinearMap.BilinForm ℝ (ℝ ⊗[ℤ] L.carrier) := L.form.baseChange ℝ

/-- The canonical embedding `L ↪ L ⊗ ℝ`, `v ↦ 1 ⊗ v`. -/
noncomputable def toReal : L.carrier →ₗ[ℤ] ℝ ⊗[ℤ] L.carrier :=
  (TensorProduct.mk ℤ ℝ L.carrier) 1

/-- The **dual lattice** `L* = {x ∈ L ⊗ ℝ : ⟨x, v⟩ ∈ ℤ for all v ∈ L}` (Gannon §1.2.1),
as an additive subgroup of `L ⊗ ℝ`. -/
noncomputable def dual : AddSubgroup (ℝ ⊗[ℤ] L.carrier) where
  carrier := {x | ∀ v : L.carrier, ∃ k : ℤ, L.formℝ x (L.toReal v) = (k : ℝ)}
  add_mem' {x y} hx hy v := by
    obtain ⟨kx, hkx⟩ := hx v
    obtain ⟨ky, hky⟩ := hy v
    exact ⟨kx + ky, by rw [map_add, LinearMap.add_apply, hkx, hky]; push_cast; ring⟩
  zero_mem' v := ⟨0, by simp⟩
  neg_mem' {x} hx v := by
    obtain ⟨k, hk⟩ := hx v
    exact ⟨-k, by rw [map_neg, LinearMap.neg_apply, hk]; push_cast; ring⟩

/-- The real form on simple tensors is the `ℝ`-cast of the integral form:
`⟨1 ⊗ v, 1 ⊗ w⟩_ℝ = ⟨v,w⟩` (Gannon §1.2.1). -/
theorem formℝ_tmul (v w : L.carrier) :
    L.formℝ ((1 : ℝ) ⊗ₜ[ℤ] v) ((1 : ℝ) ⊗ₜ[ℤ] w) = (L.form v w : ℝ) := by
  rw [formℝ, LinearMap.BilinForm.baseChange_tmul, mul_one, zsmul_eq_mul, mul_one]

/-- For an integral lattice, `L ⊆ L*` (`⟨v,w⟩ ∈ ℤ` for `v,w ∈ L`; Gannon §1.2.1). -/
theorem le_dual (v : L.carrier) : L.toReal v ∈ L.dual := by
  intro w
  exact ⟨L.form v w, L.formℝ_tmul v w⟩

/-- An integral lattice is **self-dual** (unimodular) when it equals its dual: the image of
`L` in `L ⊗ ℝ` is exactly `L*` (Gannon §1.2.1). -/
def SelfDual : Prop := ∀ x : ℝ ⊗[ℤ] L.carrier, x ∈ L.dual ↔ ∃ v : L.carrier, L.toReal v = x

end IntegralLattice

/-! ## The group algebra `ℂ{L}` -/

/-- The **group algebra** `ℂ{L} = AddMonoidAlgebra ℂ L`: a `ℂ`-basis `{eᵛ : v ∈ L}` with
`eᵘ·eᵛ = e^{u+v}` (Gannon §5.2.2). For *odd* lattices this product must be twisted by a
2-cocycle (`eᵅeᵝ = (-1)^{⟨α,β⟩} eᵝeᵅ`); see `Foundations.LatticeAlgebraTwisted`. -/
noncomputable abbrev latticeAlgebra (L : IntegralLattice) : Type _ :=
  AddMonoidAlgebra ℂ L.carrier

/-- The basis vector `eᵛ ∈ ℂ{L}`. -/
noncomputable def latticeAlgebra.e {L : IntegralLattice} (v : L.carrier) : latticeAlgebra L :=
  AddMonoidAlgebra.single v 1

/-- The defining product `eᵘ · eᵛ = e^{u+v}` (Gannon §5.2.2). -/
theorem latticeAlgebra.e_mul_e {L : IntegralLattice} (u v : L.carrier) :
    (latticeAlgebra.e u : latticeAlgebra L) * latticeAlgebra.e v = latticeAlgebra.e (u + v) := by
  simp only [latticeAlgebra.e, AddMonoidAlgebra.single_mul_single, mul_one]

/-! ## Examples and smoke tests -/

/-- The **standard lattice** `ℤⁿ` with the dot-product form `⟨v,w⟩ = ∑ᵢ vᵢwᵢ`. -/
noncomputable def stdLattice (n : ℕ) : IntegralLattice where
  carrier := Fin n → ℤ
  form := Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) ℤ)
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.one_mulVec, Matrix.one_mulVec]
    exact dotProduct_comm v w

/-- The rank-one even lattice `√2·ℤ` with form `⟨v,w⟩ = 2vw`. -/
noncomputable def sqrt2Lattice : IntegralLattice where
  carrier := ℤ
  form := (2 : ℤ) • LinearMap.mul ℤ ℤ
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro v w
    simp only [LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    ring

/-- `√2·ℤ` is even: `⟨v,v⟩ = 2·v²`. -/
example : sqrt2Lattice.Even := by
  intro v
  refine ⟨LinearMap.mul ℤ ℤ v v, ?_⟩
  change (2 : ℤ) • LinearMap.mul ℤ ℤ v v = 2 * LinearMap.mul ℤ ℤ v v
  rw [smul_eq_mul]

/-- `ℤⁿ` is positive-definite: `⟨v,v⟩ = ∑ vᵢ² > 0` for `v ≠ 0`. -/
example (n : ℕ) : (stdLattice n).PosDef := by
  intro v hv
  change 0 < Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) ℤ) v v
  rw [Matrix.toBilin'_apply', Matrix.one_mulVec]
  change 0 < ∑ i, v i * v i
  refine Finset.sum_pos' (fun i _ => mul_self_nonneg (v i)) ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-! ## Self-duality of the standard lattice `ℤⁿ` (Gannon §1.2.1)

`ℤⁿ` is unimodular: `(ℤⁿ)* = ℤⁿ`.  Concretely, identify `ℝ ⊗ ℤⁿ` with `ℝⁿ` via the
base-changed standard basis `B = (Pi.basisFun ℤ (Fin n)).baseChange ℝ`.  The standard form
makes `B` an orthonormal basis, so for `x ∈ ℝ ⊗ ℤⁿ` the pairing `⟨x, eⱼ⟩` reads off the
`j`-th coordinate `B.repr x j`.  Hence `x ∈ (ℤⁿ)*` iff every coordinate is an integer, which
is exactly `x ∈ ℤⁿ`. -/

/-- The `ℝ`-basis of `ℝ ⊗ ℤⁿ` lifting the standard `ℤ`-basis of `ℤⁿ`. -/
noncomputable def stdLatticeBasis (n : ℕ) :
    Basis (Fin n) ℝ (ℝ ⊗[ℤ] (stdLattice n).carrier) :=
  (Pi.basisFun ℤ (Fin n)).baseChange ℝ

/-- The `k`-th base-changed basis vector is `1 ⊗ eₖ`, with the lattice-carrier type
explicit so downstream `BilinForm.baseChange_tmul`/`formℝ_tmul` lemmas unify (Gannon §1.2.1).
The proof builds the equation purely in `ℝ ⊗ (Fin n → ℤ)` — where `baseChange_apply` fires
syntactically — then crosses the `Fin n → ℤ ≡ (stdLattice n).carrier` boundary by `exact`. -/
theorem stdLatticeBasis_apply (n : ℕ) (k : Fin n) :
    stdLatticeBasis n k = (1 : ℝ) ⊗ₜ[ℤ] (Pi.single k (1 : ℤ) : (stdLattice n).carrier) := by
  have h : (Pi.basisFun ℤ (Fin n)).baseChange ℝ k
      = (1 : ℝ) ⊗ₜ[ℤ] (Pi.single k (1 : ℤ) : Fin n → ℤ) := by
    rw [Module.Basis.baseChange_apply, Pi.basisFun_apply]
  exact h

/-- The base-changed standard basis is orthonormal for the real form:
`⟨Bᵢ, Bⱼ⟩_ℝ = δᵢⱼ` (Gannon §1.2.1). -/
theorem stdLattice_formℝ_basis (n : ℕ) (i j : Fin n) :
    (stdLattice n).formℝ (stdLatticeBasis n i) (stdLatticeBasis n j)
      = if i = j then (1 : ℝ) else 0 := by
  have hform : (stdLattice n).form (Pi.single i (1 : ℤ)) (Pi.single j 1)
      = if i = j then (1 : ℤ) else 0 := by
    change Matrix.toBilin' 1 (Pi.single i 1) (Pi.single j 1) = _
    rw [Matrix.toBilin'_single, Matrix.one_apply]
  have e : (stdLattice n).formℝ (stdLatticeBasis n i) (stdLatticeBasis n j)
      = ((stdLattice n).form (Pi.single i 1) (Pi.single j 1) : ℝ) := by
    rw [stdLatticeBasis_apply, stdLatticeBasis_apply]
    -- cross the `Fin n → ℤ ≡ carrier` boundary by defeq (`exact`), not syntactic `rw`
    exact IntegralLattice.formℝ_tmul (stdLattice n) (Pi.single i 1) (Pi.single j 1)
  rw [e, hform]
  split_ifs with h <;> simp

/-- The `j`-th coordinate of `x ∈ ℝ ⊗ ℤⁿ` is recovered by pairing with the `j`-th basis
vector: `⟨x, eⱼ⟩_ℝ = B.repr x j` (orthonormality of `B`). -/
theorem stdLattice_formℝ_repr (n : ℕ) (x : ℝ ⊗[ℤ] (stdLattice n).carrier) (j : Fin n) :
    (stdLattice n).formℝ x (stdLatticeBasis n j) = (stdLatticeBasis n).repr x j := by
  conv_lhs => rw [← (stdLatticeBasis n).sum_repr x]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [map_smul, LinearMap.smul_apply, stdLattice_formℝ_basis, if_pos rfl, smul_eq_mul, mul_one]
  · intro i _ hij
    rw [map_smul, LinearMap.smul_apply, stdLattice_formℝ_basis, if_neg hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- The `B`-coordinates of a lattice vector `v ∈ ℤⁿ` are its (real-cast) entries:
`B.repr (1 ⊗ v) j = vⱼ`. -/
theorem stdLattice_toReal_repr (n : ℕ) (v : Fin n → ℤ) (j : Fin n) :
    (stdLatticeBasis n).repr ((stdLattice n).toReal v) j = (v j : ℝ) := by
  change (Module.Basis.baseChange ℝ (Pi.basisFun ℤ (Fin n))).repr ((1 : ℝ) ⊗ₜ[ℤ] v) j = _
  rw [Module.Basis.baseChange_repr_tmul, Pi.basisFun_repr, zsmul_eq_mul, mul_one]

/-- **`ℤⁿ` is self-dual (unimodular)** (Gannon §1.2.1): the standard lattice equals its own
dual.  An element `x ∈ ℝ ⊗ ℤⁿ` lies in `(ℤⁿ)*` iff `⟨x, eⱼ⟩ ∈ ℤ` for every `j`, i.e. every
coordinate `B.repr x j` is an integer, which is exactly `x = 1 ⊗ v` for some `v ∈ ℤⁿ`. -/
theorem stdLattice_selfDual (n : ℕ) : (stdLattice n).SelfDual := by
  intro x
  constructor
  · intro hx
    have hbasis : ∀ j : Fin n, (stdLattice n).toReal (Pi.single j (1 : ℤ)) = stdLatticeBasis n j :=
      fun j => by rw [stdLatticeBasis_apply]; rfl
    choose k hk using fun j => hx (Pi.single j (1 : ℤ))
    refine ⟨k, ?_⟩
    refine (stdLatticeBasis n).repr.injective ?_
    ext j
    rw [stdLattice_toReal_repr]
    have hxj : (stdLatticeBasis n).repr x j = (k j : ℝ) := by
      rw [← stdLattice_formℝ_repr, ← hbasis j, hk j]
    rw [hxj]
  · rintro ⟨v, rfl⟩
    exact (stdLattice n).le_dual v

end VOA
