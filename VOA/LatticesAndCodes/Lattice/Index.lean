/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Lattice.Sublattice
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The determinant of a finite-index sublattice

`det N = [Γ : N]² · det Γ` for a sublattice `N ≤ Γ` of the same rank — the index–discriminant
relation.  It is what turns "`Λ` contains `A` with index 2" into a determinant computation, and
the Leech lattice (M22) and the gluing arguments of Stage 4 both need it.

The proof is the change-of-basis formula for a Gram matrix, with the change-of-basis matrix
replaced by the matrix `T` expressing a basis of `N` in a basis of `Γ`: then
`gram_N = Tᵀ · gram_Γ · T`, and `|det T| = [Γ : N]` by `Submodule.natAbs_det_basis_change`.

## Main results

* `IntegralLattice.gram_ofSubmodule_eq` — `gram_N = Tᵀ · gram_Γ · T`.
* `IntegralLattice.det_ofSubmodule` — the index–determinant relation.
-/

open scoped Matrix
open Module (Basis finrank finBasis)

namespace IntegralLattice

variable {Γ : IntegralLattice}

/-- The matrix expressing a basis of the sublattice `N` in a basis of `Γ`. -/
noncomputable def inclMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ)
    {N : Submodule ℤ Γ} (b' : Basis ι ℤ N) : Matrix ι ι ℤ :=
  b.toMatrix (fun i => ((b' i : N) : Γ))

/-- The Gram matrix of a sublattice is `Tᵀ · gram · T`. -/
theorem gram_ofSubmodule_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Γ)
    {N : Submodule ℤ Γ} (b' : Basis ι ℤ N) :
    (Γ.ofSubmodule N).gram b'
      = (inclMatrix b b')ᵀ * Γ.gram b * (inclMatrix b b') := by
  ext i j
  have hexp : ∀ m : ι, ((b' m : N) : Γ) = ∑ k, inclMatrix b b' k m • b k := fun m =>
    (b.sum_toMatrix_smul_self (fun i => ((b' i : N) : Γ)) m).symm
  have hb : (Γ.ofSubmodule N).gram b' i j = Γ.bilin ((b' i : N) : Γ) ((b' j : N) : Γ) :=
    IntegralLattice.gram_apply (Γ.ofSubmodule N) b' i j
  rw [hb, hexp i, hexp j]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, gram_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The index–determinant relation**: for a sublattice of the same rank,
`det N = [Γ : N]² · det Γ`. -/
theorem det_ofSubmodule (Γ : IntegralLattice) (N : Submodule ℤ Γ)
    (hrank : finrank ℤ N = Γ.rank) :
    (Γ.ofSubmodule N).det = (Nat.card (Γ ⧸ N) : ℤ) ^ 2 * Γ.det := by
  classical
  set b : Basis (Fin Γ.rank) ℤ Γ := Γ.chooseBasis with hb
  set b' : Basis (Fin Γ.rank) ℤ N := (finBasis ℤ N).reindex (finCongr hrank) with hb'
  have hT : (inclMatrix b b').det.natAbs = Nat.card (Γ ⧸ N) :=
    Submodule.natAbs_det_basis_change b N b'
  have hgram := congrArg Matrix.det (gram_ofSubmodule_eq b b')
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_eq_gram_det (Γ.ofSubmodule N) b', det_eq_gram_det Γ b] at hgram
  have hsq : (inclMatrix b b').det * (inclMatrix b b').det
      = ((Nat.card (Γ ⧸ N) : ℤ)) ^ 2 := by
    rw [← Int.natAbs_mul_self' (inclMatrix b b').det, hT]
    ring
  rw [hgram, show (inclMatrix b b').det * Γ.det * (inclMatrix b b').det
      = ((inclMatrix b b').det * (inclMatrix b b').det) * Γ.det from by ring, hsq]

/-! ### The same relation for an isometric embedding -/

variable {Λ : IntegralLattice}

/-- An injective form-preserving map identifies `Γ` with the sublattice `range f` of `Λ`. -/
noncomputable def isomRange (f : Γ →ₗ[ℤ] Λ) (hf : Function.Injective f)
    (hform : ∀ x y : Γ, Λ.bilin (f x) (f y) = Γ.bilin x y) :
    Γ ≃ₗᵢ Λ.ofSubmodule (LinearMap.range f) where
  toLinearEquiv := LinearEquiv.ofInjective f hf
  map_bilin' x y := hform x y

/-- **The index–determinant relation for an isometric embedding.**  If `f : Γ → Λ` is injective
and preserves the forms, and its image has full rank, then `det Γ = [Λ : im f]² · det Λ`. -/
theorem det_of_injective (f : Γ →ₗ[ℤ] Λ) (hf : Function.Injective f)
    (hform : ∀ x y : Γ, Λ.bilin (f x) (f y) = Γ.bilin x y)
    (hrank : finrank ℤ (LinearMap.range f) = Λ.rank) :
    Γ.det = (Nat.card (Λ ⧸ LinearMap.range f) : ℤ) ^ 2 * Λ.det := by
  rw [(isomRange f hf hform).det_eq]
  exact det_ofSubmodule Λ (LinearMap.range f) hrank

/-- The same, with the index supplied as a hypothesis.  Passing the index rather than rewriting
it afterwards keeps the `Submodule ℤ Λ.carrier` instances in one place: `Λ.carrier` and the
concrete carrier are definitionally but not syntactically equal, and `rw` cannot cross that. -/
theorem det_of_injective_index (f : Γ →ₗ[ℤ] Λ) (hf : Function.Injective f)
    (hform : ∀ x y : Γ, Λ.bilin (f x) (f y) = Γ.bilin x y)
    (hrank : finrank ℤ (LinearMap.range f) = Λ.rank)
    {k : ℕ} (hk : Nat.card (Λ ⧸ LinearMap.range f) = k) :
    Γ.det = (k : ℤ) ^ 2 * Λ.det := by
  rw [det_of_injective f hf hform hrank, hk]

end IntegralLattice
