/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Linearly filtered modules and strict filtered maps

This file supplies the small amount of filtration theory needed for the inverse
Drinfeld--Sokolov project.  Unlike `GradedFlag`, the index is an arbitrary preorder.  This is
essential for the free-field algebra `Pi`: its `R`-filtration is indexed by `ℤ` and is not bounded
below before one fixes a charge sector.

The central distinction is between:

* a **filtered** map, which only gives `f (F_i) ⊆ G_{phi i}`; and
* a **strictly filtered** map, for which
  `f (F_i) = range(f) ∩ G_{phi i}`.

For the Adamovic inverse-DS embedding, filteredness follows by checking the displayed free-field
formulas for the affine generators.  Strictness is the genuinely difficult
"no hidden cancellation" statement.  Keeping the notions separate prevents that theorem from
being smuggled into the definitions.
-/

namespace VOA

universe uι uκ uR uM uN

/-- An increasing family of submodules indexed by a preorder. -/
structure LinearFiltration (ι : Type uι) (R : Type uR) (M : Type uM)
    [Preorder ι] [Semiring R] [AddCommMonoid M] [Module R M] where
  /-- The filtration piece with index `i`. -/
  piece : ι → Submodule R M
  /-- Filtration pieces increase with the index. -/
  mono' : Monotone piece

namespace LinearFiltration

variable {ι : Type uι} {κ : Type uκ} {R : Type uR} {M : Type uM} {N : Type uN}
variable [Preorder ι] [Preorder κ] [Semiring R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem mono (F : LinearFiltration ι R M) {i j : ι} (h : i ≤ j) :
    F.piece i ≤ F.piece j :=
  F.mono' h

/-- Reindex a filtration along a monotone map. -/
def reindex (G : LinearFiltration κ R M) (phi : ι → κ) (hphi : Monotone phi) :
    LinearFiltration ι R M where
  piece i := G.piece (phi i)
  mono' _ _ h := G.mono' (hphi h)

/-- Pull a filtration back along a linear map. -/
def comap (G : LinearFiltration ι R N) (f : M →ₗ[R] N) : LinearFiltration ι R M where
  piece i := (G.piece i).comap f
  mono' _ _ h := Submodule.comap_mono (G.mono' h)

/-- `f` is filtered along `phi` if `f(F_i) ⊆ G_{phi i}` for every `i`.

No monotonicity assumption on `phi` is needed merely to state the pointwise condition. -/
def IsFilteredAlong (F : LinearFiltration ι R M) (G : LinearFiltration κ R N)
    (phi : ι → κ) (f : M →ₗ[R] N) : Prop :=
  ∀ i, F.piece i ≤ (G.piece (phi i)).comap f

/-- A filtered map is **strict** when the filtration induced on its range is exactly the source
filtration: `f(F_i) = range(f) ∩ G_{phi i}`. -/
def IsStrictFilteredAlong (F : LinearFiltration ι R M) (G : LinearFiltration κ R N)
    (phi : ι → κ) (f : M →ₗ[R] N) : Prop :=
  ∀ i, (F.piece i).map f = LinearMap.range f ⊓ G.piece (phi i)

/-- The equal-index version of `IsFilteredAlong`. -/
abbrev IsFiltered (F : LinearFiltration ι R M) (G : LinearFiltration ι R N)
    (f : M →ₗ[R] N) : Prop :=
  F.IsFilteredAlong G id f

/-- The equal-index version of `IsStrictFilteredAlong`. -/
abbrev IsStrictFiltered (F : LinearFiltration ι R M) (G : LinearFiltration ι R N)
    (f : M →ₗ[R] N) : Prop :=
  F.IsStrictFilteredAlong G id f

/-- Strict filteredness implies filteredness. -/
theorem IsStrictFilteredAlong.isFilteredAlong
    {F : LinearFiltration ι R M} {G : LinearFiltration κ R N}
    {phi : ι → κ} {f : M →ₗ[R] N} (h : F.IsStrictFilteredAlong G phi f) :
    F.IsFilteredAlong G phi f := by
  intro i x hx
  have hfx : f x ∈ (F.piece i).map f := ⟨x, hx, rfl⟩
  rw [h i] at hfx
  exact hfx.2

/-- A strict filtered embedding identifies each source piece with the pullback of the
corresponding target piece. -/
theorem IsStrictFilteredAlong.comap_eq
    {F : LinearFiltration ι R M} {G : LinearFiltration κ R N}
    {phi : ι → κ} {f : M →ₗ[R] N} (h : F.IsStrictFilteredAlong G phi f)
    (hf : Function.Injective f) (i : ι) :
    F.piece i = (G.piece (phi i)).comap f := by
  apply le_antisymm
  · exact h.isFilteredAlong i
  · intro x hx
    have hfx : f x ∈ LinearMap.range f ⊓ G.piece (phi i) := ⟨⟨x, rfl⟩, hx⟩
    rw [← h i] at hfx
    obtain ⟨y, hy, hyx⟩ := hfx
    have hxy : y = x := hf hyx
    simpa [hxy] using hy

/-- Conversely, exact pullback of all filtration pieces implies strictness on the range.  This
direction does not require injectivity. -/
theorem strictFilteredAlong_of_comap_eq
    {F : LinearFiltration ι R M} {G : LinearFiltration κ R N}
    {phi : ι → κ} {f : M →ₗ[R] N}
    (h : ∀ i, F.piece i = (G.piece (phi i)).comap f) :
    F.IsStrictFilteredAlong G phi f := by
  intro i
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [h i] at hx
    exact ⟨⟨x, rfl⟩, hx⟩
  · rintro x ⟨⟨y, rfl⟩, hy⟩
    exact ⟨y, (h i).symm ▸ hy, rfl⟩

/-- For an embedding, strictness is equivalent to exact pullback of every piece. -/
theorem strictFilteredAlong_iff_comap_eq
    {F : LinearFiltration ι R M} {G : LinearFiltration κ R N}
    {phi : ι → κ} {f : M →ₗ[R] N} (hf : Function.Injective f) :
    F.IsStrictFilteredAlong G phi f ↔
      ∀ i, F.piece i = (G.piece (phi i)).comap f := by
  constructor
  · intro h i
    exact h.comap_eq hf i
  · exact strictFilteredAlong_of_comap_eq

/-! ## Finite-dimensional strictness criteria -/

section FiniteDimensional

variable {K : Type*} [DivisionRing K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- A filtered inclusion is an equality at a finite-dimensional piece as soon as the source
piece and the induced target piece have the same dimension.

The finite-dimensional hypothesis is required only for the induced target piece, not for the
whole filtered module.  This is the useful form for graded objects such as VOAs, whose total
space is usually infinite-dimensional while each fixed-weight filtered piece is finite. -/
theorem IsFilteredAlong.piece_eq_comap_of_finrank_eq
    {F : LinearFiltration ι K V} {G : LinearFiltration κ K W}
    {phi : ι → κ} {f : V →ₗ[K] W}
    (hfiltered : F.IsFilteredAlong G phi f) (i : ι)
    [FiniteDimensional K ((G.piece (phi i)).comap f)]
    (hfinrank : Module.finrank K (F.piece i) =
      Module.finrank K ((G.piece (phi i)).comap f)) :
    F.piece i = (G.piece (phi i)).comap f :=
  Submodule.eq_of_le_of_finrank_eq (hfiltered i) hfinrank

/-- Pointwise finite-dimensional dimension equality upgrades a filtered map to a strict
filtered map.  No injectivity assumption is needed here: equality with the pullback pieces is
already strong enough to imply strictness on the range.

For an embedding, `strictFilteredAlong_iff_comap_eq` gives the converse as well. -/
theorem IsFilteredAlong.isStrictFilteredAlong_of_finrank_eq
    {F : LinearFiltration ι K V} {G : LinearFiltration κ K W}
    {phi : ι → κ} {f : V →ₗ[K] W}
    (hfiltered : F.IsFilteredAlong G phi f)
    (hfinite : ∀ i, FiniteDimensional K ((G.piece (phi i)).comap f))
    (hfinrank : ∀ i, Module.finrank K (F.piece i) =
      Module.finrank K ((G.piece (phi i)).comap f)) :
    F.IsStrictFilteredAlong G phi f := by
  apply strictFilteredAlong_of_comap_eq
  intro i
  letI : FiniteDimensional K ((G.piece (phi i)).comap f) := hfinite i
  exact hfiltered.piece_eq_comap_of_finrank_eq i (hfinrank i)

/-- Target-side version for embeddings.  A filtered embedding is strict if, at every index, its
source piece has the same dimension as the intersection of the image with the target piece.

This is often the character-theoretic form of the criterion: the source filtered character is
compared directly with the filtered character seen inside the ambient realization.  As above,
only the individual target intersections must be finite-dimensional. -/
theorem IsFilteredAlong.isStrictFilteredAlong_of_finrank_eq_range_inf
    {F : LinearFiltration ι K V} {G : LinearFiltration κ K W}
    {phi : ι → κ} {f : V →ₗ[K] W}
    (hfiltered : F.IsFilteredAlong G phi f) (hf : Function.Injective f)
    (hfinite : ∀ i, FiniteDimensional K ↥(LinearMap.range f ⊓ G.piece (phi i)))
    (hfinrank : ∀ i, Module.finrank K (F.piece i) =
      Module.finrank K ↥(LinearMap.range f ⊓ G.piece (phi i))) :
    F.IsStrictFilteredAlong G phi f := by
  intro i
  letI : FiniteDimensional K ↥(LinearMap.range f ⊓ G.piece (phi i)) := hfinite i
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hfiltered i hx⟩
  · exact (Submodule.equivMapOfInjective f hf (F.piece i)).finrank_eq.symm.trans (hfinrank i)

end FiniteDimensional

end LinearFiltration

end VOA
