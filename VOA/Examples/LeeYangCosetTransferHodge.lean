/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Core.GradedUnitarity
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Finite-dimensional Hodge linear algebra for the Lee–Yang transfer

This file proves the linear-algebra part of the harmonic-to-cohomology argument (good action and harmonic bound) of the coset
BRST–Koszul transfer.
For an endomorphism `Q` and its adjoint `Qadj` for a positive form, harmonic vectors map injectively
to cycles modulo boundaries. If `Q` squares to zero, finite-dimensionality and a positive
Hermitian form make this canonical map a linear equivalence.

The form, its positivity, the adjoint identity, and square-zero identity are explicit inputs.
No BRST differential, ghost system, positive Hodge structure, or Lee–Yang graded-unitarity
statement is constructed here. In particular, the abstract Hodge theorem does not establish
the positive Hodge input for the relative complex in the source.
-/

namespace VOA.LeeYangCosetTransfer

open Module (finrank)

universe u

variable {K : Type u} [AddCommGroup K] [Module ℂ K]

/-- Harmonic vectors for a linear map and its chosen adjoint. The adjoint identity is a
hypothesis of the theorems, not part of this definition. -/
def harmonicSpace (Q Qadj : K →ₗ[ℂ] K) : Submodule ℂ K :=
  LinearMap.ker Q ⊓ LinearMap.ker Qadj

/-- Boundaries viewed inside the cycle space. For a square-zero map every boundary is a
cycle, so this is precisely the usual boundary subspace of `ker Q`. Without square-zero,
this definition retains only boundaries that are cycles. -/
def boundariesInCycles (Q : K →ₗ[ℂ] K) : Submodule ℂ (LinearMap.ker Q) :=
  (LinearMap.range Q).comap (LinearMap.ker Q).subtype

/-- Cycles modulo boundaries. It is the cohomology of `Q` when `Q ∘ Q = 0`. -/
abbrev cycleQuotient (Q : K →ₗ[ℂ] K) :=
  (LinearMap.ker Q) ⧸ boundariesInCycles Q

/-- The canonical map sending a harmonic vector to its cycle class. -/
def harmonicToCohomology (Q Qadj : K →ₗ[ℂ] K) :
    harmonicSpace Q Qadj →ₗ[ℂ] cycleQuotient Q :=
  (boundariesInCycles Q).mkQ.comp (Submodule.inclusion inf_le_left)

/-- Positive definiteness forces a vector with zero self-pairing to vanish. -/
theorem eq_zero_of_sesq_self_eq_zero (h : SesqForm K) (hpos : IsPosOn h ⊤)
    {x : K} (hx : h x x = 0) : x = 0 := by
  by_contra hne
  obtain ⟨r, hr, hrx⟩ := hpos x Submodule.mem_top hne
  have : (r : ℂ) = 0 := hrx.symm.trans hx
  have : r = 0 := Complex.ofReal_eq_zero.mp this
  exact (ne_of_gt hr) this

/-- An exact vector killed by the adjoint for a positive form vanishes. This is the norm argument
used for the leading-cohomology injection; neither finite-dimensionality nor square-zero
is needed for this step. -/
theorem eq_zero_of_mem_range_of_adjoint_eq_zero
    (h : SesqForm K) (hpos : IsPosOn h ⊤) (Q Qadj : K →ₗ[ℂ] K)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y))
    {x : K} (hx : x ∈ LinearMap.range Q) (hxadj : Qadj x = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  apply eq_zero_of_sesq_self_eq_zero h hpos
  rw [hadj, hxadj, h.zero_right]

/-- The canonical harmonic-to-cycle-quotient map is injective. For square-zero `Q` its
target is `ker Q / range Q`. The stronger statement here needs neither square-zero nor
finite-dimensionality, since the quotient definition intersects boundaries with cycles. -/
theorem harmonicToCohomology_injective
    (h : SesqForm K) (hpos : IsPosOn h ⊤) (Q Qadj : K →ₗ[ℂ] K)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) :
    Function.Injective (harmonicToCohomology Q Qadj) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hxrange : (x : K) ∈ LinearMap.range Q := by
    exact (Submodule.Quotient.mk_eq_zero (boundariesInCycles Q)).mp hx
  apply Subtype.ext
  exact eq_zero_of_mem_range_of_adjoint_eq_zero h hpos Q Qadj hadj hxrange x.property.2

/-- The injective harmonic-to-cycle-quotient map bounds the harmonic dimension. No
square-zero identity is needed for this bound with the intersection quotient used here. -/
theorem finrank_harmonic_le_cohomology [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤) (Q Qadj : K →ₗ[ℂ] K)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) :
    finrank ℂ (harmonicSpace Q Qadj) ≤ finrank ℂ (cycleQuotient Q) :=
  LinearMap.finrank_le_finrank_of_injective
    (harmonicToCohomology_injective h hpos Q Qadj hadj)

/-- A positive Hermitian sesquilinear form admits an orthogonal decomposition along
every subspace of a finite-dimensional complex vector space. The proof installs the
inner product induced by this form locally, without imposing a pre-existing norm. -/
theorem exists_add_mem_sesq_orthogonal [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤)
    (hherm : ∀ x y, (starRingEnd ℂ) (h y x) = h x y)
    (S : Submodule ℂ K) (x : K) :
    ∃ y ∈ S, ∃ z ∈ h.orthogonal S, x = y + z := by
  letI core : InnerProductSpace.Core ℂ K :=
    { inner := h
      conj_inner_symm := hherm
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · subst x
          simp only [h.zero_left, map_zero, le_refl]
        · obtain ⟨r, hr, hrx⟩ := hpos x Submodule.mem_top hx
          simpa only [hrx, Complex.ofReal_re] using le_of_lt hr
      add_left := h.add_left
      smul_left := fun x y c => h.smul_left c x y
      definite := fun x hx => eq_zero_of_sesq_self_eq_zero h hpos hx }
  letI : NormedAddCommGroup K := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ K := InnerProductSpace.ofCore core.toCore
  obtain ⟨y, hy, z, hz, hxyz⟩ := S.exists_add_mem_mem_orthogonal x
  refine ⟨y, hy, z, ?_, hxyz⟩
  exact (S.mem_orthogonal z).mp hz

/-- Square-zero makes every boundary a cycle, as required for the usual cohomology
interpretation of `cycleQuotient`. -/
theorem range_le_ker_of_sq_zero (Q : K →ₗ[ℂ] K) (hQ : Q.comp Q = 0) :
    LinearMap.range Q ≤ LinearMap.ker Q := by
  rintro _ ⟨x, rfl⟩
  exact LinearMap.congr_fun hQ x

/-- Every cohomology class of a finite-dimensional square-zero complex has a harmonic
representative for a positive Hermitian form and its adjoint. -/
theorem harmonicToCohomology_surjective [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤)
    (hherm : ∀ x y, (starRingEnd ℂ) (h y x) = h x y)
    (Q Qadj : K →ₗ[ℂ] K) (hQ : Q.comp Q = 0)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) :
    Function.Surjective (harmonicToCohomology Q Qadj) := by
  intro c
  obtain ⟨x, rfl⟩ := (boundariesInCycles Q).mkQ_surjective c
  obtain ⟨y, hy, z, hz, hxyz⟩ :=
    exists_add_mem_sesq_orthogonal h hpos hherm (LinearMap.range Q) (x : K)
  have hyker : Q y = 0 := range_le_ker_of_sq_zero Q hQ hy
  have hzker : Q z = 0 := by
    have hxker : Q (x : K) = 0 := x.property
    rw [hxyz, map_add, hyker, zero_add] at hxker
    exact hxker
  have hzadj : Qadj z = 0 := by
    apply eq_zero_of_sesq_self_eq_zero h hpos
    rw [← hadj]
    exact hz _ ⟨Qadj z, rfl⟩
  refine ⟨⟨z, hzker, hzadj⟩, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change z - (x : K) ∈ LinearMap.range Q
  rw [hxyz, add_comm y z, sub_add_eq_sub_sub, sub_self, zero_sub]
  exact (LinearMap.range Q).neg_mem hy

/-- Finite-dimensional Hodge theorem: the canonical map from harmonic vectors to
`ker Q / range Q` is a complex-linear equivalence. All analytic inputs are explicit;
this theorem does not construct them for a BRST complex. -/
noncomputable def harmonicEquivCohomology [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤)
    (hherm : ∀ x y, (starRingEnd ℂ) (h y x) = h x y)
    (Q Qadj : K →ₗ[ℂ] K) (hQ : Q.comp Q = 0)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) :
    harmonicSpace Q Qadj ≃ₗ[ℂ] cycleQuotient Q :=
  LinearEquiv.ofBijective (harmonicToCohomology Q Qadj)
    ⟨harmonicToCohomology_injective h hpos Q Qadj hadj,
      harmonicToCohomology_surjective h hpos hherm Q Qadj hQ hadj⟩

/-- The Hodge equivalence sends a harmonic vector to its canonical cycle class. -/
@[simp] theorem harmonicEquivCohomology_apply [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤)
    (hherm : ∀ x y, (starRingEnd ℂ) (h y x) = h x y)
    (Q Qadj : K →ₗ[ℂ] K) (hQ : Q.comp Q = 0)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) (x : harmonicSpace Q Qadj) :
    harmonicEquivCohomology h hpos hherm Q Qadj hQ hadj x =
      harmonicToCohomology Q Qadj x := rfl

/-- The finite-dimensional Hodge equivalence gives equality of harmonic and cohomology
dimensions, rather than merely the injective bound. -/
theorem finrank_harmonic_eq_cohomology [FiniteDimensional ℂ K]
    (h : SesqForm K) (hpos : IsPosOn h ⊤)
    (hherm : ∀ x y, (starRingEnd ℂ) (h y x) = h x y)
    (Q Qadj : K →ₗ[ℂ] K) (hQ : Q.comp Q = 0)
    (hadj : ∀ x y, h (Q x) y = h x (Qadj y)) :
    finrank ℂ (harmonicSpace Q Qadj) = finrank ℂ (cycleQuotient Q) :=
  (harmonicEquivCohomology h hpos hherm Q Qadj hQ hadj).finrank_eq

end VOA.LeeYangCosetTransfer
