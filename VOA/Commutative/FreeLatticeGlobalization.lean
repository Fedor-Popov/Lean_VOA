/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Commutative.HeightOneGlobalization

/-!
# Globalizing an actual free lattice from local denominator witnesses

For a basis over the fraction field, its base-ring span is exactly the vectors
with integral coordinates. Membership is detected at height-one primes by
ordinary denominator witnesses: some scalar outside the prime sends the vector
into that span.

The Deligne carrier argument uses this with the free global fusion module as
the lattice. This theorem proves the extension step for the actual span, rather
than only for a separately defined coordinate lattice. The local comparisons
with the full arc carrier remain inputs to the application.
-/

namespace VOA.FreeLatticeGlobalization

open Module VOA.HeightOneGlobalization

noncomputable section

variable {R F V ι : Type*}
variable [CommRing R] [IsDomain R]
variable [Field F] [Algebra R F] [IsFractionRing R F]
variable [AddCommGroup V] [Module F V] [Module R V] [IsScalarTower R F V]
variable [Finite ι]

/-- The actual base-ring span of a fraction-field basis. -/
def lattice (b : Basis ι F V) : Submodule R V :=
  Submodule.span R (Set.range b)

omit [IsDomain R] [IsFractionRing R F] in
/-- A vector belongs to the free lattice precisely when all its basis
coefficients belong to the base ring. -/
theorem mem_lattice_iff (b : Basis ι F V) (x : V) :
    x ∈ lattice (R := R) b ↔ ∀ i, IsLocalization.IsInteger R (b.repr x i) := by
  classical
  letI := Fintype.ofFinite ι
  constructor
  · intro hx
    have hle : lattice (R := R) b ≤
        pulledBackIntegralLattice (b.repr.restrictScalars R) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩ j
      change IsLocalization.IsInteger R (b.repr (b i) j)
      simp only [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    exact hle hx
  · intro hx
    choose c hc using hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    rw [← hc i, IsScalarTower.algebraMap_smul F (c i) (b i)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A local denominator witness makes every rational basis coefficient regular
at that prime. -/
theorem coordinates_regular_of_local_witness (b : Basis ι F V) (x : V)
    (p : HeightOnePrime R)
    (hx : ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    ∀ i, b.repr x i ∈ heightOneLocalization (K := F) p := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hcoords := (mem_lattice_iff b (s • x)).mp hsx
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    rw [h]
    exact p.asIdeal.zero_mem
  have hsF : algebraMap R F s ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R F).ne hs0
  intro i
  obtain ⟨r, hr⟩ := hcoords i
  have hr' : algebraMap R F r = algebraMap R F s * b.repr x i := by
    rw [← IsScalarTower.algebraMap_smul F s x, map_smul, Finsupp.smul_apply,
      smul_eq_mul] at hr
    exact hr
  change ∃ (a t : R) (_ : t ∈ p.asIdeal.primeCompl),
    b.repr x i = algebraMap R F a * (algebraMap R F t)⁻¹
  refine ⟨r, s, hs, ?_⟩
  rw [hr']
  field_simp

/-- Height-one local membership implies global membership in the actual free
span. This discharges the extension across higher-codimension collisions. -/
theorem mem_lattice_of_local_witnesses
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (b : Basis ι F V) (x : V)
    (hx : ∀ p : HeightOnePrime R,
      ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    x ∈ lattice (R := R) b := by
  apply (mem_lattice_iff b x).mpr
  intro i
  exact isInteger_of_mem_heightOneLocalizations fun p =>
    coordinates_regular_of_local_witness b x p (hx p) i

/-- A candidate carrier containing the free cyclic lattice equals it as soon
as every carrier vector is locally in that lattice at every divisor. -/
theorem carrier_eq_lattice_of_local_witnesses
    [UniqueFactorizationMonoid R] [IsNoetherianRing R]
    (b : Basis ι F V) (W : Submodule R V)
    (hMW : lattice (R := R) b ≤ W)
    (hlocal : ∀ x ∈ W, ∀ p : HeightOnePrime R,
      ∃ s : R, s ∉ p.asIdeal ∧ s • x ∈ lattice (R := R) b) :
    W = lattice (R := R) b := by
  apply le_antisymm _ hMW
  intro x hx
  exact mem_lattice_of_local_witnesses b x (hlocal x hx)

end

end VOA.FreeLatticeGlobalization

section AxiomAudit
#print axioms VOA.FreeLatticeGlobalization.mem_lattice_iff
#print axioms VOA.FreeLatticeGlobalization.mem_lattice_of_local_witnesses
#print axioms VOA.FreeLatticeGlobalization.carrier_eq_lattice_of_local_witnesses
end AxiomAudit
