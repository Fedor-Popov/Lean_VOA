/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Dimension squeeze for the Lee–Yang coset comparison

This file proves the finite-dimensional linear algebra used in the coset-injection and
strictness step of the coset BRST–Koszul transfer argument. An injective linear
map carries each source piece into a target piece. If a numerical upper bound for the target
piece is also the dimension of the source piece, their images are equal. Exhaustion of the
target then makes the original map an isomorphism, carrying every source piece onto its
specified target piece.

The numerical bounds are an arbitrary function `d`, so a later application can supply a sum
of character coefficients without changing this linear-algebra argument. No such character
identity, coset injection, or BRST dimension bound is established here. The results hold for
arbitrarily indexed families of subspaces; in particular they apply to increasing flags,
without needing their monotonicity or exhaustion of the source.
-/

namespace VOA.LeeYangCosetTransfer

open Module

universe u v w t

variable {𝕜 : Type u} [DivisionRing 𝕜]
variable {C : Type v} [AddCommGroup C] [Module 𝕜 C]
variable {H : Type w} [AddCommGroup H] [Module 𝕜 H]
variable {ι : Type t}

/-- The lower inequality in the coset dimension chain follows from filtered injectivity.
Only the target piece needs to be finite-dimensional. -/
theorem finrank_le_of_filtered_injective
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : Submodule 𝕜 C) (F : Submodule 𝕜 H) [FiniteDimensional 𝕜 F]
    (hfiltered : P.map i ≤ F) : finrank 𝕜 P ≤ finrank 𝕜 F := by
  calc
    finrank 𝕜 P = finrank 𝕜 (P.map i) :=
      (Submodule.equivMapOfInjective i hi P).finrank_eq
    _ ≤ finrank 𝕜 F := Submodule.finrank_mono hfiltered

/-- An injective filtered map is onto a target piece when an upper bound for that piece is
exactly the dimension of the source piece. This is the single-piece dimension squeeze. -/
theorem map_eq_of_finrank_squeeze
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : Submodule 𝕜 C) (F : Submodule 𝕜 H) [FiniteDimensional 𝕜 F]
    (d : ℕ) (hfiltered : P.map i ≤ F)
    (hupper : finrank 𝕜 F ≤ d) (hexact : d = finrank 𝕜 P) : P.map i = F := by
  apply Submodule.eq_of_le_of_finrank_le hfiltered
  calc
    finrank 𝕜 F ≤ d := hupper
    _ = finrank 𝕜 P := hexact
    _ = finrank 𝕜 (P.map i) := (Submodule.equivMapOfInjective i hi P).finrank_eq

variable [FiniteDimensional 𝕜 H]

/-- Pointwise dimension squeeze identifies every piece of the two families. The bound `d r`
may later be a cumulative character coefficient; this theorem assumes its value explicitly. -/
theorem maps_eq_of_finrank_squeeze
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) : ∀ r, (P r).map i = F r := by
  intro r
  exact map_eq_of_finrank_squeeze i hi (P r) (F r) (d r)
    (hfiltered r) (hupper r) (hexact r)

/-- All dimensions in the filtered squeeze are equal, including the supplied numerical bound. -/
theorem finranks_eq_of_squeeze
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) :
    ∀ r, finrank 𝕜 (P r) = finrank 𝕜 (F r) ∧ finrank 𝕜 (F r) = d r := by
  intro r
  have hdim : finrank 𝕜 (P r) = finrank 𝕜 (F r) := by
    rw [← maps_eq_of_finrank_squeeze i hi P F d hfiltered hupper hexact r]
    exact (Submodule.equivMapOfInjective i hi (P r)).finrank_eq
  exact ⟨hdim, hdim.symm.trans (hexact r).symm⟩

omit [FiniteDimensional 𝕜 H] in
/-- If the target pieces span the target, equality of all piece images makes the map
surjective. For increasing exhaustive flags, the spanning hypothesis is their usual supremum
exhaustion. No additional hypothesis on the source flag is needed. -/
theorem surjective_of_maps_eq_of_exhaustive
    (i : C →ₗ[𝕜] H) (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H)
    (hpieces : ∀ r, (P r).map i = F r) (hexhaustive : iSup F = ⊤) :
    Function.Surjective i := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hexhaustive]
  apply iSup_le
  intro r
  rw [← hpieces r]
  exact LinearMap.map_le_range

/-- The dimension squeeze and exhaustion of the target imply surjectivity of the original
injective linear map. The character and cohomology bounds remain explicit hypotheses. -/
theorem surjective_of_finrank_squeeze
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) (hexhaustive : iSup F = ⊤) :
    Function.Surjective i := by
  exact surjective_of_maps_eq_of_exhaustive i P F
    (maps_eq_of_finrank_squeeze i hi P F d hfiltered hupper hexact) hexhaustive

/-- The linear equivalence supplied by the filtered dimension squeeze. Its underlying map
is the given injection; it does not construct a concrete coset or BRST map. -/
noncomputable def linearEquivOfFinrankSqueeze
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) (hexhaustive : iSup F = ⊤) : C ≃ₗ[𝕜] H :=
  LinearEquiv.ofBijective i
    ⟨hi, surjective_of_finrank_squeeze i hi P F d hfiltered hupper hexact hexhaustive⟩

/-- The equivalence from the squeeze is the original map, so all established form and
conjugation compatibility of that map remains applicable. -/
@[simp] theorem linearEquivOfFinrankSqueeze_apply
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) (hexhaustive : iSup F = ⊤) (x : C) :
    linearEquivOfFinrankSqueeze i hi P F d hfiltered hupper hexact hexhaustive x = i x := rfl

/-- The equivalence obtained by the dimension squeeze carries every source piece onto the
specified target piece, giving the filtered strictness needed for metric transfer. -/
theorem linearEquivOfFinrankSqueeze_map
    (i : C →ₗ[𝕜] H) (hi : Function.Injective i)
    (P : ι → Submodule 𝕜 C) (F : ι → Submodule 𝕜 H) (d : ι → ℕ)
    (hfiltered : ∀ r, (P r).map i ≤ F r)
    (hupper : ∀ r, finrank 𝕜 (F r) ≤ d r)
    (hexact : ∀ r, d r = finrank 𝕜 (P r)) (hexhaustive : iSup F = ⊤) (r : ι) :
    (P r).map
        (linearEquivOfFinrankSqueeze i hi P F d hfiltered hupper hexact hexhaustive).toLinearMap =
      F r := by
  exact maps_eq_of_finrank_squeeze i hi P F d hfiltered hupper hexact r

end VOA.LeeYangCosetTransfer
