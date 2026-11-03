/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.InverseDSVirasoroVerma
import VOA.Examples.InverseDSLeeYangFockVirasoro
import VOA.Examples.VirasoroVacuumEvaluation

/-!
# Nonvanishing of every Virasoro Verma highest vector

The existing charged rank-one Fock modes have central charge 1-24 ell²
and vacuum weight p²-2 ell p. Two complex square roots realize any specified
pair (c,h). Their nonzero polynomial vacuum witnesses that the universal
Verma highest vector is nonzero. This proves nontriviality for every (c,h),
without PBW, but does not prove a Verma basis or singular-vector existence.
-/
namespace VOA.InverseDS.VirasoroVerma
open Module (End)
open VirModule LeeYangWardClosure
open LeeYangFockExponential LeeYangFockVirasoro VirDeformModes
open LieAlgebra LieAlgebra.Extension

/-- Charged Fock modes and their scalar central operator, packaged for the
already proved extension from mode commutators to the full Virasoro algebra. -/
noncomputable def chargedFockData (ell p : ℂ) : CentralVirasoroData LeeYangFock where
  L := sectorVirasoro ell p
  central := (1-24*ell^2) • 1
  comm m n := by
    rw [LieRing.of_associative_ring_bracket, sectorVirasoro_virasoro]
    by_cases h : m+n=0 <;> simp [h, smul_smul]
  central_comm n := by
    change ((1-24*ell^2) • (1 : End ℂ LeeYangFock)) * sectorVirasoro ell p n = _
    simp

/-- The charged Fock space is an actual Virasoro representation with charge
1-24 ell², at arbitrary momentum p. No quotient or faithfulness is asserted. -/
noncomputable def chargedFockRep (ell p : ℂ) : VirRep LeeYangFock where
  ρ := fixedRho (chargedFockData ell p) rfl
  centralCharge := 1-24*ell^2
  acts_central := fixedRho_C (chargedFockData ell p) rfl

/-- The full Lie action recovers the explicitly constructed charged modes. -/
theorem chargedFockRep_mode (ell p : ℂ) (n : ℤ) :
    virMode (chargedFockRep ell p) n = sectorVirasoro ell p n :=
  fixedRho_L (chargedFockData ell p) rfl n

/-- All positive charged modes annihilate the constant polynomial vacuum. -/
theorem chargedFock_positive_vacuum (ell p : ℂ) (n : ℤ) (hn : 0 < n) :
    sectorVirasoro ell p n (HeisenbergN.vacuumN 1) = 0 := by
  simp [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    alphaMode, show n ≠ 0 by omega, HeisenbergN.LvirN_vacuum 1 2 (by omega : -1 ≤ n),
    HeisenbergN.oscN_vacuum 1 2 0 n (by omega : 0 ≤ n)]

/-- The zero mode reads the charged vacuum weight p²-2 ell p. The zero
oscillator vanishes on the polynomial carrier; the scalar shifts remain. -/
theorem chargedFock_zero_vacuum (ell p : ℂ) :
    sectorVirasoro ell p 0 (HeisenbergN.vacuumN 1) =
      (p^2-2*ell*p) • HeisenbergN.vacuumN 1 := by
  simp [sectorVirasoro, sectorSugawara, sectorBackgroundCurrent, sectorCurrent,
    alphaMode, HeisenbergN.LvirN_vacuum 1 2 (by norm_num : (-1:ℤ) ≤ 0),
    smul_smul]
  module

/-- The charged constant polynomial satisfies all highest-weight equations,
with its explicit central charge and zero-mode eigenvalue. -/
theorem chargedFock_isHighest (ell p : ℂ) :
    IsHighestWeightVector (chargedFockRep ell p) (HeisenbergN.vacuumN 1)
      (1-24*ell^2) (p^2-2*ell*p) where
  centralCharge := rfl
  pos_annihilate n hn := by
    rw [chargedFockRep_mode]
    exact chargedFock_positive_vacuum ell p n hn
  zero_acts := by
    rw [chargedFockRep_mode]
    exact chargedFock_zero_vacuum ell p

/-- Every complex charge and highest weight can be realized by a background
and a momentum. First solve ell²=(1-c)/24, then (p-ell)²=h+ell². -/
theorem exists_chargedFock_parameters (c h : ℂ) :
    ∃ ell p : ℂ, 1-24*ell^2=c ∧ p^2-2*ell*p=h := by
  obtain ⟨ell,he⟩ := IsAlgClosed.exists_pow_nat_eq ((1-c)/24) (by norm_num : 0 < 2)
  obtain ⟨q,hq⟩ := IsAlgClosed.exists_pow_nat_eq (h+ell^2) (by norm_num : 0 < 2)
  refine ⟨ell,ell+q,?_,?_⟩
  · linear_combination -24*he
  · linear_combination hq

/-- The formal highest vector of M(c,h) is nonzero for every complex pair.
Its universal map reaches the nonzero constant polynomial in a charged Fock
representation. No project PBW axiom or Verma independence theorem is used. -/
theorem highestVector_ne_zero (c h : ℂ) : highestVector c h ≠ 0 := by
  obtain ⟨ell,p,hc,hh⟩ := exists_chargedFock_parameters c h
  have hv := chargedFock_isHighest ell p
  rw [hc,hh] at hv
  apply highestVector_ne_zero_of_realization _ _ hv
  exact one_ne_zero

/-- Every universal Verma quotient is a nontrivial vector space, witnessed
by its highest vector. This does not establish its graded dimensions. -/
theorem verma_nontrivial (c h : ℂ) : Nontrivial (Verma c h) :=
  ⟨⟨highestVector c h, 0, highestVector_ne_zero c h⟩⟩

end VOA.InverseDS.VirasoroVerma
