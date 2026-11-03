/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroScreeningSingular
import VOA.Examples.VirasoroKacDegreeCount
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Actual rank-one Fock level dimensions

A homogeneous polynomial is a finite coefficient function on the occupations
of its energy. Forgetting the unique colour and converting multiplicities
to a multiset identifies those occupations with the actual Verma partition
indices. The resulting dimension equality concerns the existing Fock and
Verma subspaces, not an assumed character or a proposed basis count.
-/
namespace VOA.VirasoroScreening
open HeisenbergN MvPolynomial
open InverseDS.VirasoroVerma

/-- The multiset of a plain occupation has exactly its oscillator energy. -/
theorem occupation_multiset_energy (d : ℕ →₀ ℕ) :
    vermaMultisetEnergy d.toMultiset = Finsupp.weight (fun i => i+1) d := by
  induction d using Finsupp.induction_linear with
  | zero => simp [vermaMultisetEnergy]
  | add d e hd he => rw [Finsupp.toMultiset_add, vermaMultisetEnergy_add, map_add, hd, he]
  | single i n => simp [vermaMultisetEnergy, Finsupp.toMultiset_single,
      Finsupp.weight_single, Multiset.map_nsmul, Multiset.sum_nsmul]

/-- Forgetting the single colour preserves the exact energy of every
actual occupation, in the reverse direction to fockOccupation_weight. -/
theorem plainOccupation_weight (d : (ℕ × Fin 1) →₀ ℕ) :
    Finsupp.weight (fun i => i+1) (plainOccupation d) = Finsupp.weight weightFnN d := by
  rw [← fockOccupation_weight, fock_plainOccupation]

/-- Actual energy-N Fock occupations are equivalent to the multiset
partition indices already used by the actual Verma PBW basis. -/
noncomputable def fockMultisetPartitionEquiv (N : ℕ) :
    {d : (ℕ × Fin 1) →₀ ℕ // Finsupp.weight weightFnN d = N} ≃
      VermaMultisetPartitions N where
  toFun d := ⟨(plainOccupation d.val).toMultiset, by
    rw [occupation_multiset_energy, plainOccupation_weight]; exact d.property⟩
  invFun s := ⟨fockOccupation s.val.toFinsupp, by
    rw [fockOccupation_weight, ← occupation_multiset_energy, Multiset.toFinsupp_toMultiset]
    exact s.property⟩
  left_inv d := by
    apply Subtype.ext
    simp only [Finsupp.toMultiset_toFinsupp, fock_plainOccupation]
  right_inv s := by
    apply Subtype.ext
    simp only [plain_fockOccupation, Multiset.toFinsupp_toMultiset]

/-- The actual Fock level is linearly equivalent to finitely supported
coefficients on its energy-N occupations. The equivalence transports the
homogeneous-submodule definition, without asserting PBW for a quotient. -/
noncomputable def fockLevelCoefficientEquiv (N : ℕ) :
    gradingWN 1 N ≃ₗ[ℂ]
      ({d : (ℕ × Fin 1) →₀ ℕ // Finsupp.weight weightFnN d = N} →₀ ℂ) := by
  rw [gradingWN, weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact Finsupp.supportedEquivFinsupp _

/-- Every actual Fock level is finite-dimensional, by its finite set of
energy occupations. -/
noncomputable instance fockLevel_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (gradingWN 1 N) := by
  letI : Fintype {d : (ℕ × Fin 1) →₀ ℕ // Finsupp.weight weightFnN d = N} :=
    Fintype.ofEquiv (VermaMultisetPartitions N) (fockMultisetPartitionEquiv N).symm
  exact (fockLevelCoefficientEquiv N).symm.finiteDimensional

/-- The dimension of the actual rank-one energy-N Fock level is the
cardinality of the actual Verma PBW partition index set, including parts one. -/
theorem fockLevel_finrank (N : ℕ) :
    Module.finrank ℂ (gradingWN 1 N) = Fintype.card (VermaPartitions N) := by
  letI : Fintype {d : (ℕ × Fin 1) →₀ ℕ // Finsupp.weight weightFnN d = N} :=
    Fintype.ofEquiv (VermaMultisetPartitions N) (fockMultisetPartitionEquiv N).symm
  rw [(fockLevelCoefficientEquiv N).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr (fockMultisetPartitionEquiv N), vermaMultisetPartitions_card]

/-- The ACTUAL Fock and Verma level subspaces have equal dimensions at
every complex charge and highest weight. This is a level count, not a
claim that an arbitrary representation map between them is an isomorphism. -/
theorem fock_verma_level_finrank (c h : ℂ) (N : ℕ) :
    Module.finrank ℂ (gradingWN 1 N) = Module.finrank ℂ (sortedSpan c h N) := by
  rw [fockLevel_finrank, vermaLevel_finrank]

end VOA.VirasoroScreening
