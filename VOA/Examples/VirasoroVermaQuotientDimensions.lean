/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaMaximalRadical
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Actual irreducible Verma level dimensions and Gram ranks

Each level of the actual radical quotient is the image of the corresponding
Verma level. Its dimension is exactly the rank of the actual Gram matrix.
This identifies the irreducible dimensions appearing in ordinary determinant
formulas, but does not compute them by a Kac or minimal-model character formula.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- Assemble arbitrary partition coordinates by a linear map into the
actual Verma module. Its value is the existing finite PBW sum. -/
noncomputable def vermaLevelAssembly (c h : ℂ) (n : ℕ) :
    (VermaPartitions n → ℂ) →ₗ[ℂ] Verma c h where
  toFun := vermaLevelState c h n
  map_add' a b := by simp [vermaLevelState,add_smul,Finset.sum_add_distrib]
  map_smul' a b := by simp [vermaLevelState,Finset.smul_sum,smul_smul]

/-- The partition assembly reaches exactly the actual level span, because
the partition family is a proved basis, not an assumed spanning set. -/
theorem vermaLevelAssembly_range (c h : ℂ) (n : ℕ) :
    LinearMap.range (vermaLevelAssembly c h n)=sortedSpan c h n := by
  ext v
  constructor
  · rintro ⟨a,rfl⟩
    exact vermaLevelState_mem c h n a
  · intro hv
    obtain ⟨a,ha⟩ := exists_vermaLevelState c h n v hv
    exact ⟨a,ha⟩

/-- The actual level-n subspace of the irreducible radical quotient. It is
an image of the genuine Verma level, with no assumed irreducible character. -/
noncomputable def vermaSimpleLevel (c h : ℂ) (n : ℕ) : Submodule ℂ (VermaSimple c h) :=
  (sortedSpan c h n).map (vermaRadical c h).mkQ

/-- Project partition coordinates into the actual irreducible quotient. -/
noncomputable def vermaSimpleLevelAssembly (c h : ℂ) (n : ℕ) :
    (VermaPartitions n → ℂ) →ₗ[ℂ] VermaSimple c h :=
  (vermaRadical c h).mkQ.comp (vermaLevelAssembly c h n)

/-- Quotient assembly reaches exactly the actual quotient level. -/
theorem vermaSimpleLevelAssembly_range (c h : ℂ) (n : ℕ) :
    LinearMap.range (vermaSimpleLevelAssembly c h n)=vermaSimpleLevel c h n := by
  rw [vermaSimpleLevelAssembly,LinearMap.range_comp,vermaLevelAssembly_range]
  rfl

/-- The coordinates killed by quotient projection are EXACTLY the Gram
kernel. Orthogonality to other levels has already been proved, so a finite
Gram test here detects the full radical rather than only a restricted form. -/
theorem vermaSimpleLevelAssembly_ker (c h : ℂ) (n : ℕ) :
    LinearMap.ker (vermaSimpleLevelAssembly c h n)=
      LinearMap.ker (vermaGramMatrix c h n).mulVecLin := by
  ext a
  change (vermaRadical c h).mkQ (vermaLevelState c h n a)=0 ↔ _
  rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,mem_vermaRadical]
  exact (vermaGramMatrix_kernel_iff_radical c h n a).symm

/-- Every actual irreducible level has dimension equal to the actual Gram
rank, at every complex charge and highest weight. This is a character
interpretation, not a closed formula for the rank. -/
theorem vermaSimpleLevel_finrank_eq_gramRank (c h : ℂ) (n : ℕ) :
    Module.finrank ℂ (vermaSimpleLevel c h n)=(vermaGramMatrix c h n).rank := by
  have hq := (vermaSimpleLevelAssembly c h n).finrank_range_add_finrank_ker
  have hg := (vermaGramMatrix c h n).mulVecLin.finrank_range_add_finrank_ker
  rw [vermaSimpleLevelAssembly_range,vermaSimpleLevelAssembly_ker] at hq
  exact Nat.add_right_cancel (hq.trans hg.symm)

/-- At a nondegenerate Gram level the irreducible quotient loses no states:
its dimension is the full partition number. The nonzero determinant remains
an ordinary input, not an assumed description of the Kac singular locus. -/
theorem vermaSimpleLevel_finrank_of_det_ne_zero (c h : ℂ) (n : ℕ)
    [DecidableEq (VermaPartitions n)] (hd : (vermaGramMatrix c h n).det≠0) :
    Module.finrank ℂ (vermaSimpleLevel c h n)=Fintype.card (VermaPartitions n) := by
  rw [vermaSimpleLevel_finrank_eq_gramRank]
  exact Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))

/-- The actual Gram determinant at relative level zero is one. The only
partition is the empty word, and the highest vector has normalized norm one. -/
theorem vermaGramMatrix_zero_det (c h : ℂ) [DecidableEq (VermaPartitions 0)] :
    (vermaGramMatrix c h 0).det=1 := by
  letI : Unique (VermaPartitions 0) := {
    default := ⟨[],sortedWord_nil,rfl⟩
    uniq := fun w => Subtype.ext ((verma_energy_zero_iff w.val).mp w.property.2) }
  rw [Matrix.det_unique]
  exact vermaContravariant_normalized c h

/-- The actual irreducible highest-weight line has dimension one at every
parameter. This is the ordinary line dimension used at the first singular
level in the cited vacuum determinant argument; the determinant formula
itself is still a separate unformalized input. -/
theorem vermaSimpleLevel_zero_finrank (c h : ℂ) :
    Module.finrank ℂ (vermaSimpleLevel c h 0)=1 := by
  classical
  letI : Unique (VermaPartitions 0) := {
    default := ⟨[],sortedWord_nil,rfl⟩
    uniq := fun w => Subtype.ext ((verma_energy_zero_iff w.val).mp w.property.2) }
  rw [vermaSimpleLevel_finrank_of_det_ne_zero c h 0 (by rw [vermaGramMatrix_zero_det]; exact one_ne_zero)]
  exact Fintype.card_unique

end VOA.InverseDS.VirasoroVerma
