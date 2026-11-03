/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroDescendantIndependence
import VOA.Examples.VirasoroSingularGram

/-!
# Singular descendants give partition-sized determinant multiplicities

A nonzero singular state at level n has an independent descendant family
indexed by partitions of m into parts at least two. At level n+m these states
lie in the canonical radical, hence supply that many determinant factors.
This is a uniform lower bound from an actual singular state. It neither
constructs minimal-model singular states nor proves a simple-root upper bound.
-/
namespace VOA.VirDeformModes.NormalOrdering
open VirModule VirSimple VertexOperatorAlgebra

/-- A creation word increases conformal weight by its energy, on any
homogeneous starting state. -/
theorem creationDescendant_mem_grading (c : ℂ) (w : List ℕ) {q : ℤ}
    (v : VirUniv c) (hv : v ∈ gradingVir c q) :
    creationDescendant c w v ∈ gradingVir c (q+(energyVir w:ℤ)) := by
  induction w with
  | nil => simpa [creationDescendant] using hv
  | cons i w ih =>
    have hh := Lop_neg_maps_grading c i ih
    convert hh using 1 <;> simp only [energyVir_cons, Nat.cast_add, Nat.cast_ofNat] <;> ring

/-- The descendant convention agrees with the general Virasoro word action,
so the already proved adjoint-word radical theorem applies directly. -/
theorem creationDescendant_eq_virWord (c : ℂ) (w : List ℕ) (v : VirUniv c) :
    creationDescendant c w v =
      virWord (virasoroVOA c).L (w.map fun (i : ℕ) => -(i:ℤ)-2) v := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [creationDescendant, LinearMap.comp_apply, List.map_cons,
      virWord, Module.End.mul_apply, virasoroVOA_L_eq_Lop] using congrArg (Lop c (-(i:ℤ)-2)) ih

/-- Every creation descendant of a positive-weight singular state pairs to
zero with every vacuum-module state. Independence is supplied separately. -/
theorem creationDescendant_singular_pairing_zero (c : ℂ) {n : ℕ} (hn : 0 < n)
    (v : VirUniv c) (hv : v ∈ gradingVir c (n:ℤ))
    (h1 : Lop c 1 v = 0) (h2 : Lop c 2 v = 0) (w : List ℕ) (x : VirUniv c) :
    (VirGram4.canB c).form (creationDescendant c w v) x = 0 := by
  rw [creationDescendant_eq_virWord]
  exact canB_singular_descendant_zero c hn v hv h1 h2 _ x

/-- Partition-indexed descendants at a fixed added energy, bundled in the
correct graded subspace. Parts one are deliberately excluded. -/
noncomputable def gradedCreationDescendant (c : ℂ) {n : ℕ}
    (v : gradingVir c (n:ℤ)) (m : ℕ) (w : SortedOfEnergy m) :
    gradingVir c ((n+m:ℕ):ℤ) :=
  ⟨creationDescendant c w.1 v, by
    have hh := creationDescendant_mem_grading c w.1 v v.property
    simpa [w.property.2] using hh⟩

/-- A nonzero starting state gives exactly one independent member for each
partition of the added energy into parts at least two. No quotient or
hypothesis about descendant independence is hidden in this statement. -/
theorem gradedCreationDescendant_linearIndependent (c : ℂ) {n : ℕ}
    (v : gradingVir c (n:ℤ)) (hv : v ≠ 0) (m : ℕ) :
    LinearIndependent ℂ (gradedCreationDescendant c v m) := by
  have hv' : (v : VirUniv c) ≠ 0 := fun he => hv (Subtype.ext he)
  let e : SortedOfEnergy m → {w : List ℕ // SortedWord w} := fun w => ⟨w.1,w.property.1⟩
  have hi : Function.Injective e := by
    intro u w he
    exact Subtype.ext (congrArg (fun z : {w : List ℕ // SortedWord w} => z.1) he)
  have hh := (creationDescendant_linearIndependent c v hv').comp e hi
  exact LinearIndependent.of_comp (gradingVir c ((n+m:ℕ):ℤ)).subtype hh

/-- Coordinates of each singular descendant are actual null rows of the
level-(n+m) polynomial Gram matrix, after specialization at the charge. -/
theorem gradedCreationDescendant_gram_row (c : ℂ) {n : ℕ} (hn : 0 < n)
    (v : gradingVir c (n:ℤ)) (h1 : Lop c 1 (v : VirUniv c) = 0)
    (h2 : Lop c 2 (v : VirUniv c) = 0) (m : ℕ)
    (i : SortedOfEnergy m) (j : SortedOfEnergy (n+m)) :
    ∑ k, (gradedBasis c (n+m)).equivFun (gradedCreationDescendant c v m i) k *
      (partitionGramPolynomial (n+m) k j).eval c = 0 := by
  let b := gradedBasis c (n+m)
  have he : ∀ k, (partitionGramPolynomial (n+m) k j).eval c =
      (VirGram4.canB c).form (b k : VirUniv c) (b j : VirUniv c) := by
    intro k
    simpa only [Matrix.map_apply, GramMat.gramMatrix_apply, b] using
      congrArg (fun M => M k j) (partitionGramPolynomial_eval c (n+m))
  simp_rw [he]
  have hs := congrArg (gradingVir c ((n+m:ℕ):ℤ)).subtype
    (b.sum_equivFun (gradedCreationDescendant c v m i))
  simp only [map_sum, map_smul] at hs
  have hh := congrArg (fun x => (VirGram4.canB c).form x (b j : VirUniv c)) hs
  have hz := creationDescendant_singular_pairing_zero c hn v v.property h1 h2 i.1 (b j)
  simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul] using hh.trans hz

/-- A nonzero singular state at level n forces at least p₂(m) factors X-c
in the actual determinant at level n+m. This is a proved uniform descendant
multiplicity lower bound, not the full vacuum Kac multiplicity formula. -/
theorem partitionDeterminant_dvd_of_singular_descendants (c : ℂ) {n : ℕ} (hn : 0 < n)
    (v : gradingVir c (n:ℤ)) (hv : v ≠ 0)
    (h1 : Lop c 1 (v : VirUniv c) = 0) (h2 : Lop c 2 (v : VirUniv c) = 0) (m : ℕ) :
    (Polynomial.X-Polynomial.C c)^(Fintype.card (SortedOfEnergy m)) ∣
      (partitionGramPolynomial (n+m)).det := by
  have hi := (gradedCreationDescendant_linearIndependent c v hv m).map'
    (gradedBasis c (n+m)).equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr (gradedBasis c (n+m)).equivFun.injective)
  exact pow_X_sub_C_dvd_det_of_independent_null_rows _ c _ hi
    (fun i j => gradedCreationDescendant_gram_row c hn v h1 h2 m i j)
end VOA.VirDeformModes.NormalOrdering
