/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaDescendantIndependence
import VOA.Examples.VirasoroVermaGramPolynomial
import VOA.Examples.VirasoroGramDivisibility

/-!
# Actual singular Verma embeddings and full partition multiplicities

A nonzero highest-weight state in any Verma module generates an injective
copy of its own Verma module. The resulting descendants give full partition
counts, including parts one, in the radical of every higher Gram level.
These are lower multiplicity bounds from actual singular states; they do
not construct general Kac singular states or prove vacuum simple roots.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The universal map on a PBW word is that same negative word acting on
the chosen highest-weight state in the target Verma module. -/
theorem verma_universalMap_word (c h k : ℂ) (v : Verma c h)
    (hv : IsHighestWeightVector (vermaRep c h) v c k) (w : List ℕ) :
    universalMap (vermaRep c h) v hv (negWord c k w)=vermaDescendant c h w v := by
  induction w with
  | nil => exact universalMap_highestVector _ _ _
  | cons i w ih =>
    rw [negWord_cons]
    change universalMap _ _ _ (vermaRho _ _ _ _) = _
    rw [universalMap_intertwines,ih]
    rfl

/-- Every nonzero highest-weight state in an actual Verma module defines
an INJECTIVE Verma homomorphism. Full descendant independence proves this
without assuming a character formula or an abstract enveloping-algebra domain. -/
theorem verma_universalMap_injective (c h k : ℂ) (v : Verma c h)
    (hv : IsHighestWeightVector (vermaRep c h) v c k) (hne : v≠0) :
    Function.Injective (universalMap (vermaRep c h) v hv) := by
  have he : universalMap (vermaRep c h) v hv =
      (vermaSortedBasis c k).constr ℂ
        (fun w => vermaDescendant c h w.val v) := by
    apply (vermaSortedBasis c k).ext
    intro w
    rw [Module.Basis.constr_basis,vermaSortedBasis_apply,verma_universalMap_word]
  rw [he]
  exact (vermaSortedBasis c k).injective_constr_of_linearIndependent
    (vermaDescendant_linearIndependent c h v hne)

/-- A homogeneous state killed by L1 and L2 is an actual highest-weight
vector of shifted weight h+n, with the target module's central charge. -/
theorem verma_singular_isHighest (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0) :
    IsHighestWeightVector (vermaRep c h) v c (h+(n:ℂ)) where
  centralCharge := rfl
  pos_annihilate := verma_positive_zero_of_one_two c h v h1 h2
  zero_acts := (verma_mem_level_iff_eigen c h n v).mp hv

/-- A singular state at relative level n generates the genuine shifted
Verma representation M(c,h+n) inside M(c,h). -/
noncomputable def vermaSingularMap (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0) :
    Verma c (h+(n:ℂ)) →ₗ[ℂ] Verma c h :=
  universalMap (vermaRep c h) v (verma_singular_isHighest c h n v hv h1 h2)

/-- The actual shifted singular representation map is injective whenever
its generating state is nonzero. -/
theorem vermaSingularMap_injective (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hne : v≠0)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0) :
    Function.Injective (vermaSingularMap c h n v hv h1 h2) :=
  verma_universalMap_injective c h _ v _ hne

/-- An arbitrary negative descendant adds its full word energy to relative
level, including each translation letter's contribution of one. -/
theorem vermaDescendant_mem_level (c h : ℂ) (w : List ℕ) (n : ℕ)
    (v : Verma c h) (hv : v ∈ sortedSpan c h n) :
    vermaDescendant c h w v ∈ sortedSpan c h (n+energyHW w) := by
  induction w with
  | nil => simpa [vermaDescendant,energyHW] using hv
  | cons i w ih =>
    change vermaMode c h (-(i:ℤ)-1) _ ∈ _
    apply verma_mode_mem_level c h (n+energyHW w) _ _ ih
    simp only [energyHW_cons,Nat.cast_add,Nat.cast_one]
    omega

/-- Mode stability of the canonical radical extends to every negative word. -/
theorem vermaDescendant_radical (c h : ℂ) (w : List ℕ) (v : Verma c h)
    (hv : vermaContravariant c h v=0) :
    vermaContravariant c h (vermaDescendant c h w v)=0 := by
  induction w with
  | nil => exact hv
  | cons i w ih => exact vermaContravariant_radical_mode c h (-(i:ℤ)-1) _ ih

/-- The full partition-indexed descendant family at added level m, regarded
as states in the actual ambient level n+m. -/
noncomputable def vermaGradedDescendant (c h : ℂ) (n m : ℕ)
    (v : sortedSpan c h n) (w : VermaPartitions m) : sortedSpan c h (n+m) :=
  ⟨vermaDescendant c h w.val v, by
    simpa only [w.property.2] using vermaDescendant_mem_level c h w.val n v v.property⟩

/-- A nonzero starting state supplies one independent descendant for EVERY
partition of m, including parts one. This count is inside the actual module. -/
theorem vermaGradedDescendant_linearIndependent (c h : ℂ) (n m : ℕ)
    (v : sortedSpan c h n) (hv : v≠0) :
    LinearIndependent ℂ (vermaGradedDescendant c h n m v) := by
  let e : VermaPartitions m → {w : List ℕ // SortedWord w} := fun w => ⟨w.val,w.property.1⟩
  have he : Function.Injective e := by
    intro u w h
    exact Subtype.ext (congrArg (fun z : {w : List ℕ // SortedWord w} => z.val) h)
  have hv' : (v : Verma c h)≠0 := fun he => hv (Subtype.ext he)
  have hi := (vermaDescendant_linearIndependent c h v hv').comp e he
  exact LinearIndependent.of_comp (sortedSpan c h (n+m)).subtype hi

/-- At fixed charge the actual Gram matrix is polynomial in highest weight.
The central parameter is constant, while the highest weight is X. -/
noncomputable def vermaWeightGramPolynomial (c : ℂ) (n : ℕ) :
    Matrix (VermaPartitions n) (VermaPartitions n) (Polynomial ℂ) :=
  vermaAlgebraGramMatrix (Polynomial.C c) Polynomial.X n

/-- Evaluating the highest-weight polynomial gives the actual Verma form
matrix, with the normalization already proved by the universal construction. -/
theorem vermaWeightGramPolynomial_eval (c h : ℂ) (n : ℕ) :
    (vermaWeightGramPolynomial c n).map (Polynomial.eval h)=vermaGramMatrix c h n := by
  simpa [vermaWeightGramPolynomial] using
    vermaAlgebraGramMatrix_eval (Polynomial.C c) Polynomial.X (Polynomial.aeval h) n

/-- PBW coordinates of singular descendants are actual null rows of the
highest-weight polynomial Gram matrix, after evaluation at that weight. -/
theorem vermaGradedDescendant_null_row (c h : ℂ) (n m : ℕ) (hn : 0<n)
    (v : sortedSpan c h n) (h1 : vermaMode c h 1 (v : Verma c h)=0)
    (h2 : vermaMode c h 2 (v : Verma c h)=0)
    (i : VermaPartitions m) (j : VermaPartitions (n+m)) :
    ∑ k, (vermaLevelBasis c h (n+m)).equivFun (vermaGradedDescendant c h n m v i) k *
      (vermaWeightGramPolynomial c (n+m) k j).eval h=0 := by
  let b := vermaLevelBasis c h (n+m)
  have he : ∀ k, (vermaWeightGramPolynomial c (n+m) k j).eval h=
      vermaContravariant c h (b k : Verma c h) (b j : Verma c h) := by
    intro k
    have hh := congrArg (fun M => M k j) (vermaWeightGramPolynomial_eval c h (n+m))
    simpa only [Matrix.map_apply,vermaGramMatrix,b,vermaLevelBasis,
      Module.Basis.mk_apply,vermaLevelWord] using hh
  simp_rw [he]
  have hs := congrArg (sortedSpan c h (n+m)).subtype
    (b.sum_equivFun (vermaGradedDescendant c h n m v i))
  simp only [map_sum,map_smul] at hs
  have hh := congrArg (fun x => vermaContravariant c h x (b j : Verma c h)) hs
  have hz := LinearMap.congr_fun (vermaDescendant_radical c h i.val v
    (vermaContravariant_singular_radical c h n hn v v.property h1 h2)) (b j)
  simpa only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    smul_eq_mul,LinearMap.zero_apply] using hh.trans hz

/-- A nonzero positive-level singular state forces p(m) factors X-h in the
actual level-(n+m) determinant, where p counts ALL partitions. This is a
uniform proved lower bound, not a Kac factorization or a vacuum character. -/
theorem vermaWeightDeterminant_dvd_of_singular (c h : ℂ) (n m : ℕ)
    [DecidableEq (VermaPartitions (n+m))] (hn : 0<n)
    (v : sortedSpan c h n) (hv : v≠0)
    (h1 : vermaMode c h 1 (v : Verma c h)=0)
    (h2 : vermaMode c h 2 (v : Verma c h)=0) :
    (Polynomial.X-Polynomial.C h)^(Fintype.card (VermaPartitions m)) ∣
      (vermaWeightGramPolynomial c (n+m)).det := by
  classical
  have hi := (vermaGradedDescendant_linearIndependent c h n m v hv).map'
    (vermaLevelBasis c h (n+m)).equivFun.toLinearMap
    (LinearMap.ker_eq_bot.mpr (vermaLevelBasis c h (n+m)).equivFun.injective)
  exact VirDeformModes.NormalOrdering.pow_X_sub_C_dvd_det_of_independent_null_rows _ h _ hi
    (fun i j => vermaGradedDescendant_null_row c h n m hn v h1 h2 i j)

/-- The singular embedding commutes with every actual mode. -/
theorem vermaSingularMap_mode (c h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0)
    (r : ℤ) (u : Verma c (h+(n:ℂ))) :
    vermaSingularMap c h n v hv h1 h2 (vermaMode c (h+(n:ℂ)) r u)=
      vermaMode c h r (vermaSingularMap c h n v hv h1 h2 u) :=
  universalMap_intertwines _ _ _ _ _

/-- Relative level m in the embedded Verma module is EXACTLY ambient level
n+m. Injectivity and the L0 eigenvalue characterize this in both directions,
so the descendant count is the actual graded submodule dimension. -/
theorem vermaSingularMap_mem_level_iff (c h : ℂ) (n m : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hne : v≠0)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0)
    (u : Verma c (h+(n:ℂ))) :
    vermaSingularMap c h n v hv h1 h2 u ∈ sortedSpan c h (n+m) ↔
      u ∈ sortedSpan c (h+(n:ℂ)) m := by
  rw [verma_mem_level_iff_eigen,verma_mem_level_iff_eigen]
  have hs : h+((n+m:ℕ):ℂ)=(h+(n:ℂ))+(m:ℂ) := by push_cast; ring
  rw [hs,← vermaSingularMap_mode,← map_smul]
  exact (vermaSingularMap_injective c h n v hv hne h1 h2).eq_iff

/-- Each level of the actual embedded singular Verma submodule has the full
partition dimension. This is an exact submodule count, not an irreducible
quotient character or a claim about intersections of different submodules. -/
theorem vermaSingularMap_level_finrank (c h : ℂ) (n m : ℕ) (v : Verma c h)
    (hv : v ∈ sortedSpan c h n) (hne : v≠0)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0) :
    Module.finrank ℂ ((sortedSpan c (h+(n:ℂ)) m).map
      (vermaSingularMap c h n v hv h1 h2))=Fintype.card (VermaPartitions m) := by
  rw [← (Submodule.equivMapOfInjective _
    (vermaSingularMap_injective c h n v hv hne h1 h2)
    (sortedSpan c (h+(n:ℂ)) m)).finrank_eq]
  exact vermaLevel_finrank _ _ _

/-- The constructed nonzero BSA singular family gives actual
highest-weight determinant factors at EVERY later level, of multiplicity
at least the full partition count. This has no singular-existence input;
it covers the (1,N) curve, not all Kac labels. -/
theorem vermaWeightDeterminant_bsa_factor (t : ℂ) (N m : ℕ)
    [DecidableEq (VermaPartitions (N+m))] (ht : t≠0) (hN : 3≤N) :
    (Polynomial.X-Polynomial.C (vermaBSAWeight N t))^(Fintype.card (VermaPartitions m)) ∣
      (vermaWeightGramPolynomial (vermaBSACharge t) (N+m)).det := by
  obtain ⟨v,hv,hlev,hhigh⟩ := vermaBSA_nonzero_highest t N ht hN
  exact vermaWeightDeterminant_dvd_of_singular _ _ N m (by omega) ⟨v,hlev⟩
    (fun he => hv (congrArg Subtype.val he))
    (hhigh.pos_annihilate 1 (by norm_num)) (hhigh.pos_annihilate 2 (by norm_num))

end VOA.InverseDS.VirasoroVerma
