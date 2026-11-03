/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2ParabolicJoint
import VOA.Examples.AffineSl2VacuumAdaptedFamily

/-! # Constant adapted bases for actual finite parabolic weight spaces -/
namespace VOA.AffineVOA.HighestModule
open Wak.Charged (JointIndex Occupation occupationWord)
noncomputable section
local instance parabolicAdaptedIndexFintype (N : ℕ) (c : ℤ) : Fintype (JointIndex N c) := Wak.Charged.jointIndexFintype N c
local instance parabolicAdaptedJointFinite (k h : ℂ) (N : ℕ) (c : ℤ) : Module.Finite ℂ (jointSpace k h N c) :=
  Module.Finite.of_basis (jointBasis k h N c)

/-- Projection onto its actual finite joint image. -/
def parabolicJointProjection (k : ℂ) (d N : ℕ) (c : ℤ) :
    jointSpace k d N c →ₗ[ℂ] parabolicJointSpace k d N c :=
  ((parabolicProjection k d).comp (jointSpace k d N c).subtype).codRestrict _
    (fun x => ⟨x.1,x.2,rfl⟩)

theorem parabolicJointProjection_surjective (k : ℂ) (d N : ℕ) (c : ℤ) :
    Function.Surjective (parabolicJointProjection k d N c) := by
  rintro ⟨y,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

instance parabolicJointSpace_finite (k : ℂ) (d N : ℕ) (c : ℤ) :
    Module.Finite ℂ (parabolicJointSpace k d N c) :=
  Module.Finite.of_surjective (parabolicJointProjection k d N c)
    (parabolicJointProjection_surjective k d N c)

/-- A linear section of the actual finite-dimensional projection. -/
def parabolicJointSection (k : ℂ) (d N : ℕ) (c : ℤ) :
    parabolicJointSpace k d N c →ₗ[ℂ] jointSpace k d N c :=
  Classical.choose ((parabolicJointProjection k d N c).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (parabolicJointProjection_surjective k d N c)))

theorem parabolicJointProjection_section (k : ℂ) (d N : ℕ) (c : ℤ) :
    (parabolicJointProjection k d N c).comp (parabolicJointSection k d N c) = LinearMap.id :=
  Classical.choose_spec ((parabolicJointProjection k d N c).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (parabolicJointProjection_surjective k d N c)))

theorem parabolicJointProjection_ker (k : ℂ) (d N : ℕ) (c : ℤ) :
    LinearMap.ker (parabolicJointProjection k d N c) =
      LinearMap.range (horizontalReflectionJoint k d N c) := by
  apply le_antisymm
  · intro x hx
    have hx' : x.1 ∈ LinearMap.ker (parabolicProjection k d) := congrArg Subtype.val hx
    rw [← horizontalReflection_range_eq_kernel] at hx'
    obtain ⟨y,hy⟩ := hx'
    have hy' : y ∈ jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1) :=
      (horizontalReflection_joint_iff k d N c y).mp (hy ▸ x.2)
    exact ⟨⟨y,hy'⟩,Subtype.ext hy⟩
  · rintro x ⟨y,rfl⟩
    apply Subtype.ext
    change parabolicProjection k d (horizontalReflection k d y.1) = 0
    exact (LinearMap.mem_ker.mp ((horizontalReflection_range_eq_kernel k d) ▸
      (show horizontalReflection k d y.1 ∈ LinearMap.range (horizontalReflection k d) from ⟨y.1,rfl⟩)))

/-- The finite parabolic quotient and the reflected Verma space split the actual joint space. -/
def parabolicJointSplit (k : ℂ) (d N : ℕ) (c : ℤ) :
    (parabolicJointSpace k d N c × jointSpace k (-(d : ℂ)-2) N (c+(d : ℤ)+1)) →ₗ[ℂ]
      jointSpace k d N c :=
  (parabolicJointSection k d N c).coprod (horizontalReflectionJoint k d N c)

theorem parabolicJointSplit_bijective (k : ℂ) (d n : ℕ) (c : ℤ) :
    Function.Bijective (parabolicJointSplit k d n c) := by
  have hz (u : jointSpace k (-(d : ℂ)-2) n (c+(d : ℤ)+1)) :
      parabolicJointProjection k d n c (horizontalReflectionJoint k d n c u)=0 := by
    have hm : horizontalReflectionJoint k d n c u∈LinearMap.ker (parabolicJointProjection k d n c) := by
      rw [parabolicJointProjection_ker]
      exact ⟨u,rfl⟩
    exact hm
  have hs (v : parabolicJointSpace k d n c) :
      parabolicJointProjection k d n c (parabolicJointSection k d n c v)=v :=
    LinearMap.congr_fun (parabolicJointProjection_section k d n c) v
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot.mpr
    intro a b he
    have hf := congrArg (parabolicJointProjection k d n c) he
    change parabolicJointProjection k d n c (parabolicJointSection k d n c a.1+
      horizontalReflectionJoint k d n c a.2)=
      parabolicJointProjection k d n c (parabolicJointSection k d n c b.1+
        horizontalReflectionJoint k d n c b.2) at hf
    simp only [map_add,hz,hs,add_zero] at hf
    apply Prod.ext hf
    apply horizontalReflectionJoint_injective k d n c
    change parabolicJointSection k d n c a.1+horizontalReflectionJoint k d n c a.2=
      parabolicJointSection k d n c b.1+horizontalReflectionJoint k d n c b.2 at he
    rw [hf] at he
    exact add_left_cancel he
  · intro v
    let a := parabolicJointProjection k d n c v
    have hm : v-parabolicJointSection k d n c a∈LinearMap.ker (parabolicJointProjection k d n c) := by
      change parabolicJointProjection k d n c (v-parabolicJointSection k d n c a)=0
      rw [map_sub,hs]
      exact sub_self _
    rw [parabolicJointProjection_ker] at hm
    obtain ⟨b,hb⟩ := hm
    refine ⟨(a,b),?_⟩
    change parabolicJointSection k d n c a+horizontalReflectionJoint k d n c b=v
    rw [hb]
    abel


/-- The complement size is the dimension of the actual quotient at the reference level. -/
abbrev ParabolicAdaptedIndex (d N : ℕ) (c : ℤ) :=
  Fin (Module.finrank ℂ (parabolicJointSpace 1 d N c)) ⊕ JointIndex N (c+(d : ℤ)+1)

local instance parabolicAdaptedMatrixDecidable (d N : ℕ) (c : ℤ) :
    DecidableEq (ParabolicAdaptedIndex d N c) := Classical.decEq _

/-- A basis at the reference level, with its right block the literal singular descendants. -/
def parabolicReferenceBasis (d N : ℕ) (c : ℤ) :
    Module.Basis (ParabolicAdaptedIndex d N c) ℂ (jointSpace 1 d N c) :=
  ((Module.finBasis ℂ (parabolicJointSpace 1 d N c)).prod
    (jointBasis 1 (-(d : ℂ)-2) N (c+(d : ℤ)+1))).map
    (LinearEquiv.ofBijective (parabolicJointSplit 1 d N c)
      (parabolicJointSplit_bijective 1 d N c))

/-- The reference right block is the actual reflection of the canonical PBW basis. -/
theorem parabolicReferenceBasis_right (d N : ℕ) (c : ℤ)
    (i : JointIndex N (c+(d : ℤ)+1)) :
    (parabolicReferenceBasis d N c (Sum.inr i) : Verma 1 d) =
      horizontalReflection 1 d (occupationBasis 1 (-(d : ℂ)-2) i.val) := by
  simp [parabolicReferenceBasis,Module.Basis.prod_apply,parabolicJointSplit,
    horizontalReflectionJoint,jointBasis_apply]

/-- Transport the one reference basis to every level and highest weight by fixed PBW coordinates. -/
def parabolicAdaptedFamilyBasis (k h : ℂ) (d N : ℕ) (c : ℤ) :
    Module.Basis (ParabolicAdaptedIndex d N c) ℂ (jointSpace k h N c) :=
  (parabolicReferenceBasis d N c).map (jointCoordinateTransport 1 d k h N c)

/-- A reflected basis vector is its fixed occupation word followed by the horizontal relation. -/
theorem horizontalReflection_basis_word (k : ℂ) (d : ℕ) (i : Occupation) :
    horizontalReflection k d (occupationBasis k (-(d : ℂ)-2) i) =
      indexedWord k d (i.toMultiset.toList ++ List.replicate (d+1) (1,0)) := by
  rw [occupationBasis_apply,horizontalReflection,universalMap_word]
  simp only [indexedWord,List.map_append,List.map_replicate,Wak.Charged.lowerLetter,
    if_pos rfl,Int.cast_zero,neg_zero,NormalOrdering.currentWord_append]
  rfl

/-- The right block remains the same literal descendant word at all two-parameter values. -/
theorem parabolicAdaptedFamilyBasis_right (k h : ℂ) (d N : ℕ) (c : ℤ)
    (i : JointIndex N (c+(d : ℤ)+1)) :
    (parabolicAdaptedFamilyBasis k h d N c (Sum.inr i) : Verma k h) =
      indexedWord k h (i.val.toMultiset.toList ++ List.replicate (d+1) (1,0)) := by
  rw [parabolicAdaptedFamilyBasis,Module.Basis.map_apply,jointCoordinateTransport_coe,
    parabolicReferenceBasis_right,horizontalReflection_basis_word,vermaCoordinateTransport_word]

/-- The exact cardinality identity supplies one fixed finite reindexing. -/
def parabolicAdaptedIndexEquiv (d N : ℕ) (c : ℤ) :
    JointIndex N c ≃ ParabolicAdaptedIndex d N c :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum,Fintype.card_fin] using
      (parabolicJointSpace_finrank_add 1 d N c).symm)

/-- The original PBW basis reindexed by the actual quotient and kernel dimensions. -/
def parabolicReindexedBasis (k h : ℂ) (d N : ℕ) (c : ℤ) :
    Module.Basis (ParabolicAdaptedIndex d N c) ℂ (jointSpace k h N c) :=
  (jointBasis k h N c).reindex (parabolicAdaptedIndexEquiv d N c)

theorem parabolicReindexedBasis_transport (k h : ℂ) (d N : ℕ) (c : ℤ) :
    parabolicReindexedBasis k h d N c =
      (parabolicReindexedBasis 1 d d N c).map (jointCoordinateTransport 1 d k h N c) := by
  ext i
  simp only [parabolicReindexedBasis,Module.Basis.map_apply,Module.Basis.reindex_apply]
  change (jointBasis k h N c ((parabolicAdaptedIndexEquiv d N c).symm i) : Verma k h) =
    (((jointBasis 1 d N c).equiv (jointBasis k h N c) (Equiv.refl _))
      (jointBasis 1 d N c ((parabolicAdaptedIndexEquiv d N c).symm i)) : Verma k h)
  rw [Module.Basis.equiv_apply]
  rfl

/-- This basis-change matrix has constant coefficients, independent of level and highest weight. -/
def parabolicBasisChange (d N : ℕ) (c : ℤ) :
    Matrix (ParabolicAdaptedIndex d N c) (ParabolicAdaptedIndex d N c) ℂ :=
  (parabolicReindexedBasis 1 d d N c).toMatrix (parabolicReferenceBasis d N c)

theorem parabolicBasisChange_eq (k h : ℂ) (d N : ℕ) (c : ℤ) :
    (parabolicReindexedBasis k h d N c).toMatrix (parabolicAdaptedFamilyBasis k h d N c) =
      parabolicBasisChange d N c := by
  rw [parabolicReindexedBasis_transport,Module.Basis.toMatrix_map]
  have he : (jointCoordinateTransport 1 d k h N c).symm ∘ parabolicAdaptedFamilyBasis k h d N c =
      parabolicReferenceBasis d N c := by
    funext i
    exact (jointCoordinateTransport 1 d k h N c).symm_apply_apply _
  rw [he]
  rfl

theorem parabolicBasisChange_det_ne_zero (d N : ℕ) (c : ℤ) :
    (parabolicBasisChange d N c).det ≠ 0 := by
  classical
  have he := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip
    (parabolicReindexedBasis 1 d d N c) (parabolicReferenceBasis d N c))
  rw [Matrix.det_mul,Matrix.det_one] at he
  intro hz
  change (parabolicBasisChange d N c).det * _ = 1 at he
  rw [hz,zero_mul] at he
  exact zero_ne_one he

/-- The transported right block vanishes in the actual parabolic quotient. -/
theorem parabolicJointProjection_right (k : ℂ) (d N : ℕ) (c : ℤ)
    (i : JointIndex N (c+(d : ℤ)+1)) :
    parabolicJointProjection k d N c (parabolicAdaptedFamilyBasis k d d N c (Sum.inr i)) = 0 := by
  apply Subtype.ext
  change parabolicProjection k d (parabolicAdaptedFamilyBasis k d d N c (Sum.inr i)) = 0
  rw [parabolicAdaptedFamilyBasis_right,← horizontalReflection_basis_word]
  exact (LinearMap.mem_ker.mp ((horizontalReflection_range_eq_kernel k d) ▸
    (show horizontalReflection k d (occupationBasis k (-(d : ℂ)-2) i.val) ∈
      LinearMap.range (horizontalReflection k d) from ⟨_,rfl⟩)))

/-- The projected left block spans the literal parabolic joint image. -/
theorem parabolicQuotientLeft_spans (k : ℂ) (d N : ℕ) (c : ℤ) :
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i : Fin (Module.finrank ℂ (parabolicJointSpace 1 d N c)) =>
      parabolicJointProjection k d N c (parabolicAdaptedFamilyBasis k d d N c (Sum.inl i)))) := by
  intro y hy
  clear hy
  obtain ⟨x,rfl⟩ := parabolicJointProjection_surjective k d N c y
  have hx : x ∈ Submodule.span ℂ (Set.range (parabolicAdaptedFamilyBasis k d d N c)) := by
    rw [Module.Basis.span_eq]
    trivial
  induction hx using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,rfl⟩ := hv
    cases i with
    | inl i => exact Submodule.subset_span ⟨i,rfl⟩
    | inr i => rw [parabolicJointProjection_right]; exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
  | smul z u hu ihu => rw [map_smul]; exact Submodule.smul_mem _ z ihu

/-- Actual finite parabolic dimensions are independent of the level. -/
theorem parabolicJointSpace_finrank_level (k k' : ℂ) (d N : ℕ) (c : ℤ) :
    Module.finrank ℂ (parabolicJointSpace k d N c) =
      Module.finrank ℂ (parabolicJointSpace k' d N c) := by
  have h := parabolicJointSpace_finrank_add k d N c
  have h' := parabolicJointSpace_finrank_add k' d N c
  omega

/-- The actual quotient basis is exactly the projected left block of the fixed adapted family. -/
def parabolicQuotientBasis (k : ℂ) (d N : ℕ) (c : ℤ) :
    Module.Basis (Fin (Module.finrank ℂ (parabolicJointSpace 1 d N c))) ℂ
      (parabolicJointSpace k d N c) :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun i => parabolicJointProjection k d N c (parabolicAdaptedFamilyBasis k d d N c (Sum.inl i)))
    (parabolicQuotientLeft_spans k d N c)
    (by rw [Fintype.card_fin]; exact parabolicJointSpace_finrank_level 1 k d N c)

@[simp] theorem parabolicQuotientBasis_apply (k : ℂ) (d N : ℕ) (c : ℤ)
    (i : Fin (Module.finrank ℂ (parabolicJointSpace 1 d N c))) :
    parabolicQuotientBasis k d N c i =
      parabolicJointProjection k d N c (parabolicAdaptedFamilyBasis k d d N c (Sum.inl i)) := by
  simp [parabolicQuotientBasis]

end
end VOA.AffineVOA.HighestModule
