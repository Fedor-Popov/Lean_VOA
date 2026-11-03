/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VacuumJointSequence
import Mathlib.LinearAlgebra.Basis.Prod

/-!
# An actual joint basis adapted to the horizontal submodule

Explicit vacuum PBW lifts and the embedded weight-minus-two PBW vectors
form a basis of the weight-zero Verma joint space. The proof uses the actual
exact sequence and its grading, not a presumed character identity.
-/
namespace VOA.AffineVOA.HighestModule
open Wak.Charged (Occupation)
noncomputable section
local instance vacuumBasisVermaFintype (n : ℕ) (c : ℤ) : Fintype (Wak.Charged.JointIndex n c) :=
  Wak.Charged.jointIndexFintype n c

/-- The actual horizontal embedding restricted to the exact finite joint spaces. -/
def horizontalJointEmbedding (k : ℂ) (n : ℕ) (c : ℤ) :
    jointSpace k (-2) n (c+1)→ₗ[ℂ]jointSpace k 0 n c :=
  ((horizontalEmbedding k).comp (jointSpace k (-2) n (c+1)).subtype).codRestrict _
    (fun v => (horizontalEmbedding_mem_joint_iff k n c v).mpr v.property)

/-- The restricted embedding is still injective. -/
theorem horizontalJointEmbedding_injective (k : ℂ) (n : ℕ) (c : ℤ) :
    Function.Injective (horizontalJointEmbedding k n c) := by
  intro v w he
  apply Subtype.ext
  exact horizontalEmbedding_injective k (congrArg Subtype.val he)

/-- The actual vacuum projection restricted to one joint energy/charge. -/
def vacuumJointProjection (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    jointSpace k 0 n c→ₗ[ℂ]AffineSl2GeneralRigidity.jointSpace k hk (n : ℤ) (2*c) :=
  ((vacuumProjection k).comp (jointSpace k 0 n c).subtype).codRestrict _
    (fun v => vacuumProjection_mem_joint k hk n c v v.property)

/-- A chosen linear section defined by the literal fixed vacuum PBW lifts. -/
def vacuumJointSection (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    AffineSl2GeneralRigidity.jointSpace k hk (n : ℤ) (2*c)→ₗ[ℂ]jointSpace k 0 n c :=
  (AffineSl2GeneralRigidity.jointBasis k hk (n : ℤ) (2*c)).constr ℂ
    (fun i => ⟨indexedWord k 0 (vacuumLiftWord i.val),vacuumLift_mem_joint k 0 n c i⟩)

/-- On a vacuum basis vector the section is exactly its explicit creation lift. -/
theorem vacuumJointSection_basis (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i : AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) :
    (vacuumJointSection k hk n c
      (AffineSl2GeneralRigidity.jointBasis k hk (n : ℤ) (2*c) i) : Verma k 0)=
      indexedWord k 0 (vacuumLiftWord i.val) := by
  rw [vacuumJointSection,Module.Basis.constr_basis]

/-- Projection after this section is the identity on the actual vacuum joint space. -/
theorem vacuumJointProjection_section (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (vacuumJointProjection k hk n c).comp (vacuumJointSection k hk n c)=LinearMap.id := by
  apply (AffineSl2GeneralRigidity.jointBasis k hk (n : ℤ) (2*c)).ext
  intro i
  apply Subtype.ext
  change vacuumProjection k (vacuumJointSection k hk n c
    (AffineSl2GeneralRigidity.jointBasis k hk (n : ℤ) (2*c) i))=_
  rw [vacuumJointSection_basis,vacuumProjection_lift k hk]
  exact (AffineSl2GeneralRigidity.jointBasis_apply k hk _ _ i).symm

/-- Every joint vacuum vector has a lift in exactly the same Verma joint space. -/
theorem vacuumJointProjection_surjective (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    Function.Surjective (vacuumJointProjection k hk n c) := by
  intro v
  exact ⟨vacuumJointSection k hk n c v,LinearMap.congr_fun (vacuumJointProjection_section k hk n c) v⟩

/-- The restricted sequence is exact; its kernel consists of precisely the
shifted joint space in the horizontal singular module. -/
theorem vacuumJointProjection_ker (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    LinearMap.ker (vacuumJointProjection k hk n c)=
      LinearMap.range (horizontalJointEmbedding k n c) := by
  apply le_antisymm
  · intro v hv
    have hz : vacuumProjection k v=0 := congrArg Subtype.val hv
    have hm : (v : Verma k 0)∈LinearMap.ker (vacuumProjection k) := hz
    rw [vacuumProjection_ker] at hm
    obtain ⟨u,hu⟩ := hm
    have hg : u∈jointSpace k (-2) n (c+1) :=
      (horizontalEmbedding_mem_joint_iff k n c u).mp (hu.symm ▸ v.property)
    exact ⟨⟨u,hg⟩,Subtype.ext hu⟩
  · rintro v ⟨u,rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun (vacuumProjection_horizontalEmbedding k) u

/-- Sum the explicit vacuum lift and an embedded singular descendant. -/
def vacuumJointSplit (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    (AffineSl2GeneralRigidity.jointSpace k hk (n : ℤ) (2*c) × jointSpace k (-2) n (c+1))→ₗ[ℂ]
      jointSpace k 0 n c :=
  (vacuumJointSection k hk n c).coprod (horizontalJointEmbedding k n c)

/-- The explicit split map is bijective, using exactness and the proved
injectivity of the actual horizontal singular embedding. -/
theorem vacuumJointSplit_bijective (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    Function.Bijective (vacuumJointSplit k hk n c) := by
  have hz (u : jointSpace k (-2) n (c+1)) :
      vacuumJointProjection k hk n c (horizontalJointEmbedding k n c u)=0 := by
    have hm : horizontalJointEmbedding k n c u∈LinearMap.ker (vacuumJointProjection k hk n c) := by
      rw [vacuumJointProjection_ker]
      exact ⟨u,rfl⟩
    exact hm
  have hs (v : AffineSl2GeneralRigidity.jointSpace k hk (n : ℤ) (2*c)) :
      vacuumJointProjection k hk n c (vacuumJointSection k hk n c v)=v :=
    LinearMap.congr_fun (vacuumJointProjection_section k hk n c) v
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot.mpr
    intro a b he
    have hf := congrArg (vacuumJointProjection k hk n c) he
    change vacuumJointProjection k hk n c (vacuumJointSection k hk n c a.1+
      horizontalJointEmbedding k n c a.2)=
      vacuumJointProjection k hk n c (vacuumJointSection k hk n c b.1+
        horizontalJointEmbedding k n c b.2) at hf
    simp only [map_add,hz,hs,add_zero] at hf
    apply Prod.ext hf
    apply horizontalJointEmbedding_injective k n c
    change vacuumJointSection k hk n c a.1+horizontalJointEmbedding k n c a.2=
      vacuumJointSection k hk n c b.1+horizontalJointEmbedding k n c b.2 at he
    rw [hf] at he
    exact add_left_cancel he
  · intro v
    let a := vacuumJointProjection k hk n c v
    have hm : v-vacuumJointSection k hk n c a∈LinearMap.ker (vacuumJointProjection k hk n c) := by
      change vacuumJointProjection k hk n c (v-vacuumJointSection k hk n c a)=0
      rw [map_sub,hs]
      exact sub_self _
    rw [vacuumJointProjection_ker] at hm
    obtain ⟨b,hb⟩ := hm
    refine ⟨(a,b),?_⟩
    change vacuumJointSection k hk n c a+horizontalJointEmbedding k n c b=v
    rw [hb]
    abel

/-- Indexing separates ordinary vacuum words from horizontal descendants. -/
abbrev VacuumAdaptedIndex (n : ℕ) (c : ℤ) :=
  AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c) ⊕ Wak.Charged.JointIndex n (c+1)

/-- The actual basis of the joint Verma space adapted to its vacuum quotient. -/
def vacuumAdaptedBasis (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ) :
    Module.Basis (VacuumAdaptedIndex n c) ℂ (jointSpace k 0 n c) :=
  ((AffineSl2GeneralRigidity.jointBasis k hk (n : ℤ) (2*c)).prod (jointBasis k (-2) n (c+1))).map
    (LinearEquiv.ofBijective (vacuumJointSplit k hk n c) (vacuumJointSplit_bijective k hk n c))

/-- Vacuum indices of the adapted basis are the fixed creation lifts. -/
theorem vacuumAdaptedBasis_left (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i : AffineSl2GeneralRigidity.JointIndex (n : ℤ) (2*c)) :
    (vacuumAdaptedBasis k hk n c (Sum.inl i) : Verma k 0)=indexedWord k 0 (vacuumLiftWord i.val) := by
  simp [vacuumAdaptedBasis,Module.Basis.prod_apply,vacuumJointSplit,
    vacuumJointSection_basis]

/-- Singular indices of the adapted basis are the literal embedded PBW descendants. -/
theorem vacuumAdaptedBasis_right (k : ℂ) (hk : k+2≠0) (n : ℕ) (c : ℤ)
    (i : Wak.Charged.JointIndex n (c+1)) :
    (vacuumAdaptedBasis k hk n c (Sum.inr i) : Verma k 0)=
      horizontalEmbedding k (occupationBasis k (-2) i.val) := by
  simp [vacuumAdaptedBasis,Module.Basis.prod_apply,vacuumJointSplit,
    horizontalJointEmbedding,jointBasis_apply]

end
end VOA.AffineVOA.HighestModule
