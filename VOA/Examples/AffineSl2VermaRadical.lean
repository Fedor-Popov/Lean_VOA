/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2VermaDescendants

/-!
# Actual joint Gram kernels and the full contravariant radical

Different joint eigenspaces are orthogonal. Consequently a kernel of one
finite actual Gram block is a vector of the entire canonical radical,
not merely a vector invisible to a selected list of tests. The already
proved screening roots therefore give genuine nonzero radical vectors.
-/
namespace VOA.AffineVOA.HighestModule
open Module (End)
open Wak.Charged (Occupation JointIndex occupationEnergy occupationCharge)
noncomputable section
local instance (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := Wak.Charged.jointIndexFintype n c
local instance (n : ℕ) (c : ℤ) : DecidableEq (JointIndex n c) := Classical.decEq _

/-- Different degree/Cartan joint eigenspaces are orthogonal in the actual
form. The assertion is valid at every complex level and highest weight. -/
theorem joint_orthogonal (k h : ℂ) (n m : ℕ) (c d : ℤ) (u v : Verma k h)
    (hu : u∈jointSpace k h n c) (hv : v∈jointSpace k h m d)
    (hne : n≠m ∨ c≠d) : contravariant k h u v=0 := by
  have heu := (mem_jointSpace_iff k h n c u).mp hu
  have hev := (mem_jointSpace_iff k h m d v).mp hv
  rcases hne with hn|hc
  · have he := contravariant_degree_adj k h u v
    rw [heu.1,hev.1,map_smul,LinearMap.smul_apply,map_smul,smul_eq_mul,smul_eq_mul] at he
    have hz : (n : ℂ)-(m : ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    apply (mul_eq_zero.mp (show ((n : ℂ)-(m : ℂ))*contravariant k h u v=0 by linear_combination -he)).resolve_left hz
  · have he := contravariant_adj k h 2 0 u v
    have ha : adjointColour 2=2 := rfl
    rw [ha,neg_zero,heu.2,hev.2,map_smul,LinearMap.smul_apply,map_smul,smul_eq_mul,smul_eq_mul] at he
    have hz : (c : ℂ)-(d : ℂ)≠0 := sub_ne_zero.mpr (by exact_mod_cast hc)
    apply (mul_eq_zero.mp (show ((c : ℂ)-(d : ℂ))*contravariant k h u v=0 by linear_combination (1/2 : ℂ)*he)).resolve_left hz

/-- The actual finite state with prescribed joint PBW coordinates. -/
def jointState (k h : ℂ) (n : ℕ) (c : ℤ) (a : JointIndex n c→ℂ) : Verma k h :=
  ∑ i,a i • occupationBasis k h i.val

/-- The finite coordinate state lies in the intended actual joint space. -/
theorem jointState_mem (k h : ℂ) (n : ℕ) (c : ℤ) (a : JointIndex n c→ℂ) :
    jointState k h n c a∈jointSpace k h n c := by
  apply Submodule.sum_mem
  intro i hi
  exact (jointSpace k h n c).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)

/-- Zero state means zero coordinates, by the actual Verma basis. -/
theorem jointState_eq_zero_iff (k h : ℂ) (n : ℕ) (c : ℤ) (a : JointIndex n c→ℂ) :
    jointState k h n c a=0 ↔ a=0 := by
  constructor
  · intro he
    exact funext ((Fintype.linearIndependent_iff.mp (jointWords_independent k h n c)) a he)
  · rintro rfl
    simp [jointState]

/-- Gram multiplication is actual pairing with the finite coordinate state. -/
theorem gramMatrix_mulVec (k h : ℂ) (n : ℕ) (c : ℤ) (a : JointIndex n c→ℂ) (i : JointIndex n c) :
    (gramMatrix k h n c).mulVec a i=
      contravariant k h (occupationBasis k h i.val) (jointState k h n c a) := by
  simp only [Matrix.mulVec, dotProduct,gramMatrix,jointState,map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- A finite block kernel is exactly a vector in the FULL actual radical;
all tests outside that joint block vanish by proved orthogonality. -/
theorem gramMatrix_kernel_iff_radical (k h : ℂ) (n : ℕ) (c : ℤ) (a : JointIndex n c→ℂ) :
    (gramMatrix k h n c).mulVec a=0 ↔ contravariant k h (jointState k h n c a)=0 := by
  constructor
  · intro ha
    apply (occupationBasis k h).ext
    intro e
    change contravariant k h (jointState k h n c a) (occupationBasis k h e)=0
    by_cases he : occupationEnergy e=n ∧ occupationCharge e=c
    · have hh := congrFun ha (⟨e,he⟩ : JointIndex n c)
      rw [gramMatrix_mulVec,contravariant_symm] at hh
      exact hh
    · apply joint_orthogonal k h n (occupationEnergy e) c (occupationCharge e) _ _ (jointState_mem k h n c a)
      · exact Submodule.subset_span ⟨⟨e,rfl,rfl⟩,rfl⟩
      · rcases not_and_or.mp he with hn|hc
        · exact Or.inl (Ne.symm hn)
        · exact Or.inr (Ne.symm hc)
  · intro hv
    funext i
    rw [gramMatrix_mulVec,contravariant_symm,hv]
    rfl

/-- Any actual joint determinant root supplies a NONZERO vector in the
entire canonical Verma radical, with no earlier nondegeneracy assumption. -/
theorem nonzero_radical_of_gram_root (k h : ℂ) (n : ℕ) (c : ℤ)
    (hroot : (gramMatrix k h n c).det=0) :
    ∃ v : Verma k h,v≠0 ∧ v∈jointSpace k h n c ∧ contravariant k h v=0 := by
  obtain ⟨a,hne,ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨jointState k h n c a,?_,jointState_mem k h n c a,(gramMatrix_kernel_iff_radical k h n c a).mp ha⟩
  intro hv
  exact hne ((jointState_eq_zero_iff k h n c a).mp hv)

/-- EVERY positive real-root Kac line has an ACTUAL nonzero radical vector
at its root joint label. This uses the proved integer screenings and
interpolation, not a determinant-factor or singular-existence hypothesis. -/
theorem kac_positive_nonzero_radical (r q : ℕ) (hr : 0<r) (hq : 0<q) (t : ℂ) :
    ∃ v : Verma (t-2) ((q : ℂ)*t-r-1),v≠0 ∧
      v∈jointSpace (t-2) ((q : ℂ)*t-r-1) (r*q) (r : ℤ) ∧
      contravariant (t-2) ((q : ℂ)*t-r-1) v=0 := by
  apply nonzero_radical_of_gram_root
  rw [← highestDeterminant_verma]
  exact Wak.Charged.highestDeterminant_kac_root r q hr hq t

/-- The opposite real-root family likewise has actual nonzero radical
vectors, including the horizontal q=0 branch. -/
theorem kac_negative_nonzero_radical (r q : ℕ) (hr : 0<r) (t : ℂ) :
    ∃ v : Verma (t-2) ((r : ℂ)-1-q*t),v≠0 ∧
      v∈jointSpace (t-2) ((r : ℂ)-1-q*t) (r*q) (-(r : ℤ)) ∧
      contravariant (t-2) ((r : ℂ)-1-q*t) v=0 := by
  apply nonzero_radical_of_gram_root
  rw [← highestDeterminant_verma]
  exact Wak.Charged.highestDeterminant_opposite_kac_root r q hr t

end
end VOA.AffineVOA.HighestModule
