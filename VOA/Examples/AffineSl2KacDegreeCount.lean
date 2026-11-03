/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2OccupationThresholds

/-!
# Finite real-root degree count for affine Verma determinants

Summing charged oscillator multiplicities counts the exact highest-weight
degree. Removing positive numbers of copies turns this into the full joint
descendant multiplicities attached to real roots. Principal weight provides
finite bounds even for the horizontal zero-energy lowering root.
-/
namespace VOA.Wak.Charged
open scoped BigOperators
noncomputable section
local instance rootCountFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- Root colours have count one; neutral Cartan colour has count zero. -/
def rootCountWeight (v : Fin 3×ℕ) : ℕ := if v.1=2 then 0 else 1

/-- Root-letter count of a literal affine word. -/
def rootLetterCount : List (Fin 3×ℤ)→ℕ
  | [] => 0
  | an::w => (if an.1=2 then 0 else 1)+rootLetterCount w

/-- Each charged creation letter contributes either in the creation word
or in its adjoint, and a neutral letter contributes in neither. -/
theorem adjoint_loweringCount_add (w : List (Fin 3×ℤ)) :
    loweringCount (adjointWord w)+loweringCount w=rootLetterCount w := by
  induction w with
  | nil => simp [adjointWord,loweringCount,rootLetterCount]
  | cons an w ih =>
    simp only [adjointWord,List.reverse_cons,List.map_append,List.map_singleton,
      loweringCount_append,loweringCount,rootLetterCount] at *
    rcases an with ⟨a,m⟩
    fin_cases a <;> norm_num [adjointLetter,Fin.ext_iff] at * <;> omega

/-- The literal root count is an ordinary sum of its colour weights. -/
theorem rootLetterCount_sum (w : List (Fin 3×ℤ)) :
    rootLetterCount w=(w.map (fun an => if an.1=2 then 0 else 1)).sum := by
  induction w with
  | nil => rfl
  | cons an w ih => simp only [rootLetterCount,List.map_cons,List.sum_cons,ih]

/-- Actual occupation root multiplicity agrees with the charged word count. -/
theorem occupation_rootLetterCount (d : Occupation) :
    rootLetterCount (occupationWord d)=Finsupp.weight rootCountWeight d := by
  rw [rootLetterCount_sum,occupationWord,List.map_map]
  exact occupation_list_weight rootCountWeight d

/-- Finite oscillator box forced by the joint principal weight. -/
def jointModeBox (n : ℕ) (c : ℤ) : Finset (Fin 3×ℕ) :=
  Finset.univ.product (Finset.range ((2*(n : ℤ)-c).toNat+1))

/-- The root-colour part of the forced oscillator box. -/
def realRootModes (n : ℕ) (c : ℤ) : Finset (Fin 3×ℕ) :=
  (jointModeBox n c).filter (fun v => v.1≠2)

/-- Every occupied oscillator lies inside this finite box, including bosons. -/
theorem jointIndex_support_box (n : ℕ) (c : ℤ) (d : JointIndex n c) :
    d.val.support⊆jointModeBox n c := by
  intro v hv
  have hb := principalIndex_support _ ⟨d.val,jointIndex_principal n c d⟩ v (Finsupp.mem_support_iff.mp hv)
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩

/-- Summing the multiplicities over the finite root box gives exactly the
charged occupation weight; neutral and absent oscillators contribute zero. -/
theorem jointIndex_root_count (n : ℕ) (c : ℤ) (d : JointIndex n c) :
    Finsupp.weight rootCountWeight d.val=∑ v∈realRootModes n c,d.val v := by
  change d.val.sum (fun v a => a • rootCountWeight v)=_
  rw [Finsupp.sum_of_support_subset d.val (jointIndex_support_box n c d)]
  · rw [realRootModes,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hh : v.1=2 <;> simp [rootCountWeight,hh]
  · intro v hv; simp

/-- Exact finite real-root count for the actual highest-weight degree. The
multiplicity index r+1 includes horizontal lowering when its mode has energy zero. -/
theorem joint_root_degree_count (n : ℕ) (c : ℤ) :
    rowDegree n c+creationDegree n c=
      ∑ v∈realRootModes n c,∑ r∈Finset.range (2*(n : ℤ)-c).toNat,
        if (r+1)*oscillatorEnergy v≤n then
          Fintype.card (JointIndex (n-(r+1)*oscillatorEnergy v)
            (c-((r+1 : ℕ) : ℤ)*oscillatorCharge v)) else 0 := by
  classical
  calc
    _ = ∑ d : JointIndex n c,rootLetterCount (occupationWord d.val) := by
      rw [rowDegree,creationDegree,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      exact adjoint_loweringCount_add _
    _ = ∑ d : JointIndex n c,∑ v∈realRootModes n c,d.val v := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [occupation_rootLetterCount,jointIndex_root_count]
    _ = ∑ v∈realRootModes n c,∑ d : JointIndex n c,d.val v := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      exact jointIndex_sum_multiplicity n c v

end
end VOA.Wak.Charged
