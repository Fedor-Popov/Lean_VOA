/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaBasis
import VOA.Examples.VirasoroSingularSpecialization

/-!
# Actual Verma Ward kernels and specialization

The L₁/L₂ equations are written in the proved PBW coordinates. Their kernel
is exactly the space of singular vectors at the selected word level. A
generic rational relation for a polynomial presentation of these equations
can be specialized without evaluating any pole. Constructing that generic
relation and identifying its polynomial equation family are separate inputs;
no minimal-model singular vector is asserted by this interface alone.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule LeeYangWardClosure

/-- Assemble the actual level-n Verma state from its partition coefficients. -/
noncomputable def vermaLevelState (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ) : Verma c h :=
  ∑ w, v w • negWord c h w.val

/-- A nonzero coefficient vector gives a nonzero state because the general
Verma partition words are independent, including their L₋₁ descendants. -/
theorem vermaLevelState_eq_zero_iff (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ) :
    vermaLevelState c h n v=0 ↔ v=0 := by
  constructor
  · intro he
    have hh := verma_negWord_coef_zero_indexed (fun w : VermaPartitions n => w.val)
      Subtype.val_injective (fun w => w.property.1) c h Finset.univ v he
    funext w
    exact hh w (Finset.mem_univ _)
  · intro he
    simp [vermaLevelState,he]

/-- The assembled state belongs to the actual level span, term by term. -/
theorem vermaLevelState_mem (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ) :
    vermaLevelState c h n v ∈ sortedSpan c h n := by
  apply Submodule.sum_mem
  intro w hw
  exact Submodule.smul_mem _ _ (negWord_mem_sortedSpan_of_sorted c h w.property.1 w.property.2)

/-- Every creation word is an L₀ eigenvector of weight h plus its total
creation energy. This is the relative grading of the general Verma module. -/
theorem vermaMode_zero_negWord (c h : ℂ) (w : List ℕ) :
    vermaMode c h 0 (negWord c h w)=(h+(energyHW w:ℂ)) • negWord c h w := by
  induction w with
  | nil => simpa [vermaMode] using verma_zero_acts c h
  | cons i w ih =>
    simp only [negWord_cons]
    rw [vermaMode_comm_apply,ih]
    simp only [show -(i:ℤ)-1≠0 by omega,if_false,add_zero,zero_add,
      map_smul,Int.cast_zero,Int.cast_sub,Int.cast_neg,Int.cast_natCast,
      Int.cast_one,energyHW_cons,Nat.cast_add,Nat.cast_one]
    module

/-- Every state assembled at level n has actual L₀ weight h+n. -/
theorem vermaLevelState_zero_mode (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ) :
    vermaMode c h 0 (vermaLevelState c h n v)=(h+(n:ℂ)) • vermaLevelState c h n v := by
  simp only [vermaLevelState,map_sum,map_smul,vermaMode_zero_negWord,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [w.property.2,smul_comm]

/-- Killing the two positive generators L₁ and L₂ kills every positive
mode. This applies to any Verma state and does not assume a form or grading. -/
theorem verma_positive_zero_of_one_two (c h : ℂ) (v : Verma c h)
    (h1 : vermaMode c h 1 v=0) (h2 : vermaMode c h 2 v=0) :
    ∀ n : ℤ, 0<n → vermaMode c h n v=0 := by
  have hall : ∀ k : ℕ, vermaMode c h ((k:ℤ)+2) v=0 := by
    intro k
    induction k with
    | zero => simpa using h2
    | succ k ih =>
      have hh := vermaMode_comm_apply c h 1 ((k:ℤ)+2) v
      simp only [h1,ih,map_zero,show ¬ (1:ℤ)+((k:ℤ)+2)=0 by omega,
        if_false,zero_add,add_zero] at hh
      have hn : (1:ℂ)-((k:ℤ)+2)≠0 := by
        intro he
        have he' : (1:ℤ)-((k:ℤ)+2)=0 := by exact_mod_cast he
        omega
      push_cast at hh hn
      have he := (smul_eq_zero.mp hh.symm).resolve_left hn
      convert he using 1 <;> push_cast <;> ring
  intro n hn
  by_cases he : n=1
  · simpa [he] using h1
  · obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0≤n-2 by omega)
    have he : n=(k:ℤ)+2 := by omega
    simpa [he] using hall k

/-- Each equation records a PBW coefficient of either the L₁ or L₂ image.
All PBW output words are allowed, so no unstated degree-closure lemma is used. -/
abbrev VermaWardRows := Fin 2 × {w : List ℕ // SortedWord w}

/-- The actual matrix of the two positive-mode equations at level n. Its
entries are coordinates in the proved general Verma basis. -/
noncomputable def vermaWardMatrix (c h : ℂ) (n : ℕ) :
    Matrix VermaWardRows (VermaPartitions n) ℂ := fun row col =>
  (vermaSortedBasis c h).repr
    (vermaMode c h (if row.1=0 then 1 else 2) (negWord c h col.val)) row.2

/-- Multiplying the Ward matrix by coefficients gives exactly the PBW
coordinates of the actual mode applied to the assembled state. -/
theorem vermaWardMatrix_mulVec (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ)
    (row : VermaWardRows) :
    (vermaWardMatrix c h n).mulVec v row =
      (vermaSortedBasis c h).repr
        (vermaMode c h (if row.1=0 then 1 else 2) (vermaLevelState c h n v)) row.2 := by
  classical
  simp [vermaWardMatrix,Matrix.mulVec,dotProduct,vermaLevelState,
    mul_comm]

/-- Vanishing of the Ward matrix is equivalent to the actual L₁/L₂ state
equations. Faithfulness of PBW coordinates is proved by the basis theorem. -/
theorem vermaWardMatrix_kernel_iff (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ) :
    (vermaWardMatrix c h n).mulVec v=0 ↔
      vermaMode c h 1 (vermaLevelState c h n v)=0 ∧
      vermaMode c h 2 (vermaLevelState c h n v)=0 := by
  constructor
  · intro he
    constructor
    · apply (vermaSortedBasis c h).repr.injective
      ext w
      have hh := congrFun he (0,w)
      simpa [vermaWardMatrix_mulVec] using hh
    · apply (vermaSortedBasis c h).repr.injective
      ext w
      have hh := congrFun he (1,w)
      simpa [vermaWardMatrix_mulVec] using hh
  · rintro ⟨h1,h2⟩
    funext row
    rw [vermaWardMatrix_mulVec]
    split_ifs <;> simp [h1,h2]

/-- Every nonzero actual Ward-kernel vector is a nonzero highest-weight
state of weight h+n in M(c,h). This gives all positive-mode equations and
its zero-mode equation, not merely a pair of necessary conditions. -/
theorem vermaWardMatrix_highest (c h : ℂ) (n : ℕ) (v : VermaPartitions n → ℂ)
    (hv : v≠0) (hAv : (vermaWardMatrix c h n).mulVec v=0) :
    vermaLevelState c h n v≠0 ∧
      IsHighestWeightVector (vermaRep c h) (vermaLevelState c h n v) c (h+n) := by
  have hh := (vermaWardMatrix_kernel_iff c h n v).mp hAv
  refine ⟨fun he => hv ((vermaLevelState_eq_zero_iff c h n v).mp he),?_⟩
  exact ⟨rfl,verma_positive_zero_of_one_two c h _ hh.1 hh.2,
    vermaLevelState_zero_mode c h n v⟩

/-- A generic rational kernel relation for a polynomial Ward presentation
specializes to a genuine nonzero highest-weight state. Poles in the chosen
coefficient formula are removed internally. The polynomial presentation and
its generic kernel relation must still be established by representation theory. -/
theorem verma_highest_of_generic_ward (c h : ℂ) (n : ℕ)
    (A : Matrix VermaWardRows (VermaPartitions n) (Polynomial ℂ))
    (v : VermaPartitions n → RatFunc ℂ) (hv : v≠0)
    (hAv : (A.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).mulVec v=0)
    (a : ℂ) (hA : A.map (Polynomial.evalRingHom a)=vermaWardMatrix c h n) :
    ∃ w : Verma c h, w≠0 ∧ w∈sortedSpan c h n ∧
      IsHighestWeightVector (vermaRep c h) w c (h+n) := by
  obtain ⟨u,hu,hAu⟩ := VirasoroSpecialization.exists_specialized_kernel_of_rational A v hv hAv a
  rw [hA] at hAu
  have hh := vermaWardMatrix_highest c h n u hu hAu
  exact ⟨vermaLevelState c h n u,hh.1,vermaLevelState_mem c h n u,hh.2⟩

end VOA.InverseDS.VirasoroVerma
