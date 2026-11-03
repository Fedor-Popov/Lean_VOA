/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov, Leonardo Rastelli
-/
import VOA.AffineGeneral.Grading

/-!
# The actual weight-one space of the affine sl3 vacuum

Creation-word spanning identifies weight one with the image of sl3 under
x ↦ x(-1) vacuum. At nonzero level the opposite positive current reads off
the nondegenerate trace pairing, proving injectivity. This concerns the
universal vacuum quotient, before a simple quotient has been constructed.
-/
namespace VOA.AffineGeneral

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)
open VOA.AffineLie Module
noncomputable section
set_option maxHeartbeats 4000000

/-- A weight-one current state, linear in the actual trace-zero matrix. -/
def currentState (k : ℂ) : 𝔤 →ₗ[ℂ] Vacuum D k where
  toFun x := vacuumRho κ D.invariant k (ofLoop κ D.invariant x (-1)) (vacuumA D k)
  map_add' x y := by simp [← ofLoopₗ_apply,map_add,LinearMap.add_apply]
  map_smul' c x := by simp [← ofLoopₗ_apply,map_smul,LinearMap.smul_apply]

/-- A creation word has energy one exactly when it is one mode of depth zero. -/
theorem wordDeg_one_shape (L : List (𝔤 × ℕ)) (hL : wordDeg L=1) :
    ∃ x, L=[(x,0)] := by
  cases L with
  | nil => simp [wordDeg] at hL
  | cons a L =>
    rcases a with ⟨x,j⟩
    change j+1+wordDeg L=1 at hL
    have hj : j=0 := by omega
    have h0 : wordDeg L=0 := by omega
    have he := (wordDeg_eq_zero_iff L).mp h0
    subst j; subst L; exact ⟨x,rfl⟩

/-- Matrix current states lie in the actual energy-one eigenspace. -/
theorem currentState_mem_grading (k : ℂ) (x : 𝔤) :
    currentState D k x ∈ gradingZA D k 1 := by
  have h := negWord_mem_eigenspace κ D.invariant k [(x,0)]
  simpa [currentState,negWord,wordDeg,gradingZA,ell0OpA,vacuumA] using h

/-- Every energy-one vacuum vector is a single matrix current state;
only creation-word spanning, not ordered-word independence, is used. -/
theorem grading_one_eq_range (k : ℂ) : gradingZA D k 1=LinearMap.range (currentState D k) := by
  apply le_antisymm
  · rw [gradingZA,ell0OpA,eigenspace_eq_degSpan,degSpan,Submodule.span_le]
    rintro _ ⟨L,hL,rfl⟩
    have hw : wordDeg L=1 := by
      change -(wordDeg L : ℂ)= -((1 : ℤ) : ℂ) at hL
      have hcast := neg_injective hL
      exact_mod_cast hcast
    obtain ⟨x,rfl⟩ := wordDeg_one_shape L hw
    exact ⟨x,by simp [currentState,negWord,vacuumA]⟩
  · rintro _ ⟨x,rfl⟩
    exact currentState_mem_grading D k x

/-- A positive mode applied to a weight-one current reads the trace pairing
multiplied by the level. The zero-mode bracket kills the vacuum. -/
theorem positive_current_currentState (k : ℂ) (x y : 𝔤) :
    vacuumRho κ D.invariant k (ofLoop κ D.invariant y 1) (currentState D k x)=
      (k*κ y x) • vacuumA D k := by
  unfold currentState
  change vacuumRho κ D.invariant k (ofLoop κ D.invariant y 1)
    (vacuumRho κ D.invariant k (ofLoop κ D.invariant x (-1)) (vacuumA D k)) = _
  rw [vacuumRho_comm]
  have hv : vacuumRho κ D.invariant k (ofLoop κ D.invariant y 1) (vacuumA D k)=0 :=
    vacuum_pos_annihilate κ D.invariant k y 1 (by norm_num)
  rw [hv,map_zero,zero_add,affine_bracket κ D.invariant]
  norm_num only [Int.reduceAdd,ite_true,Int.cast_one,one_mul]
  rw [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,vacuum_acts_central]
  have hz : vacuumRho κ D.invariant k (ofLoop κ D.invariant ⁅y,x⁆ 0) (vacuumA D k)=0 :=
    vacuum_pos_annihilate κ D.invariant k _ 0 (by norm_num)
  rw [hz,zero_add,LinearMap.smul_apply,LinearMap.id_apply,smul_smul,mul_comm]

/-- At nonzero level no nonzero element of `𝔤` creates the zero state (the form argument).
For `𝔰𝔩₃` only, `AffineSl3.currentState_injective` (in `VOA.Examples.AffineSl3VacuumBasis`) proves
injectivity at every level from the PBW basis; no general-`𝔤` analogue without `k ≠ 0` is stated
in `AffineGeneral`. -/
theorem currentState_injective_of_ne_zero (k : ℂ) (hk : k≠0) :
    Function.Injective (currentState D k) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply LieData.form_right_nondegenerate D x
  intro y
  have h := positive_current_currentState D k x y
  rw [hx,map_zero] at h
  have hs : k*κ y x=0 := (smul_eq_zero.mp h.symm).resolve_right (vacuumA_ne_zero D k)
  exact (mul_eq_zero.mp hs).resolve_left hk
/-- The actual universal weight-one space is linearly equivalent to sl3 at
nonzero level, with surjectivity from spanning and injectivity from the form. -/
def weightOneEquiv (k : ℂ) (hk : k ≠ 0) : 𝔤 ≃ₗ[ℂ] gradingZA D k 1 := by
  rw [grading_one_eq_range]
  exact LinearEquiv.ofInjective (currentState D k) (currentState_injective_of_ne_zero D k hk)

/-- The eight Chevalley directions give a genuine basis of universal weight one. -/
def weightOneBasis (k : ℂ) (hk : k ≠ 0) : Module.Basis (ι) ℂ (gradingZA D k 1) :=
  D.basis.map (weightOneEquiv D k hk)

/- `weightOne_finrank` (dimension eight at EVERY level) is in `VOA.Examples.AffineSl3VacuumBasis`. -/
end
end VOA.AffineGeneral
