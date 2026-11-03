/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl3VacuumGrading

/-!
# The actual weight-one space of the affine sl3 vacuum

Creation-word spanning identifies weight one with the image of sl3 under
x ↦ x(-1) vacuum. At nonzero level the opposite positive current reads off
the nondegenerate trace pairing, proving injectivity. This concerns the
universal vacuum quotient, before a simple quotient has been constructed.
-/
namespace VOA.AffineSl3
open VOA.AffineLie Module
noncomputable section
set_option maxHeartbeats 4000000

/-- A weight-one current state, linear in the actual trace-zero matrix. -/
def currentState (k : ℂ) : Sl3 →ₗ[ℂ] Vacuum k where
  toFun x := vacuumRho form form_invariant k (current x (-1)) (vacuumA k)
  map_add' x y := by simp [current,← ofLoopₗ_apply,map_add,LinearMap.add_apply]
  map_smul' c x := by simp [current,← ofLoopₗ_apply,map_smul,LinearMap.smul_apply]

/-- A creation word has energy one exactly when it is one mode of depth zero. -/
theorem wordDeg_one_shape (L : List (Sl3 × ℕ)) (hL : wordDeg L=1) :
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
theorem currentState_mem_grading (k : ℂ) (x : Sl3) :
    currentState k x ∈ gradingZA k 1 := by
  have h := negWord_mem_eigenspace form form_invariant k [(x,0)]
  simpa [currentState,current,negWord,wordDeg,gradingZA,ell0OpA,vacuumA] using h

/-- Every energy-one vacuum vector is a single matrix current state;
only creation-word spanning, not ordered-word independence, is used. -/
theorem grading_one_eq_range (k : ℂ) : gradingZA k 1=LinearMap.range (currentState k) := by
  apply le_antisymm
  · rw [gradingZA,ell0OpA,eigenspace_eq_degSpan,degSpan,Submodule.span_le]
    rintro _ ⟨L,hL,rfl⟩
    have hw : wordDeg L=1 := by
      change -(wordDeg L : ℂ)= -((1 : ℤ) : ℂ) at hL
      have hcast := neg_injective hL
      exact_mod_cast hcast
    obtain ⟨x,rfl⟩ := wordDeg_one_shape L hw
    exact ⟨x,by simp [currentState,current,negWord,vacuumA]⟩
  · rintro _ ⟨x,rfl⟩
    exact currentState_mem_grading k x

/-- A positive mode applied to a weight-one current reads the trace pairing
multiplied by the level. The zero-mode bracket kills the vacuum. -/
theorem positive_current_currentState (k : ℂ) (x y : Sl3) :
    vacuumRho form form_invariant k (current y 1) (currentState k x)=
      (k*form y x) • vacuumA k := by
  unfold currentState
  change vacuumRho form form_invariant k (current y 1)
    (vacuumRho form form_invariant k (current x (-1)) (vacuumA k)) = _
  rw [vacuumRho_comm]
  have hv : vacuumRho form form_invariant k (current y 1) (vacuumA k)=0 :=
    vacuum_pos_annihilate form form_invariant k y 1 (by norm_num)
  rw [hv,map_zero,zero_add,current_bracket]
  norm_num only [Int.reduceAdd,ite_true,Int.cast_one,one_mul]
  rw [map_add,LinearMap.add_apply,map_smul,LinearMap.smul_apply,vacuum_acts_central]
  have hz : vacuumRho form form_invariant k (current ⁅y,x⁆ 0) (vacuumA k)=0 :=
    vacuum_pos_annihilate form form_invariant k _ 0 (by norm_num)
  rw [hz,zero_add,LinearMap.smul_apply,LinearMap.id_apply,smul_smul,mul_comm]

/-- At nonzero level no nonzero trace-zero matrix creates the zero state (the form argument).
The level hypothesis is not needed: `currentState_injective` (in
`VOA.Examples.AffineSl3VacuumBasis`) proves injectivity at every level from the PBW basis; this
variant is kept because `weightOneEquiv` is defined here, below that file in the import order. -/
theorem currentState_injective_of_ne_zero (k : ℂ) (hk : k≠0) :
    Function.Injective (currentState k) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply form_right_nondegenerate x
  intro y
  have h := positive_current_currentState k x y
  rw [hx,map_zero] at h
  have hs : k*form y x=0 := (smul_eq_zero.mp h.symm).resolve_right (vacuumA_ne_zero k)
  exact (mul_eq_zero.mp hs).resolve_left hk
/-- The actual universal weight-one space is linearly equivalent to sl3 at
nonzero level, with surjectivity from spanning and injectivity from the form. -/
def weightOneEquiv (k : ℂ) (hk : k ≠ 0) : Sl3 ≃ₗ[ℂ] gradingZA k 1 := by
  rw [grading_one_eq_range]
  exact LinearEquiv.ofInjective (currentState k) (currentState_injective_of_ne_zero k hk)

/-- The eight Chevalley directions give a genuine basis of universal weight one. -/
def weightOneBasis (k : ℂ) (hk : k ≠ 0) : Module.Basis (Fin 8) ℂ (gradingZA k 1) :=
  chevalleyBasis.map (weightOneEquiv k hk)

/- `weightOne_finrank` (dimension eight at EVERY level) is in `VOA.Examples.AffineSl3VacuumBasis`. -/
end
end VOA.AffineSl3
