/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoJointEigenspaces
import Mathlib.Data.Finsupp.Multiset

/-!
# Highest-weight creation and adjoint words at actual joint labels

An occupation index supplies negative E,H modes and nonpositive F modes.
The horizontal F_0 corresponds to the gamma-zero occupation. Reversing the
word and applying the Chevalley involution gives only positive modes and E_0.
-/
namespace VOA.Wak.Charged
open MvPolynomial
open Module (End)
open AffineVOA.HighestNormalOrdering
open AffineVOA.NormalOrdering (currentWord)
open scoped BigOperators
noncomputable section

/-- Creation mode corresponding to an actual oscillator occupation. -/
def lowerLetter (v : Fin 3×ℕ) : Fin 3×ℤ :=
  (v.1,if v.1=1 then -(v.2 : ℤ) else -(v.2 : ℤ)-1)

/-- Every indexed creation letter is a genuine highest-weight lower mode. -/
theorem lowerLetter_isLower (v : Fin 3×ℕ) : IsLower (lowerLetter v).1 (lowerLetter v).2 := by
  simp only [lowerLetter,IsLower]
  split_ifs with h
  · by_cases hz : v.2=0
    · right; simp [hz,h]
    · left; omega
  · left; omega

/-- The mode's energy increment is exactly the oscillator energy. -/
theorem lowerLetter_energy (v : Fin 3×ℕ) :
    -(lowerLetter v).2=(oscillatorEnergy v : ℤ) := by
  simp [lowerLetter,oscillatorEnergy]
  split_ifs <;> ring

/-- The mode's charge increment is exactly the oscillator charge. -/
theorem lowerLetter_charge (v : Fin 3×ℕ) : colourCharge (lowerLetter v).1=oscillatorCharge v := rfl

/-- One fixed finite creation word for each occupation. No PBW independence
or quotient basis is assumed by this choice of order. -/
def occupationWord (d : Occupation) : List (Fin 3×ℤ) := d.toMultiset.toList.map lowerLetter

/-- All letters of the occupation word are genuine creation operators. -/
theorem occupationWord_lower (d : Occupation) :
    ∀ an∈occupationWord d,IsLower an.1 an.2 := by
  intro an han
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp han
  exact lowerLetter_isLower v

/-- A weighted sum over the literal occupation list is the exact Finsupp
weight. This does not depend on the chosen list ordering. -/
theorem occupation_list_weight {A : Type*} [AddCommMonoid A]
    (w : Fin 3×ℕ→A) (d : Occupation) :
    (d.toMultiset.toList.map w).sum=Finsupp.weight w d := by
  have h (e : Occupation) : (e.toMultiset.map w).sum=Finsupp.weight w e := by
    induction e using Finsupp.induction_linear with
    | zero => simp
    | add e f he hf => rw [Finsupp.toMultiset_add,Multiset.map_add,Multiset.sum_add,map_add,he,hf]
    | single v n => simp [Finsupp.toMultiset_single,Finsupp.weight_single,
        Multiset.map_nsmul,Multiset.sum_nsmul]
  simpa only [← Multiset.sum_coe,← Multiset.map_coe,Multiset.coe_toList] using h d

/-- Energy increment of a literal current word. -/
def wordEnergy (w : List (Fin 3×ℤ)) : ℤ := (w.map (fun an => -an.2)).sum

/-- Ghost-charge increment of a literal current word. -/
def wordCharge (w : List (Fin 3×ℤ)) : ℤ := (w.map (fun an => colourCharge an.1)).sum

/-- Actual word action on the highest polynomial has its computed energy. -/
theorem currentWord_energy (k lam : ℂ) (w : List (Fin 3×ℤ)) :
    Dwt (currentWord (J k lam) w (1 : WakFock))=
      (wordEnergy w : ℂ) • currentWord (J k lam) w (1 : WakFock) := by
  induction w with
  | nil => simp [currentWord,wordEnergy,Dwt,Eul_one']
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ WakFock => T (currentWord (J k lam) w 1))
        (degree_J k lam an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply] at hc
      simp only [currentWord,Module.End.mul_apply,wordEnergy,List.map_cons,List.sum_cons,
        Int.cast_add,Int.cast_neg,add_smul]
      rw [sub_eq_iff_eq_add] at hc
      exact hc

/-- Actual word action on the highest polynomial has its computed charge. -/
theorem currentWord_charge (k lam : ℂ) (w : List (Fin 3×ℤ)) :
    Dch (currentWord (J k lam) w (1 : WakFock))=
      (wordCharge w : ℂ) • currentWord (J k lam) w (1 : WakFock) := by
  induction w with
  | nil => simp [currentWord,wordCharge,Dch,Eul_one']
  | cons an w ih =>
      have hc := congrArg (fun T : End ℂ WakFock => T (currentWord (J k lam) w 1))
        (charge_J k lam an.1 an.2)
      dsimp only at hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih,map_smul,LinearMap.smul_apply] at hc
      simp only [currentWord,Module.End.mul_apply,wordCharge,List.map_cons,List.sum_cons,
        Int.cast_add,add_smul]
      rw [sub_eq_iff_eq_add] at hc
      exact hc

/-- The creation word retains the exact natural energy of its occupation. -/
theorem occupationWord_energy (d : Occupation) : wordEnergy (occupationWord d)=(occupationEnergy d : ℤ) := by
  rw [wordEnergy,occupationWord,List.map_map]
  simp only [Function.comp_def,lowerLetter_energy]
  rw [occupation_list_weight]
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he => rw [map_add,map_add,Nat.cast_add,hd,he]
  | single v n => simp [occupationEnergy,Finsupp.weight_single,nsmul_eq_mul]

/-- The creation word retains the exact signed charge of its occupation. -/
theorem occupationWord_charge (d : Occupation) : wordCharge (occupationWord d)=occupationCharge d := by
  rw [wordCharge,occupationWord,List.map_map]
  simp only [Function.comp_def,lowerLetter_charge]
  exact occupation_list_weight oscillatorCharge d

/-- Actual creation columns lie in the proved finite joint Fock space. -/
theorem occupationWord_mem_joint (k lam : ℂ) (n : ℕ) (c : ℤ) (d : JointIndex n c) :
    currentWord (J k lam) (occupationWord d.val) (1 : WakFock)∈jointFockSpace n c := by
  apply mem_jointFockSpace_of_eigen
  · rw [currentWord_energy,occupationWord_energy,d.property.1,Int.cast_natCast]
  · rw [currentWord_charge,occupationWord_charge,d.property.2]

/-- The Chevalley adjoint exchanges raising and lowering colours and fixes
Cartan, while reversing the mode index. -/
def adjointLetter (an : Fin 3×ℤ) : Fin 3×ℤ :=
  (if an.1=0 then 1 else if an.1=1 then 0 else 2,-an.2)

/-- The literal adjoint word acts in the reverse order. -/
def adjointWord (w : List (Fin 3×ℤ)) : List (Fin 3×ℤ) := w.reverse.map adjointLetter

/-- Every adjoint of an indexed creation letter is positive or E_0. -/
theorem adjoint_lowerLetter_positive (v : Fin 3×ℕ) :
    0<(adjointLetter (lowerLetter v)).2 ∨ adjointLetter (lowerLetter v)=(0,0) := by
  rcases v with ⟨a,j⟩
  rcases fin3_cases a with rfl|rfl|rfl <;>
    norm_num [adjointLetter,lowerLetter,Fin.ext_iff] <;> omega

/-- Every mode in the adjoint word kills the ACTUAL screening singular
state at its screening parameters. -/
theorem adjoint_occupation_letter_kills (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (d : Occupation)
    (an : Fin 3×ℤ) (han : an∈adjointWord (occupationWord d)) :
    J k ((q : ℂ)*(k+2)-(r : ℂ)-1) an.1 an.2 (Screening.state r q M)=0 := by
  obtain ⟨bn,hbn,rfl⟩ := List.mem_map.mp han
  have hb : bn∈occupationWord d := List.mem_reverse.mp hbn
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hb
  rcases adjoint_lowerLetter_positive v with hn|he
  · exact Screening.state_positive_current r q M hr hq k hMk _ _ hn
  · rw [he,J_E]
    exact Screening.state_raising r q M 0 (by omega)

/-- Every nonempty word of annihilating operators kills the vector. -/
theorem currentWord_kills_of_letters {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : Fin 3→ℤ→End ℂ E) (v : E) (w : List (Fin 3×ℤ)) (hw : w≠[])
    (h : ∀ an∈w,A an.1 an.2 v=0) : currentWord A w v=0 := by
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons an w ih =>
      cases w with
      | nil => simpa [currentWord] using h an (by simp)
      | cons bn w =>
          rw [currentWord,Module.End.mul_apply,ih (by simp) (fun cn hc => h cn (by simp [hc])),map_zero]

/-- At positive joint energy every indexed adjoint word kills the actual
nonzero screening state. This gives the kernel equations for finite rows. -/
theorem adjoint_occupation_kills_screening (r q M : ℕ) (hr : 0<r) (hq : 0<q)
    (k : ℂ) (hMk : (M : ℂ)*(k+2)=1) (d : JointIndex (r*q) (r : ℤ)) :
    currentWord (J k ((q : ℂ)*(k+2)-(r : ℂ)-1))
      (adjointWord (occupationWord d.val)) (Screening.state r q M)=0 := by
  apply currentWord_kills_of_letters
  · intro he
    have hw : occupationWord d.val=[] := by simpa [adjointWord] using he
    have hd := occupationWord_energy d.val
    rw [hw,wordEnergy,List.map_nil,List.sum_nil,d.property.1] at hd
    have hp : 0<r*q := Nat.mul_pos hr hq
    exact (ne_of_gt (show (0 : ℤ)<(r*q : ℕ) by exact_mod_cast hp)) hd.symm
  · exact adjoint_occupation_letter_kills r q M hr hq k hMk d.val

end
end VOA.Wak.Charged
