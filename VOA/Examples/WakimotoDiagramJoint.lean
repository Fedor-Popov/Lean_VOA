/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.WakimotoDiagramAction

/-!
# Actual joint spaces under affine diagram symmetry

Swapping beta and gamma occupations sends (energy,charge) to
(energy-charge,-charge). The transformed creation columns lie in precisely
that finite actual Fock space, with an explicit bijection of its indices.
-/
namespace VOA.Wak.Charged
open Module (End)
open MvPolynomial
open AffineVOA.NormalOrdering (currentWord)
noncomputable section

/-- Exchange beta and gamma oscillator labels, fixing the boson and depth. -/
def diagramVariable (v : Fin 3×ℕ) : Fin 3×ℕ :=
  ((Equiv.swap (0 : Fin 3) 1) v.1,v.2)

/-- The oscillator exchange is an involution. -/
theorem diagramVariable_involutive : Function.Involutive diagramVariable := by
  intro v
  simp [diagramVariable]

/-- Exchange beta and gamma multiplicities in a finite occupation. -/
def diagramOccupation (d : Occupation) : Occupation := Finsupp.mapDomain diagramVariable d

/-- The finite occupation exchange is itself an involution. -/
theorem diagramOccupation_involutive : Function.Involutive diagramOccupation := by
  intro d
  unfold diagramOccupation
  rw [← Finsupp.mapDomain_comp]
  have he : diagramVariable ∘ diagramVariable=id := funext diagramVariable_involutive
  rw [he,Finsupp.mapDomain_id]

/-- Exact charge change of the exchanged occupation. -/
theorem diagramOccupation_charge (d : Occupation) :
    occupationCharge (diagramOccupation d)= -occupationCharge d := by
  induction d using Finsupp.induction_linear with
  | zero => simp [diagramOccupation]
  | add d e hd he =>
      simp only [diagramOccupation,Finsupp.mapDomain_add,map_add] at hd he ⊢
      rw [hd,he]; ring
  | single v n =>
      rw [diagramOccupation,Finsupp.mapDomain_single]
      rcases v with ⟨a,j⟩
      rcases fin3_cases a with rfl|rfl|rfl <;>
        norm_num [occupationCharge,Finsupp.weight_single,diagramVariable,
          oscillatorCharge,Equiv.swap_apply_def,Fin.ext_iff,nsmul_eq_mul]

/-- Exact energy change of the exchanged occupation, expressed in integers
so that no truncated subtraction hides the charge correction. -/
theorem diagramOccupation_energy (d : Occupation) :
    (occupationEnergy (diagramOccupation d) : ℤ)=
      (occupationEnergy d : ℤ)-occupationCharge d := by
  induction d using Finsupp.induction_linear with
  | zero => simp [diagramOccupation]
  | add d e hd he =>
      simp only [diagramOccupation,Finsupp.mapDomain_add,map_add,Nat.cast_add] at hd he ⊢
      rw [hd,he]; ring
  | single v n =>
      rw [diagramOccupation,Finsupp.mapDomain_single]
      rcases v with ⟨a,j⟩
      rcases fin3_cases a with rfl|rfl|rfl <;>
        norm_num [occupationEnergy,occupationCharge,Finsupp.weight_single,diagramVariable,
          oscillatorCharge,oscillatorEnergy,Equiv.swap_apply_def,Fin.ext_iff,nsmul_eq_mul] <;> ring

/-- A genuine bijection of the two actual finite joint occupation sets.
The integer label equality prevents any natural-subtraction convention. -/
def diagramJointEquiv (n n' : ℕ) (c : ℤ) (hn : (n' : ℤ)=(n : ℤ)-c) :
    JointIndex n c ≃ JointIndex n' (-c) where
  toFun d := ⟨diagramOccupation d.val,by
    constructor
    · have h := diagramOccupation_energy d.val
      rw [d.property.1,d.property.2,← hn] at h
      exact_mod_cast h
    · rw [diagramOccupation_charge,d.property.2]⟩
  invFun d := ⟨diagramOccupation d.val,by
    constructor
    · have h := diagramOccupation_energy d.val
      rw [d.property.1,d.property.2,hn] at h
      exact_mod_cast (show (occupationEnergy (diagramOccupation d.val) : ℤ)=(n : ℤ) by omega)
    · rw [diagramOccupation_charge,d.property.2,neg_neg]⟩
  left_inv d := Subtype.ext (diagramOccupation_involutive d.val)
  right_inv d := Subtype.ext (diagramOccupation_involutive d.val)

/-- Under the transformed currents, actual energy increments are minus
mode index minus the transformed root charge. -/
theorem energy_diagramJ (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅Dwt,diagramJ k lam a n⁆=
      ((-n-colourCharge a : ℤ) : ℂ) • diagramJ k lam a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [diagramJ_E,← J_F,degree_J,J_F]
    norm_num [colourCharge,Fin.ext_iff]
    congr 1
    ring
  · rw [diagramJ_F,← J_E k lam,degree_J,J_E]
    norm_num [colourCharge,Fin.ext_iff]
    congr 1
    ring
  · rw [diagramJ_H,lie_add,lie_neg,← J_H,degree_J,J_H]
    have hs : ⁅Dwt,k • (1 : End ℂ WakFock)⁆=0 := by rw [lie_smul,lie_one',smul_zero]
    by_cases hz : n=0
    · subst n; simp [hs,colourCharge,Fin.ext_iff]
    · simp only [if_neg hz,lie_zero,add_zero]
      norm_num [colourCharge,Fin.ext_iff]

/-- The actual ghost charge increment of a transformed current is opposite
to its transformed root colour. -/
theorem charge_diagramJ (k lam : ℂ) (a : Fin 3) (n : ℤ) :
    ⁅Dch,diagramJ k lam a n⁆=
      ((-colourCharge a : ℤ) : ℂ) • diagramJ k lam a n := by
  rcases fin3_cases a with rfl|rfl|rfl
  · rw [diagramJ_E,← J_F,charge_J,J_F]
    norm_num [colourCharge,Fin.ext_iff]
  · rw [diagramJ_F,← J_E k lam,charge_J,J_E]
    norm_num [colourCharge,Fin.ext_iff]
  · rw [diagramJ_H,lie_add,lie_neg,← J_H,charge_J,J_H]
    have hs : ⁅Dch,k • (1 : End ℂ WakFock)⁆=0 := by rw [lie_smul,lie_one',smul_zero]
    split_ifs <;> simp [hs,colourCharge,Fin.ext_iff]

/-- The literal transformed word has exact actual energy and charge,
proved from the current commutators without a basis assumption. -/
theorem diagramWord_grades (k lam : ℂ) (w : List (Fin 3×ℤ)) :
    Dwt (currentWord (diagramJ k lam) w (1 : WakFock))=
      ((wordEnergy w-wordCharge w : ℤ) : ℂ) • currentWord (diagramJ k lam) w 1 ∧
    Dch (currentWord (diagramJ k lam) w (1 : WakFock))=
      ((-wordCharge w : ℤ) : ℂ) • currentWord (diagramJ k lam) w 1 := by
  induction w with
  | nil => simp [currentWord,wordEnergy,wordCharge,Dwt,Dch,Eul_one']
  | cons an w ih =>
      have he := congrArg (fun T : End ℂ WakFock => T (currentWord (diagramJ k lam) w 1))
        (energy_diagramJ k lam an.1 an.2)
      have hc := congrArg (fun T : End ℂ WakFock => T (currentWord (diagramJ k lam) w 1))
        (charge_diagramJ k lam an.1 an.2)
      dsimp only at he hc
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih.1,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at he
      rw [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply,Module.End.mul_apply,
        ih.2,map_smul,LinearMap.smul_apply,sub_eq_iff_eq_add] at hc
      simp only [currentWord,Module.End.mul_apply,wordEnergy,wordCharge,List.map_cons,List.sum_cons]
      dsimp only [wordEnergy,wordCharge] at he hc
      constructor
      · rw [he]; push_cast; module
      · rw [hc]; push_cast; module

/-- Transformed creation columns lie in the opposite-charge, shifted-energy
actual Fock space identified by the occupation bijection. -/
theorem diagramOccupationWord_mem_joint (k lam : ℂ) (n n' : ℕ) (c : ℤ)
    (hn : (n' : ℤ)=(n : ℤ)-c) (d : JointIndex n c) :
    currentWord (diagramJ k lam) (occupationWord d.val) (1 : WakFock)∈jointFockSpace n' (-c) := by
  apply mem_jointFockSpace_of_eigen
  · rw [(diagramWord_grades k lam _).1,occupationWord_energy,occupationWord_charge,
      d.property.1,d.property.2,← hn,Int.cast_natCast]
  · rw [(diagramWord_grades k lam _).2,occupationWord_charge,d.property.2]

end
end VOA.Wak.Charged
