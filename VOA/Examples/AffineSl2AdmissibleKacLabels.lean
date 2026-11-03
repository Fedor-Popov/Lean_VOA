/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2KacSpecialization
import VOA.Examples.AffineSl2AdmissibleRootArithmetic

/-!
# The ordinary Kac labels at the first admissible vacuum level

Coprimality isolates the horizontal root and one further weight-zero root.
At highest weight minus two the only possible root at that energy would
require a positive-charge, zero-energy descendant, which does not exist.
All multiplicities here count the actual finite occupation indices.
-/
namespace VOA.Wak.Charged
open AffineSl2AdmissibleArithmetic
noncomputable section
local instance admissibleFintype (n : ℕ) (c : ℤ) : Fintype (JointIndex n c) := jointIndexFintype n c

/-- A zero-energy occupation cannot have positive ghost charge: its
principal weight would be negative. -/
theorem jointIndex_zero_positive_empty (c : ℤ) (hc : 0<c) : IsEmpty (JointIndex 0 c) := by
  refine ⟨fun d => ?_⟩
  have he := occupationPrincipal_eq d.val
  rw [d.property.1,d.property.2] at he
  omega

/-- The zero energy and zero charge block consists only of the empty
occupation, so its descendant multiplicity is exactly one. -/
theorem jointIndex_zero_zero_card : Fintype.card (JointIndex 0 0)=1 := by
  let z : JointIndex 0 0 := ⟨0,by simp⟩
  have hz : ∀d : JointIndex 0 0,d=z := by
    intro d
    apply Subtype.ext
    ext v
    have hh := jointIndex_multiplicity_le 0 0 d v
    simpa using Nat.eq_zero_of_le_zero (by simpa using hh)
  exact Fintype.card_eq_one_iff.mpr ⟨z,hz⟩

/-- Every root label in the actual finite determinant has a genuine root
colour and fits the block's energy budget. -/
theorem affineKacLabels_bounds (n : ℕ) (c : ℤ) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels n c) :
    i.1.1≠2 ∧ (i.2+1)*oscillatorEnergy i.1≤n := by
  exact ⟨(Finset.mem_filter.mp (Finset.mem_product.mp (Finset.mem_filter.mp hi).1).1).2,
    (Finset.mem_filter.mp hi).2⟩

/-- Clearing the nonzero denominator converts a positive-family zero
at highest weight zero into the natural real-root resonance equation. -/
theorem positive_weight_zero_equation (p q m r : ℕ) (hq : 0<q)
    (he : (m : ℂ)*((p : ℂ)/q)-(r : ℂ)-1=0) : m*p=q*(r+1) := by
  have hqC : (q : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hh : (m : ℂ)*p=q*(r+1) := by
    field_simp at he
    linear_combination he
  exact_mod_cast hh

/-- Clearing the same denominator in the negative family gives the
second real-root resonance equation, with its horizontal exception intact. -/
theorem negative_weight_zero_equation (p q m r : ℕ) (hq : 0<q)
    (he : (r : ℂ)-1-(m : ℂ)*((p : ℂ)/q)=0) : m*p+q=q*r := by
  have hqC : (q : ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hh : (m : ℂ)*p+q=q*r := by
    field_simp at he
    linear_combination -he
  exact_mod_cast hh

/-- At the first admissible energy, the actual weight-zero Kac labels
are only the horizontal translation root and the first affine real root. -/
theorem admissible_zero_labels (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels (q*(p-1)) ((p : ℤ)-1))
    (hz : realRootWeight ((p : ℂ)/q) i=0) :
    i=((1,0),0) ∨ i=((0,q-1),p-2) := by
  obtain ⟨hc,he⟩ := affineKacLabels_bounds _ _ i hi
  rcases i with ⟨⟨a,m⟩,r⟩
  fin_cases a
  · have hz' : ((m+1 : ℕ) : ℂ)*((p : ℂ)/q)-((r+1 : ℕ) : ℂ)-1=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination hz
    have eqn := positive_weight_zero_equation p q (m+1) (r+1) hq hz'
    have hb : (m+1)*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
    obtain ⟨hm,hr⟩ := first_minus_resonance_unique hp hq (by omega) hcop eqn hb
    right
    have hm' : m=q-1 := by omega
    have hr' : r=p-2 := by omega
    simp [hm',hr']
  · by_cases hm : m=0
    · subst m
      have hr : r=0 := by
        have hz' : (r : ℂ)=0 := by simpa [realRootWeight,realRootSlope,realRootOffset] using hz
        exact_mod_cast hz'
      left; simp [hr]
    · have hz' : ((r+1 : ℕ) : ℂ)-1-(m : ℂ)*((p : ℂ)/q)=0 := by
        simpa [realRootWeight,realRootSlope,realRootOffset,Nat.cast_add,sub_eq_add_neg,
          neg_mul,add_comm,add_left_comm,add_assoc] using hz
      have eqn := negative_weight_zero_equation p q m (r+1) hq hz'
      have hs := plus_resonance_energy_gt hp hq (by omega) hcop eqn
      have hb : m*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
      omega
  · exact False.elim (hc rfl)

/-- At highest weight minus two, any Kac zero whose energy fits the first
vacuum level has the opposite-charge root label at exactly that level. -/
theorem admissible_minus_two_labels (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels (q*(p-1)) (p : ℤ))
    (hz : realRootWeight ((p : ℂ)/q) i = -2) :
    i=((1,q),p-2) := by
  obtain ⟨hc,he⟩ := affineKacLabels_bounds _ _ i hi
  rcases i with ⟨⟨a,m⟩,r⟩
  fin_cases a
  · have hz' : ((r+1 : ℕ) : ℂ)-1-((m+1 : ℕ) : ℂ)*((p : ℂ)/q)=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination -hz
    have eqn := negative_weight_zero_equation p q (m+1) (r+1) hq hz'
    have hs := plus_resonance_energy_gt hp hq (by omega) hcop eqn
    have hb : (m+1)*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
    omega
  · have hz' : (m : ℂ)*((p : ℂ)/q)-((r+1 : ℕ) : ℂ)-1=0 := by
      norm_num [realRootWeight,realRootSlope,realRootOffset,Fin.ext_iff] at hz
      push_cast
      linear_combination -hz
    have eqn := positive_weight_zero_equation p q m (r+1) hq hz'
    have hm : 0<m := by
      by_contra hn
      have hm0 : m=0 := by omega
      simp only [hm0,zero_mul] at eqn
      have : 0<q*(r+1+1) := Nat.mul_pos hq (by omega)
      omega
    have hb : m*(r+1)≤q*(p-1) := by simpa [oscillatorEnergy,Nat.mul_comm] using he
    obtain ⟨hm',hr⟩ := first_minus_resonance_unique hp hq hm hcop eqn hb
    have hr' : r=p-2 := by omega
    simp [hm',hr']
  · exact False.elim (hc rfl)

/-- The only prospective denominator zero has no descendants in its
required joint block. Its actual Kac multiplicity is therefore zero. -/
theorem admissible_minus_two_multiplicity_zero (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) (i : (Fin 3×ℕ)×ℕ)
    (hi : i∈affineKacLabels (q*(p-1)) (p : ℤ))
    (hz : realRootWeight ((p : ℂ)/q) i = -2) :
    affineKacMultiplicity (q*(p-1)) (p : ℤ) i=0 := by
  rw [admissible_minus_two_labels p q hp hq hcop i hi hz]
  have hr : p-2+1=p-1 := by omega
  simp only [affineKacMultiplicity,oscillatorEnergy,oscillatorCharge,
    Fin.isValue,Fin.reduceEq,if_pos,if_false,hr]
  rw [Nat.mul_comm (p-1) q,Nat.sub_self]
  have hc : 0<(p : ℤ)-((p-1 : ℕ) : ℤ)*(-1) := by
    have hcast : ((p-1 : ℕ) : ℤ)=(p : ℤ)-1 := by omega
    rw [hcast]; omega
  letI := jointIndex_zero_positive_empty _ hc
  exact Fintype.card_eq_zero

/-- The actual finite Kac product at highest weight minus two is nonzero
in the first vacuum block. No character or generic nondegeneracy premise is used. -/
theorem affineKacProduct_admissible_minus_two (p q : ℕ) (hp : 2≤p) (hq : 0<q)
    (hcop : p.Coprime q) :
    (affineKacProduct ((p : ℂ)/q) (q*(p-1)) (p : ℤ)).eval (-2)≠0 := by
  classical
  simp only [affineKacProduct,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  by_cases hz : realRootWeight ((p : ℂ)/q) i = -2
  · rw [admissible_minus_two_multiplicity_zero p q hp hq hcop i hi hz,pow_zero]
    exact one_ne_zero
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hz))

end
end VOA.Wak.Charged
